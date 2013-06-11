
module Dwarf (
  dwarfGen,
  cmmDwarfFiles, DwarfFiles
  ) where

import BlockId         ( blockLbl )
import CLabel
import CmmExpr         ( GlobalReg(..) )
import Config          ( cProjectName, cProjectVersion )
import Debug
import DynFlags
import FastString
import Module
import Outputable
import Platform
import Reg
import UniqFM
import Unique
import UniqSupply

import CodeGen.Platform

import Dwarf.Constants
import Dwarf.Types

import Data.Maybe
import System.FilePath
import System.Directory ( getCurrentDirectory )

-- | Generate DWARF/debug information for an individual CmmDecl. Takes
-- ticks from the raw CmmDecl and generates the appropriate structures
-- into .debug_info and .debug_ghc.
dwarfGen :: DynFlags -> ModLocation -> UniqSupply -> [DebugBlock]
            -> IO (SDoc, UniqSupply)
dwarfGen df modLoc us blocks = do

  -- Convert debug data structures to DWARF info records
  let toDwarf DebugBlock { dblProcedure=pr, dblLabel=lbl, dblCLabel=clbl, dblSourceTick=src,
                           dblBlocks=childs }
        | pr
        = DwarfSubprogram { dwChildren = dwarfChilds
                          , dwName     = case src of
                               Just s@SourceNote{} -> sourceName s
                               _otherwise          -> showSDocDump df (ppr lbl)
                          , dwLabel    = clbl
                          }
        | otherwise
        =  DwarfBlock { dwChildren = dwarfChilds
                      , dwLabel    = blockLbl lbl
                      , dwMarker   = mkAsmTempLabel lbl
                      }
        where dwarfChilds = map toDwarf $ filter (not . dblOptimizedOut) childs
  compPath <- getCurrentDirectory
  let dwarfUnit = DwarfCompileUnit
        { dwChildren = map toDwarf blocks
        , dwName = fromMaybe "" (ml_hs_file modLoc)
        , dwCompDir = addTrailingPathSeparator compPath
        , dwProducer = cProjectName ++ " " ++ cProjectVersion
        , dwLineLabel = dwarfLineLabel
        }

  -- .debug_abbrev section: Declare the format we're using
  let abbrevSct = abbrevDecls

  -- .debug_info section: Information records on procedures and blocks
  let (unitU, us') = takeUniqFromSupply us
      infoSct = vcat [ dwarfInfoSection
                     , compileUnitHeader unitU
                     , pprDwarfInfo dwarfUnit
                     , compileUnitFooter unitU
                     ]

  -- .debug_line section: Generated mainly by the assembler, but we need to label it
  let lineSct = dwarfLineSection $$
                ptext dwarfLineLabel <> colon

  -- .debug_frame section: Information about the layout of the GHC stack
  let (framesU, us'') = takeUniqFromSupply us'
      frameSct = dwarfFrameSection $$
                 debugFrameHeader framesU $$
                 debugFrames framesU blocks

  -- .debug_ghc section: debug data in eventlog format (GHC-specific, obviously)
  let dbgMod = DebugModule { dmodPackage = thisPackage df
                           , dmodLocation = modLoc
                           , dmodBlocks = blocks
                           }
  evData <- debugWriteEventlog df dbgMod
  let ghcSct = dwarfGhcSection $$
               pprBuffer evData

  return (infoSct $$ abbrevSct $$ lineSct $$ frameSct $$ ghcSct, us'')

-- | Header for a compilation unit, establishing global format
-- parameters
compileUnitHeader :: Unique -> SDoc
compileUnitHeader unitU = sdocWithPlatform $ \plat ->
  let cuLabel = mkAsmTempLabel unitU
      length = ppr (mkAsmTempEndLabel cuLabel) <> char '-' <> ppr cuLabel
  in vcat [ -- CU size and DWARF variant (32-bit vs 64-bit)
            case platformWordSize plat of
              4 -> ptext (sLit "\t.long ") <> length
              8 -> ptext (sLit "\t.long 0xffffffff\n\t.quad ") <> length
              _other -> panic "compileUnitHeader: Unsupported word size!"
          , ppr cuLabel <> colon             -- start calculating CU size from here
          , ptext (sLit "\t.word 3")         -- DWARF version
          , pprWord (ptext dwarfAbbrevLabel) -- pointer to our abbrevs
          , ptext (sLit "\t.byte ") <> ppr (platformWordSize plat) -- word size
          ]

-- | Compilation unit footer, mainly establishing size of debug sections
compileUnitFooter :: Unique -> SDoc
compileUnitFooter unitU =
  let cuEndLabel = mkAsmTempEndLabel $ mkAsmTempLabel unitU
  in ppr cuEndLabel <> colon


-- | Generates the .file directives needed for all new files in the
-- second file map
cmmDwarfFiles :: DwarfFiles -> DwarfFiles -> SDoc
cmmDwarfFiles fileIds fileIds'
  = vcat $ map declFile $ eltsUFM (fileIds' `minusUFM` fileIds)
  where declFile (f,n) = ptext (sLit "\t.file ") <> ppr n <+> doubleQuotes (ftext f)

-- | Header for the .debug_frame section. Here we emit the "Common
-- Information Entry" record that etablishes general call frame
-- parameters and the default stack layout.
debugFrameHeader :: Unique -> SDoc
debugFrameHeader u
  = sdocWithPlatform $ \plat ->
    let cieLabel    = mkAsmTempLabel u
        cieStartLabel= mkAsmTempDerivedLabel cieLabel (fsLit "_start")
        cieEndLabel = mkAsmTempEndLabel cieLabel
        length      = ppr cieEndLabel <> char '-' <> ppr cieStartLabel
        toRegNo     = maybe 0 (dwarfRegNo plat . RegReal) . globalRegMaybe plat
        spReg       = toRegNo Sp
        retReg      = dwarfReturnRegNo plat
        wordSize    = platformWordSize plat
    in vcat [ ppr cieLabel <> colon          -- Label to refer to this CIE
            , pprData4' length
            , ppr cieStartLabel <> colon     -- calculate length from here
            , pprData4' (ptext (sLit "-1"))  -- Common Information Entry marker (-1 is lazy for 0xf..f)
            , pprByte 3                      -- CIE version (we require DWARF 3)
            , pprByte 0                      -- Augmentation (none)
            , pprByte 1                      -- Code offset multiplicator
            , pprByte (128-fromIntegral wordSize) -- Data offset multiplicator
                                             -- (stacks grow downward, hence "-w" in signed LEB128)
            , pprByte retReg                 -- virtual register holding return address

              -- CFA = Sp
              -- (CFA should be what the Sp was on function entry. We
              -- will update the offset in @blockFrame@ where neccessary)
            , pprByte dW_CFA_def_cfa
            , pprByte spReg
            , pprByte 0

              -- RET = *CFA
            , pprByte (dW_CFA_offset+retReg)
            , pprByte 0

              -- Sp' = CFA
              -- (we need to set this manually as our Sp register is
              -- often not the architecture's default stack register)
            , pprByte dW_CFA_val_offset
            , pprLEBWord (fromIntegral spReg)
            , pprLEBWord 0

            , ptext (sLit "\t.align ") <> ppr wordSize -- note that 0 = dW_CFA_nop
            , ppr cieEndLabel <> colon
            ]

debugFrames :: Unique -> [DebugBlock] -> SDoc
debugFrames u = vcat . map (debugFrame u)

-- | Writes a "Frame Description Entry" for a procedure. This consists
-- mainly of referencing the CIE and writing state machine
-- instructions to describe how the frame base (CFA) changes.
debugFrame :: Unique -> DebugBlock -> SDoc
debugFrame u DebugBlock{ dblCLabel=procLbl, dblBlocks=blocks, dblHasInfoTbl=hasInfo }
  = sdocWithPlatform $ \plat ->
    let fdeLabel    = mkAsmTempDerivedLabel procLbl (fsLit "_fde")
        fdeEndLabel = mkAsmTempDerivedLabel procLbl (fsLit "_fde_end")
        length      = ppr fdeEndLabel <> char '-' <> ppr fdeLabel
        procEnd     = mkAsmTempEndLabel procLbl

        wordSize = platformWordSize plat
        (_, instrs) = foldl (blockFrame wordSize) (0, empty) blocks
        info_offs = if hasInfo then char '1' else char '0' -- see [Note: Info Offset]

    in vcat [ pprData4' length
            , ppr fdeLabel <> colon
            , pprData4' (ppr (mkAsmTempLabel u))               -- Reference to CIE
            , pprWord (ppr procLbl <> char '-' <> info_offs)   -- Code pointer
            , pprWord (ppr procEnd <> char '-' <> ppr procLbl
                                   <> char '+' <> info_offs)   -- Block byte length
            , instrs
            , ptext (sLit "\t.align ") <> ppr wordSize
            , ppr fdeEndLabel <> colon
            ]

-- | Write debug block
blockFrame :: Int -> (Int, SDoc) -> DebugBlock -> (Int, SDoc)
blockFrame wordSize (oldOff, doc)
           DebugBlock{ dblOptimizedOut=isMissing, dblLabel=blockLbl, dblHasInfoTbl=hasInfo,
                       dblStackOff=m_stackOff, dblBlocks=blocks }
  = let off | isMissing             = oldOff
            | Just s <- m_stackOff  = s - wordSize          -- remove return ptr
            | otherwise             = 0
        info_offs = if hasInfo then ptext (sLit "-1") else empty  -- see [Note: Info Offset]
        instrs   = vcat [ pprByte dW_CFA_set_loc            -- set code address
                        , pprWord $ ppr (mkAsmTempLabel blockLbl) <> info_offs
                        , pprByte dW_CFA_def_cfa_offset     -- set new stack offset
                        , pprLEBWord $ fromIntegral off     -- new offset
                        ]
        doc'     | off == oldOff || isMissing  = doc
                 | otherwise                   = doc $$ instrs
    in foldl (blockFrame wordSize) (off, doc') blocks


-- [Note: Info Offset]
--
-- GDB was pretty much written with C-like programs in mind, and as a
-- result they assume that once you have a return address, it is a
-- good idea to look at (PC-1) to unwind further - as that's where the
-- "call" instruction is supposed to be.
--
-- Now on one hand, code generated by GHC looks nothing like what GDB
-- expects, and in fact going up from a return pointer is guaranteed
-- to land us inside an info table! On the other hand, that actually
-- gives us some wiggle room, as we expect IP to never *actually* end
-- up inside the info table, so we can "cheat" by putting whatever GDB
-- expects to see there. This is probably pretty safe, as GDB cannot
-- assume (PC-1) to be a valid code pointer in the first place - and I
-- have seen no code trying to correct this.
--
-- Note that this will not prevent GDB from failing to look-up the
-- correct function name for the frame, as that uses the symbol table,
-- which we can not manipulate as easily.
