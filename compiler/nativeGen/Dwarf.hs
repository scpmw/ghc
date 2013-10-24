
module Dwarf (
  dwarfGen
  ) where

import BlockId         ( blockLbl )
import CLabel
import CmmExpr         ( GlobalReg(..) )
import Config          ( cProjectName, cProjectVersion )
import CoreSyn         ( Tickish(..) )
import Debug
import DynFlags
import FastString
import Module
import Outputable
import Platform
import Reg
import Unique
import UniqSupply

import CodeGen.Platform

import Dwarf.Constants
import Dwarf.Types

import Data.Maybe
import Data.List        ( sortBy )
import Data.Ord         ( comparing )
import Data.Word        ( Word8 )
import qualified Data.Map as Map
import System.FilePath
import System.Directory ( getCurrentDirectory )

-- | Generate DWARF/debug information
dwarfGen :: DynFlags -> ModLocation -> UniqSupply -> [DebugBlock]
            -> IO (SDoc, UniqSupply)
dwarfGen df modLoc us blocks = do

  -- Convert debug data structures to DWARF info records
  let procs = concatMap debugSplitProcs blocks
      procToDwarf prc
        = DwarfSubprogram { dwChildren = blocksToDwarf $ dblBlocks prc
                          , dwName     = case dblSourceTick prc of
                               Just s@SourceNote{} -> sourceName s
                               _otherwise          -> showSDocDump df $ ppr $ dblLabel prc
                          , dwLabel    = dblCLabel prc
                          }
      blocksToDwarf = foldr blockToDwarf []
      blockToDwarf blk dws
        | isJust (dblPosition blk)  = dw : dws
        | otherwise                 = nested ++ dws -- block was optimized out, flatten
        where nested = blocksToDwarf $ dblBlocks blk
              dw = DwarfBlock { dwChildren = nested
                              , dwLabel    = blockLbl (dblLabel blk)
                              , dwMarker   = mkAsmTempLabel (dblLabel blk)
                              }
  compPath <- getCurrentDirectory
  let dwarfUnit = DwarfCompileUnit
        { dwChildren = map procToDwarf procs
        , dwName = fromMaybe "" (ml_hs_file modLoc)
        , dwCompDir = addTrailingPathSeparator compPath
        , dwProducer = cProjectName ++ " " ++ cProjectVersion
        , dwLineLabel = dwarfLineLabel
        }

  -- .debug_abbrev section: Declare the format we're using
  let abbrevSct = pprAbbrevDecls

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
                 debugFrames framesU procs

  return (infoSct $$ abbrevSct $$ lineSct $$ frameSct, us'')

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
        spReg       = dwarfGlobalRegNo plat Sp
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

-- | Splits out all nested procedures. Produces a list of procedures
-- where all nested blocks are either normal blocks or proc-points.
debugSplitProcs :: DebugBlock -> [DebugBlock]
debugSplitProcs b = fst $ split Nothing b
  where split m_prc blk
          | procLbl == dblLabel blk  = (blk' : concat prcss, Nothing)
          | m_prc == Just procLbl    = (concat prcss, Just blk')
          | otherwise                = pprPanic "debugSplitProcs: Context corrupt!" (ppr m_prc) -- see cmmDebugGen
          where procLbl = dblProcedure blk
                (prcss, nested) = unzip $ map (split (Just procLbl)) $ dblBlocks blk
                blk' = blk { dblBlocks = catMaybes nested }

debugFrames :: Unique -> [DebugBlock] -> SDoc
debugFrames u = vcat . map (debugFrame u)

-- | Writes a "Frame Description Entry" for a procedure. This consists
-- mainly of referencing the CIE and writing state machine
-- instructions to describe how the frame base (CFA) changes.
debugFrame :: Unique -> DebugBlock -> SDoc
debugFrame u prc@DebugBlock{ dblCLabel=procLbl, dblHasInfoTbl=hasInfo }
  = sdocWithPlatform $ \plat ->
    let fdeLabel    = mkAsmTempDerivedLabel procLbl (fsLit "_fde")
        fdeEndLabel = mkAsmTempDerivedLabel procLbl (fsLit "_fde_end")
        length      = ppr fdeEndLabel <> char '-' <> ppr fdeLabel
        procEnd     = mkAsmTempEndLabel procLbl

        -- | Recurses through all blocks, producing a list of labels
        -- with their respective unwind table, sorted by the position
        -- they appear in the assembly.
        unwindTable
          parentUws
          DebugBlock{ dblPosition=pos, dblLabel=blockLbl, dblHasInfoTbl=hasInfo,
                      dblUnwind=unwinds, dblBlocks=blocks }
          | Just p <- pos  = (p, (addr, unwinds')):nested
          | otherwise      = nested -- block was optimized out
          where addr     = ppr (mkAsmTempLabel blockLbl) <>
                           if hasInfo then ptext (sLit "-1") else empty -- see [Note: Info Offset]
                unwinds' = unwinds `Map.union` parentUws
                nested   = concatMap (unwindTable unwinds') blocks
        initialUw = Map.singleton Sp (UwReg Sp 0)
        sortedTable = map snd $ sortBy (comparing fst) $
                      unwindTable initialUw prc

        -- | Takes the list of unwind tables and generates a minimal frame program
        -- (= only generates instructions where unwind info actually changes)
        unwindCode oldUws ((lbl, uws) : xs)
          | uws /= oldUws
          = pprByte dW_CFA_set_loc $$ pprWord lbl $$ -- update code address
            let isChanged g v
                  | old == Just v  = Nothing
                  | otherwise      = Just (old, v)
                  where old = Map.lookup g oldUws
                changed = Map.toList $ Map.mapMaybeWithKey isChanged uws
                died    = Map.toList $ Map.difference oldUws uws
            in vcat (map (uncurry $ pprSetUnwind plat) changed) $$
               vcat (map (pprUndefUnwind plat . fst) died) $$
               unwindCode uws xs
          | otherwise
          = unwindCode oldUws xs
        unwindCode _      []
          = empty

        info_offs = if hasInfo then char '1' else char '0' -- see [Note: Info Offset]

    in vcat [ pprData4' length
            , ppr fdeLabel <> colon
            , pprData4' (ppr (mkAsmTempLabel u))               -- Reference to CIE
            , pprWord (ppr procLbl <> char '-' <> info_offs)   -- Code pointer
            , pprWord (ppr procEnd <> char '-' <> ppr procLbl
                                   <> char '+' <> info_offs)   -- Block byte length
            , unwindCode initialUw sortedTable
            , ptext (sLit "\t.align ") <> ppr (platformWordSize plat)
            , ppr fdeEndLabel <> colon
            ]

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

dwarfGlobalRegNo :: Platform -> GlobalReg -> Word8
dwarfGlobalRegNo plat = maybe 0 (dwarfRegNo plat . RegReal) . globalRegMaybe plat

-- | Generate code for setting the unwind information for a register,
-- optimized using its known old value in the table. Note that "Sp" is
-- special: We see it as synonym for the CFA.
pprSetUnwind :: Platform -> GlobalReg -> (Maybe UnwindExpr, UnwindExpr) -> SDoc
pprSetUnwind _    Sp (Just (UwReg s _), UwReg s' o') | s == s'
  = if o' >= 0
    then pprByte dW_CFA_def_cfa_offset $$ pprLEBWord (fromIntegral o')
    else pprByte dW_CFA_def_cfa_offset_sf $$ pprLEBInt o'
pprSetUnwind plat Sp (_, UwReg s' o')
  = if o' >= 0
    then pprByte dW_CFA_def_cfa $$
         pprLEBWord (fromIntegral $ dwarfGlobalRegNo plat s') $$
         pprLEBWord (fromIntegral o')
    else pprByte dW_CFA_def_cfa_sf $$
         pprLEBWord (fromIntegral $ dwarfGlobalRegNo plat s') $$
         pprLEBInt o'
pprSetUnwind _    Sp (_, uw)
  = pprByte dW_CFA_def_cfa_expression $$ pprUnwindExpr False uw
pprSetUnwind plat g  (_, UwDeref (UwReg Sp o))
  | o < 0 && ((-o) `mod` platformWordSize plat) == 0 -- expected case
  = pprByte (dW_CFA_offset + dwarfGlobalRegNo plat g) $$
    pprLEBWord (fromIntegral ((-o) `div` platformWordSize plat))
  | otherwise
  = pprByte dW_CFA_offset_extended_sf $$
    pprLEBWord (fromIntegral (dwarfGlobalRegNo plat g)) $$
    pprLEBInt o
pprSetUnwind plat g  (_, UwDeref uw)
  = pprByte dW_CFA_expression $$
    pprLEBWord (fromIntegral (dwarfGlobalRegNo plat g)) $$
    pprUnwindExpr True uw
pprSetUnwind plat g  (_, uw)
  = pprByte dW_CFA_val_expression $$
    pprLEBWord (fromIntegral (dwarfGlobalRegNo plat g)) $$
    pprUnwindExpr True uw

-- | Generates a DWARF expression for the given unwind expression. If
-- @spIsCFA@ is true, we see @Sp@ as the frame base CFA where it gets
-- mentioned.
pprUnwindExpr :: Bool -> UnwindExpr -> SDoc
pprUnwindExpr spIsCFA expr
  = sdocWithPlatform $ \plat ->
    let ppr (UwConst i)
          | i >= 0 && i < 32 = pprByte (dW_OP_lit0 + fromIntegral i)
          | otherwise        = pprByte dW_OP_consts $$ pprLEBInt i -- the lazy way
        ppr (UwReg Sp i) | spIsCFA
                             = if i == 0
                               then pprByte dW_OP_call_frame_cfa
                               else ppr (UwPlus (UwReg Sp 0) (UwConst i))
        ppr (UwReg g i)      = pprByte (dW_OP_breg0 + fromIntegral (dwarfGlobalRegNo plat g)) $$
                               pprLEBInt i
        ppr (UwDeref u)      = ppr u $$ pprByte dW_OP_deref
        ppr (UwPlus u1 u2)   = ppr u1 $$ ppr u2 $$ pprByte dW_OP_plus
        ppr (UwMinus u1 u2)  = ppr u1 $$ ppr u2 $$ pprByte dW_OP_minus
        ppr (UwTimes u1 u2)  = ppr u1 $$ ppr u2 $$ pprByte dW_OP_mul
    in ptext (sLit "\t.byte 1f-.-1") $$
       ppr expr $$
       ptext (sLit "1:")

-- | Generate code for re-setting the unwind information for a
-- register to "undefined"
pprUndefUnwind :: Platform -> GlobalReg -> SDoc
pprUndefUnwind _    Sp = panic "pprUndefUnwind Sp" -- should never happen
pprUndefUnwind plat g  = pprByte dW_CFA_undefined $$
                         pprLEBWord (fromIntegral $ dwarfGlobalRegNo plat g)
