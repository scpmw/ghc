
module Dwarf (
  dwarfGen
  ) where

import BlockId         ( blockLbl )
import CLabel
import Config          ( cProjectName, cProjectVersion )
import CoreSyn         ( Tickish(..) )
import Debug
import DynFlags
import FastString
import Module
import Outputable
import Platform
import Unique
import UniqSupply

import Dwarf.Constants
import Dwarf.Types

import Data.Maybe
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

  return (infoSct $$ abbrevSct $$ lineSct, us')

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
