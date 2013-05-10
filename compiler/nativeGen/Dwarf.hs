
module Dwarf (
  dwarfGen,
  cmmDwarfFiles, DwarfFiles
  ) where

import BlockId         ( blockLbl )
import CLabel
import Config          ( cProjectName, cProjectVersion )
import Debug
import DynFlags
import FastString
import Module
import Outputable
import Platform
import UniqFM
import Unique
import UniqSupply

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

  -- Convert debug data structures to DWARF
  let toDwarf DebugBlock { dblProcedure=pr, dblLabel=lbl, dblCLabel=clbl, dblBlocks=childs }
        | pr
        = DwarfSubprogram { dwChildren = dwarfChilds
                          , dwName = showSDocDump df (ppr lbl)
                          , dwLabel = clbl
                          }
        | otherwise
        =  DwarfBlock { dwChildren = dwarfChilds
                      , dwLabel = blockLbl lbl
                      , dwMarker = mkAsmTempLabel lbl
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

  -- .debug_ghc section: debug data in eventlog format (GHC-specific, obviously)
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


-- | Generates the .file directives needed for all new files in the
-- second file map
cmmDwarfFiles :: DwarfFiles -> DwarfFiles -> SDoc
cmmDwarfFiles fileIds fileIds'
  = vcat $ map declFile $ eltsUFM (fileIds' `minusUFM` fileIds)
  where declFile (f,n) = ptext (sLit "\t.file ") <> ppr n <+> doubleQuotes (ftext f)
