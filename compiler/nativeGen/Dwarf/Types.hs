
module Dwarf.Types
  ( DwarfInfo(..)
  , pprDwarfInfo
  , pprAbbrevDecls
  , pprByte
  , pprWord
  , pprDwWord
  , pprLEBWord
  , pprLEBInt
  )
  where

import CLabel
import FastString
import Outputable
import Platform

import Dwarf.Constants

import Data.Bits
import Data.Word
import Data.Char

-- | Individual dwarf records
data DwarfInfo
  = DwarfCompileUnit { dwChildren :: [DwarfInfo]
                     , dwName :: String
                     , dwProducer :: String
                     , dwCompDir :: String
                     , dwLineLabel :: LitString }
  | DwarfSubprogram { dwChildren :: [DwarfInfo]
                    , dwName :: String
                    , dwLabel :: CLabel }
  | DwarfBlock { dwChildren :: [DwarfInfo]
               , dwLabel :: CLabel
               , dwMarker :: CLabel }

-- | Abbreviation codes used in dwarf file
data DwarfAbbrev
  = DwAbbrNull          -- ^ Pseudo, used for marking the end of lists
  | DwAbbrCompileUnit
  | DwAbbrSubprogram
  | DwAbbrBlock
  deriving (Eq, Enum)

-- | Gives code to use in binary represenation.
abbrevToCode :: DwarfAbbrev -> Word
abbrevToCode = fromIntegral . fromEnum

-- | Abbreviation declaration. This explains the binary encoding we
-- use for representing @DwarfInfo@.
pprAbbrevDecls :: Bool -> SDoc
pprAbbrevDecls haveDebugLine =
  let mkAbbrev abbr tag chld flds =
        let fld (tag, form) = pprLEBWord tag $$ pprLEBWord form
        in pprLEBWord (abbrevToCode abbr) $$ pprLEBWord tag $$ pprByte chld $$
           vcat (map fld flds) $$ pprByte 0 $$ pprByte 0
  in dwarfAbbrevSection $$
     ptext dwarfAbbrevLabel <> colon $$
     mkAbbrev DwAbbrCompileUnit dW_TAG_compile_unit dW_CHILDREN_yes
       ([ (dW_AT_name, dW_FORM_string)
       , (dW_AT_producer, dW_FORM_string)
       , (dW_AT_language, dW_FORM_data4)
       , (dW_AT_comp_dir, dW_FORM_string)
       ] ++
       (if haveDebugLine
        then [ (dW_AT_stmt_list, dW_FORM_data4) ]
        else [])) $$
     mkAbbrev DwAbbrSubprogram dW_TAG_subprogram dW_CHILDREN_yes
       [ (dW_AT_name, dW_FORM_string)
       , (dW_AT_MIPS_linkage_name, dW_FORM_string)
       , (dW_AT_external, dW_FORM_flag)
       , (dW_AT_low_pc, dW_FORM_addr)
       , (dW_AT_high_pc, dW_FORM_addr)
       ] $$
     mkAbbrev DwAbbrBlock dW_TAG_lexical_block dW_CHILDREN_yes
       [ (dW_AT_name, dW_FORM_string)
       , (dW_AT_low_pc, dW_FORM_addr)
       , (dW_AT_high_pc, dW_FORM_addr)
       ]

pprAbbrev :: DwarfAbbrev -> SDoc
pprAbbrev = pprLEBWord . abbrevToCode

pprString' :: SDoc -> SDoc
pprString' str = ptext (sLit "\t.asciz \"") <> str <> char '"'

pprString :: String -> SDoc
pprString = pprString' . hcat . map escape
  where escape '\\' = ptext (sLit "\\\\")
        escape '\"' = ptext (sLit "\\\"")
        escape '\n' = ptext (sLit "\\n")
        escape c    | isAscii c && isPrint c && c /= '?' -- silence trigraph warnings
                    = char c
                    | otherwise
                    = let ch = ord c
                      in char '\\' <>
                         char (intToDigit (ch `div` 64)) <>
                         char (intToDigit ((ch `div` 8) `mod` 8)) <>
                         char (intToDigit (ch `mod` 8))

pprData4' :: SDoc -> SDoc
pprData4' x = ptext (sLit "\t.long ") <> x

pprData4 :: Word -> SDoc
pprData4 = pprData4' . ppr

pprDwWord :: SDoc -> SDoc
pprDwWord = pprData4'

-- | Machine-dependent word directive
pprWord :: SDoc -> SDoc
pprWord s = (<> s) . sdocWithPlatform $ \plat ->
  case platformWordSize plat of
    4 -> ptext (sLit "\t.long ")
    8 -> ptext (sLit "\t.quad ")
    n -> panic $ "pprWord: Unsupported target platform word length " ++ show n ++ "!"

pprFlag :: Bool -> SDoc
pprFlag True  = ptext (sLit "\t.byte 0xff")
pprFlag False = ptext (sLit "\t.byte 0")

pprDwarfInfo :: Bool -> DwarfInfo -> SDoc
pprDwarfInfo haveSrc d
  = pprDwarfInfoOpen haveSrc d $$
    vcat (map (pprDwarfInfo haveSrc) (dwChildren d)) $$
    pprDwarfInfoClose

-- | Prints assembler data corresponding to DWARF info records. Note
-- that the binary format of this is paramterized in @abbrevDecls@ and
-- has to be kept in synch.
pprDwarfInfoOpen :: Bool -> DwarfInfo -> SDoc
pprDwarfInfoOpen haveSrc (DwarfCompileUnit _ name producer compDir lineLbl) =
  pprAbbrev DwAbbrCompileUnit
  $$ pprString name
  $$ pprString producer
  $$ pprData4 dW_LANG_Haskell
  $$ pprString compDir
  $$ if haveSrc
     then pprData4' (ptext lineLbl <> char '-' <> ptext dwarfLineLabel)
     else empty
pprDwarfInfoOpen _ (DwarfSubprogram _ name label) = sdocWithDynFlags $ \df ->
  pprAbbrev DwAbbrSubprogram
  $$ pprString name
  $$ pprString (renderWithStyle df (ppr label) (mkCodeStyle CStyle))
  $$ pprFlag (externallyVisibleCLabel label)
  $$ pprWord (ppr label)
  $$ pprWord (ppr $ mkAsmTempEndLabel label)
pprDwarfInfoOpen _ (DwarfBlock _ label marker) = sdocWithDynFlags $ \df ->
  pprAbbrev DwAbbrBlock
  $$ pprString (renderWithStyle df (ppr label) (mkCodeStyle CStyle))
  $$ pprWord (ppr marker)
  $$ pprWord (ppr $ mkAsmTempEndLabel marker)

pprDwarfInfoClose :: SDoc
pprDwarfInfoClose = pprAbbrev DwAbbrNull
