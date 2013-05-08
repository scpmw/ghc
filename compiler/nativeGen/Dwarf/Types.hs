
module Dwarf.Types
  ( DwarfInfo(..)
  , pprDwarfInfo
  , pprDwarfInfoOpen
  , pprDwarfInfoClose
  , abbrevDecls
  , DwarfFiles
  , pprWord
  , pprBuffer
  )
  where

import CLabel
import FastString
import Outputable
import Platform
import UniqFM ( UniqFM )

import Dwarf.Constants

import Data.Bits
import Data.Word
import Data.Char

import Binary
import Foreign
import System.IO.Unsafe as Unsafe

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
  = DwAbbrNull          -- | Pseudo, used for marking the end of lists
  | DwAbbrCompileUnit
  | DwAbbrSubprogram
  | DwAbbrBlock
  deriving (Eq, Enum)

-- | Map of files to IDs (used for .loc / .file directives)
type DwarfFiles = UniqFM (FastString, Int)

-- | Gives code to use in binary represenation.
abbrevToCode :: DwarfAbbrev -> Word
abbrevToCode = fromIntegral . fromEnum

pprByte :: Word8 -> SDoc
pprByte x = ptext (sLit "\t.byte ") <> ppr (fromIntegral x :: Word)

-- | Prints a number in "little endian base 128" format. The idea is
-- to optimize for small numbers by stopping once all further bytes
-- would be 0. The highest bit in every byte signals whether there
-- are further bytes to read.
pprLEBWord :: Word -> SDoc
pprLEBWord x = go x
 where go x | x < 128   = pprByte (fromIntegral x)
            | otherwise = pprByte (fromIntegral $ 128 .|. (x .&. 127)) $$
                          go (x `shiftR` 7)

-- | Abbreviation declaration. This explains the binary encoding we
-- use for representing @DwarfInfo@.
abbrevDecls :: SDoc
abbrevDecls =
  let mkAbbrev abbr tag chld flds =
        let fld (tag, form) = pprLEBWord tag $$ pprLEBWord form
        in pprLEBWord (abbrevToCode abbr) $$ pprLEBWord tag $$ pprByte chld $$
           vcat (map fld flds) $$ pprByte 0 $$ pprByte 0
  in dwarfAbbrevSection $$
     ptext dwarfAbbrevLabel <> colon $$
     mkAbbrev DwAbbrCompileUnit dW_TAG_compile_unit dW_CHILDREN_yes
       [ (dW_AT_name, dW_FORM_string)
       , (dW_AT_producer, dW_FORM_string)
       , (dW_AT_language, dW_FORM_data4)
       , (dW_AT_comp_dir, dW_FORM_string)
       , (dW_AT_stmt_list, dW_FORM_data4)
       ] $$
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
pprString = pprString' . text

pprData4' :: SDoc -> SDoc
pprData4' x = ptext (sLit "\t.long ") <> x

pprData4 :: Word -> SDoc
pprData4 = pprData4' . ppr

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

pprDwarfInfo :: DwarfInfo -> SDoc
pprDwarfInfo d = pprDwarfInfoOpen d $$
                 vcat (map pprDwarfInfo (dwChildren d)) $$
                 pprDwarfInfoClose

-- | Prints assembler data corresponding to DWARF info records. Note
-- that the binary format of this is paramterized in @abbrevDecls@ and
-- has to be kept in synch.
pprDwarfInfoOpen :: DwarfInfo -> SDoc
pprDwarfInfoOpen (DwarfCompileUnit _ name producer compDir lineLbl) =
  pprAbbrev DwAbbrCompileUnit
  $$ pprString name
  $$ pprString producer
  $$ pprData4 dW_LANG_Haskell
  $$ pprString compDir
  $$ pprData4' (ptext lineLbl)
pprDwarfInfoOpen (DwarfSubprogram _ name label) = sdocWithDynFlags $ \df ->
  pprAbbrev DwAbbrSubprogram
  $$ pprString name
  $$ pprString (renderWithStyle df (ppr label) (mkCodeStyle CStyle))
  $$ pprFlag (externallyVisibleCLabel label)
  $$ pprWord (ppr label)
  $$ pprWord (ppr $ mkAsmTempEndLabel label)
pprDwarfInfoOpen (DwarfBlock _ label marker) = sdocWithDynFlags $ \df ->
  pprAbbrev DwAbbrBlock
  $$ pprString (renderWithStyle df (ppr label) (mkCodeStyle CStyle))
  $$ pprWord (ppr marker)
  $$ pprWord (ppr $ mkAsmTempEndLabel marker)

pprDwarfInfoClose :: SDoc
pprDwarfInfoClose = pprAbbrev DwAbbrNull

-- | Generate code for emitting the given buffer. Will take care to
-- escape it appropriatly.
pprBuffer :: (Int, ForeignPtr Word8) -> SDoc
pprBuffer (len, buf) = Unsafe.unsafePerformIO $ do

  -- As we output a string, we need to do escaping. We approximate
  -- here that the escaped string will have double the size of the
  -- original buffer. That should be plenty of space given the fact
  -- that we expect to be converting a lot of text.
  bh <- openBinMem (len * 2)
  let go p q | p == q    = return ()
             | otherwise = peek p >>= escape . fromIntegral >> go (p `plusPtr` 1) q
      escape c
        | c == ord '\\'  = putB '\\' >> putB '\\'
        | c == ord '\"'  = putB '\\' >> putB '"'
        | c == ord '\n'  = putB '\\' >> putB 'n'
        | isAscii (chr c) && isPrint (chr c)
                         = putByte bh (fromIntegral c)
        | otherwise      = do putB '\\'
                              putB $ intToDigit (c `div` 64)
                              putB $ intToDigit ((c `div` 8) `mod` 8)
                              putB $ intToDigit (c `mod` 8)
      putB :: Char -> IO ()
      putB = putByte bh . fromIntegral . ord
      {-# INLINE putB #-}
  withForeignPtr buf $ \p ->
    go p (p `plusPtr` len)

  -- Pack result into a string
  (elen, ebuf) <- getBinMemBuf bh
  buf <- withForeignPtr ebuf $ \p -> mkFastStringForeignPtr p ebuf elen

  return $ ptext (sLit "\t.ascii ") <> doubleQuotes (ftext buf)
