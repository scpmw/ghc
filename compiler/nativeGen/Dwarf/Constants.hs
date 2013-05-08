
module Dwarf.Constants where

import FastString
import Outputable

import Data.Word

-- | Language ID used for Haskell.
dW_LANG_Haskell :: Word
dW_LANG_Haskell = dW_LANG_lo_user + 0x7368 -- 'hs'
dW_LANG_lo_user :: Word
dW_LANG_lo_user = 0x8000
-- Note: Using user language codes seems to sometimes confuse back-ends.
--       I had it cause crashes when dumping LLVM metadata, for instance.
--       It is unclear what the right behaviour here is.

-- | Dwarf tags
dW_TAG_compile_unit, dW_TAG_subroutine_type,
  dW_TAG_file_type, dW_TAG_subprogram, dW_TAG_lexical_block,
  dW_TAG_base_type, dW_TAG_structure_type, dW_TAG_pointer_type,
  dW_TAG_array_type, dW_TAG_subrange_type, dW_TAG_typedef,
  dW_TAG_variable, dW_TAG_arg_variable, dW_TAG_auto_variable :: Word
dW_TAG_array_type      = 1
dW_TAG_lexical_block   = 11
dW_TAG_pointer_type    = 15
dW_TAG_compile_unit    = 17
dW_TAG_structure_type  = 19
dW_TAG_typedef         = 22
dW_TAG_subroutine_type = 32
dW_TAG_subrange_type   = 33
dW_TAG_base_type       = 36
dW_TAG_file_type       = 41
dW_TAG_subprogram      = 46
dW_TAG_variable        = 52
dW_TAG_auto_variable   = 256
dW_TAG_arg_variable    = 257

-- | Dwarf attributes
dW_AT_name, dW_AT_stmt_list, dW_AT_low_pc, dW_AT_high_pc, dW_AT_language,
  dW_AT_comp_dir, dW_AT_producer, dW_AT_external, dW_AT_MIPS_linkage_name :: Word
dW_AT_name              = 0x03
dW_AT_stmt_list         = 0x10
dW_AT_low_pc            = 0x11
dW_AT_high_pc           = 0x12
dW_AT_language          = 0x13
dW_AT_comp_dir          = 0x1b
dW_AT_producer          = 0x25
dW_AT_external          = 0x3f
dW_AT_MIPS_linkage_name = 0x2007

-- | Abbrev declaration
dW_CHILDREN_no, dW_CHILDREN_yes :: Word8
dW_CHILDREN_no  = 0
dW_CHILDREN_yes = 1

dW_FORM_addr, dW_FORM_data4, dW_FORM_string, dW_FORM_flag, dW_FORM_ref4 :: Word
dW_FORM_addr   = 0x01
dW_FORM_data4  = 0x06
dW_FORM_string = 0x08
dW_FORM_flag   = 0x0c
dW_FORM_ref4   = 0x13

-- | Dwarf native types
dW_ATE_address, dW_ATE_boolean, dW_ATE_float, dW_ATE_signed,
  dW_ATE_signed_char, dW_ATE_unsigned, dW_ATE_unsigned_char :: Word
dW_ATE_address       = 1
dW_ATE_boolean       = 2
dW_ATE_float         = 4
dW_ATE_signed        = 5
dW_ATE_signed_char   = 6
dW_ATE_unsigned      = 7
dW_ATE_unsigned_char = 8

-- | Dwarf section declarations
dwarfInfoSection, dwarfAbbrevSection, dwarfLineSection, dwarfGhcSection :: SDoc
dwarfInfoSection   = ptext (sLit ".section .debug_info,\"\",@progbits")
dwarfAbbrevSection = ptext (sLit ".section .debug_abbrev,\"\",@progbits")
dwarfLineSection   = ptext (sLit ".section .debug_line,\"\",@progbits")
dwarfGhcSection    = ptext (sLit ".section .debug_ghc,\"\",@progbits")

-- | Dwarf section labels
dwarfInfoLabel, dwarfAbbrevLabel, dwarfLineLabel :: LitString
dwarfInfoLabel   = sLit ".Lsection_info"
dwarfAbbrevLabel = sLit ".Lsection_abbrev"
dwarfLineLabel   = sLit ".Lsection_line"
