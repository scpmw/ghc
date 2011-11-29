-- ----------------------------------------------------------------------------
-- | Pretty print helpers for the LLVM Code generator.
--

module LlvmCodeGen.Ppr (
        pprLlvmHeader, pprLlvmCmmDecl, pprLlvmData, infoSection, iTableSuf
    ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Base
import LlvmCodeGen.Data

import CLabel
import OldCmm

import FastString
import Outputable
import Unique

import qualified Data.Map as Map ( lookup )

-- ----------------------------------------------------------------------------
-- * Top level
--

-- | LLVM module layout description for the host target
moduleLayout :: SDoc
moduleLayout =
#if i386_TARGET_ARCH

#if darwin_TARGET_OS
    text "target datalayout = \"e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128-n8:16:32\""
    $+$ text "target triple = \"i386-apple-darwin9.8\""
#elif mingw32_TARGET_OS
    text "target datalayout = \"e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-f80:128:128-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32\""
    $+$ text "target triple = \"i686-pc-win32\""
#else /* Linux */
    text "target datalayout = \"e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32\""
    $+$ text "target triple = \"i386-pc-linux-gnu\""
#endif

#elif x86_64_TARGET_ARCH

#if darwin_TARGET_OS
    text "target datalayout = \"e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64\""
    $+$ text "target triple = \"x86_64-apple-darwin10.0.0\""
#else /* Linux */
    text "target datalayout = \"e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64\""
    $+$ text "target triple = \"x86_64-linux-gnu\""
#endif

#elif defined (arm_TARGET_ARCH)

#if linux_TARGET_OS
    text "target datalayout = \"e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:64:128-a0:0:64-n32\""
    $+$ text "target triple = \"arm-unknown-linux-gnueabi\""
#endif

#else
    -- FIX: Other targets
    empty
#endif


-- | Header code for LLVM modules
pprLlvmHeader :: SDoc
pprLlvmHeader = moduleLayout


-- | Pretty print LLVM data code
pprLlvmData :: LlvmData -> SDoc
pprLlvmData (globals, types) =
    let ppLlvmTys (LMAlias    a) = ppLlvmAlias a
        ppLlvmTys (LMFunction f) = ppLlvmFunctionDecl f
        ppLlvmTys _other         = empty

        types'   = vcat $ map ppLlvmTys types
        globals' = ppLlvmGlobals globals
    in types' $+$ globals'


-- | Pretty print LLVM code
pprLlvmCmmDecl :: TickMap -> Int -> LlvmCmmDecl -> LlvmM (SDoc, [LlvmVar])
pprLlvmCmmDecl _ _ (CmmData _ lmdata)
  = return (vcat $ map pprLlvmData lmdata, [])

pprLlvmCmmDecl tick_map count (CmmProc mb_info entry_lbl (ListGraph blks))
  = do (idoc, ivar) <- case mb_info of
                        Nothing -> return (empty, [])
                        Just (Statics info_lbl dat)
                         -> pprInfoTable count info_lbl (Statics entry_lbl dat)

       let sec = mkLayoutSection (count + 1)
           (lbl',sec') = case mb_info of
                           Nothing                   -> (entry_lbl, Nothing)
                           Just (Statics info_lbl _) -> (info_lbl,  sec)
           link = if externallyVisibleCLabel lbl'
                      then ExternallyVisible
                      else Internal
           lmblocks = map (\(BasicBlock id stmts) ->
                                LlvmBlock (getUnique id) stmts) blks
           instr = Map.lookup entry_lbl tick_map >>= timInstr

       fun <- mkLlvmFunc lbl' link  sec' lmblocks instr

       return (idoc $+$ ppLlvmFunction fun, ivar)


-- | Pretty print CmmStatic
pprInfoTable :: Int -> CLabel -> CmmStatics -> LlvmM (SDoc, [LlvmVar])
pprInfoTable count info_lbl stat
  = do unres <- genLlvmData (Text, stat)
       (ldata, ltypes) <- resolveLlvmData unres

       let setSection (LMGlobal (LMGlobalVar _ ty l _ _ c) d) = do
             lbl <- strCLabel_llvm info_lbl
             let sec = mkLayoutSection count
                 ilabel = lbl `appendFS` fsLit iTableSuf
                 gv = LMGlobalVar ilabel ty l sec llvmInfAlign c
                 v = if l == Internal then [gv] else []
             return (LMGlobal gv d, v)
           setSection v = return (v,[])

       (ldata', llvmUsed) <- setSection (last ldata)
       if length ldata /= 1
          then Outputable.panic "LlvmCodeGen.Ppr: invalid info table!"
          else return (pprLlvmData ([ldata'], ltypes), llvmUsed)


-- | We generate labels for info tables by converting them to the same label
-- as for the entry code but adding this string as a suffix.
iTableSuf :: String
iTableSuf = "_itable"


-- | Create a specially crafted section declaration that encodes the order this
-- section should be in the final object code.
-- 
-- The LlvmMangler.llvmFixupAsm pass over the assembly produced by LLVM uses
-- this section declaration to do its processing.
mkLayoutSection :: Int -> LMSection
mkLayoutSection n
  = Just (fsLit $ infoSection ++ show n)


-- | The section we are putting info tables and their entry code into, should
-- be unique since we process the assembly pattern matching this.
infoSection :: String
infoSection = "X98A__STRIP,__me"

