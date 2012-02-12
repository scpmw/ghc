-- -----------------------------------------------------------------------------
-- | This is the top-level module in the LLVM code generator.
--

module LlvmCodeGen ( llvmCodeGen, llvmFixupAsm ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Base
import LlvmCodeGen.CodeGen
import LlvmCodeGen.Data
import LlvmCodeGen.Ppr
import LlvmMangler

import LlvmMeta

import CLabel
import CgUtils ( fixStgRegisters )
import OldCmm
import OldPprCmm
import Module

import BufWrite
import DynFlags
import ErrUtils
import FastString
import Outputable
import UniqSupply
import SysTools ( figureLlvmVersion )
import MonadUtils

import Data.Maybe ( fromMaybe, catMaybes )
import System.IO

-- -----------------------------------------------------------------------------
-- | Top-level of the LLVM Code generator
--
llvmCodeGen :: DynFlags -> ModLocation -> Handle -> UniqSupply -> [RawCmmGroup] -> TickMap -> IO ()
llvmCodeGen dflags location h us cmms tick_map
  = do bufh <- newBufHandle h
       ver  <- (fromMaybe defaultLlvmVersion) `fmap` figureLlvmVersion dflags

       runLlvm (targetPlatform dflags) ver bufh us $
         llvmCodeGen' dflags location cmms tick_map

       bFlush bufh

llvmCodeGen' :: DynFlags -> ModLocation -> [RawCmmGroup] -> TickMap -> LlvmM ()
llvmCodeGen' dflags location cmms tick_map
  = do
        -- Insert functions into map, collect data
        let split (CmmData s d' ) = return $ Just (s, d')
            split (CmmProc i l _) = do
              lbl <- strCLabel_llvm $ case i of
                         Nothing                   -> l
                         Just (Statics info_lbl _) -> info_lbl
              funInsert lbl llvmFunTy
              return Nothing
        let cmm = concat cmms
        cdata <- fmap catMaybes $ mapM split cmm

        renderLlvm pprLlvmHeader
        ghcInternalFunctions
        
        {-# SCC "llvm_datas_gen" #-}
          cmmDataLlvmGens dflags cdata []
        {-# SCC "llvm_procs_gen" #-}
          cmmProcLlvmGens dflags cmm tick_map 1
        cmmMetaLlvmGens dflags location tick_map cmm
        cmmDebugLlvmGens dflags location tick_map cmm

        cmmUsedLlvmGens


-- -----------------------------------------------------------------------------
-- | Do LLVM code generation on all these Cmms data sections.
--
cmmDataLlvmGens :: DynFlags -> [(Section,CmmStatics)]
                -> [LlvmUnresData] -> LlvmM ()

cmmDataLlvmGens dflags [] lmdata
  = do lmdata' <- resolveLlvmDatas (reverse lmdata)
       let lmdoc = vcat $ map pprLlvmData lmdata'
       liftIO $ dumpIfSet_dyn dflags Opt_D_dump_llvm "LLVM Code" lmdoc
       renderLlvm lmdoc

cmmDataLlvmGens dflags (cmm:cmms) lmdata
  = do lmdata'@(l, _, ty, _) <- genLlvmData cmm
       l' <- strCLabel_llvm l
       funInsert l' ty
       cmmDataLlvmGens dflags cmms (lmdata' : lmdata)


-- -----------------------------------------------------------------------------
-- | Do LLVM code generation on all these Cmms procs.
--
cmmProcLlvmGens :: DynFlags -> [RawCmmDecl] -> TickMap
      -> Int         -- ^ count, used for generating unique subsections
      -> LlvmM ()

cmmProcLlvmGens _ [] _ _
  = return ()

cmmProcLlvmGens dflags ((CmmData _ _) : cmms) tick_map count
 = cmmProcLlvmGens dflags cmms tick_map count

cmmProcLlvmGens dflags ((CmmProc _ _ (ListGraph [])) : cmms) tick_map count
 = cmmProcLlvmGens dflags cmms tick_map count

cmmProcLlvmGens dflags (cmm : cmms) tick_map count
 = do cmmLlvmGen dflags tick_map count cmm
      cmmProcLlvmGens dflags cmms tick_map (count + 2)


-- | Complete LLVM code generation phase for a single top-level chunk of Cmm.
cmmLlvmGen :: DynFlags -> TickMap -> Int -> RawCmmDecl -> LlvmM ()
cmmLlvmGen dflags tick_map count cmm = do
    -- rewrite assignments to global regs
    let fixed_cmm = fixStgRegisters cmm

    liftIO $ dumpIfSet_dyn dflags Opt_D_dump_opt_cmm "Optimised Cmm"
        (pprCmmGroup (targetPlatform dflags) [fixed_cmm])

    -- generate llvm code from cmm
    llvmBC <- withClearVars $ genLlvmProc fixed_cmm

    -- print to buffer, dump if requested
    let pp = pprLlvmCmmDecl tick_map count
    (docs, ivars) <- fmap unzip $ mapM pp llvmBC
    liftIO $ dumpIfSet_dyn dflags Opt_D_dump_llvm "LLVM Code" (vcat docs)

    -- Output, note down used variables
    renderLlvm (vcat docs)
    mapM_ markUsedVar $ concat ivars

-- -----------------------------------------------------------------------------
-- | Marks variables as used where necessary
--

cmmUsedLlvmGens :: LlvmM ()
cmmUsedLlvmGens = do

  -- LLVM would discard variables that are internal and not obviously
  -- used if we didn't provide these hints. This will generate a
  -- definition of the form
  --
  --   @llvm.used = appending global [42 x i8*] [i8* bitcast <var> to i8*, ...]
  --
  -- Which is the LLVM way of protecting them against getting removed.
  ivars <- getUsedVars
  let cast x = LMBitc (LMStaticPointer (pVarLift x)) i8Ptr
      ty     = (LMArray (length ivars) i8Ptr)
      usedArray = LMStaticArray (map cast ivars) ty
      sectName  = Just $ fsLit "llvm.metadata"
      lmUsedVar = LMGlobalVar (fsLit "llvm.used") ty Appending sectName Nothing False
      lmUsed    = LMGlobal lmUsedVar (Just usedArray)
  if null ivars
     then return ()
     else renderLlvm $ pprLlvmData ([lmUsed], [])
