-- -----------------------------------------------------------------------------
-- | This is the top-level module in the LLVM code generator.
--

{-# LANGUAGE GADTs #-}
module LlvmCodeGen ( llvmCodeGen, llvmFixupAsm ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Base
import LlvmCodeGen.CodeGen
import LlvmCodeGen.Data
import LlvmCodeGen.Ppr
import LlvmMangler

import LlvmMeta

import BlockId ( blockLbl )
import CgUtils ( fixStgRegisters )
import Cmm
import Hoopl
import PprCmm
import CmmUtils ( toBlockList )
import Module
import Debug

import BufWrite
import DynFlags
import ErrUtils
import FastString
import Outputable
import UniqSupply
import SysTools ( figureLlvmVersion )
import MonadUtils
import qualified Stream

import Data.Maybe ( fromMaybe, catMaybes )
import Control.Monad ( when )
import Data.IORef ( writeIORef )
import System.IO

-- -----------------------------------------------------------------------------
-- | Top-level of the LLVM Code generator
--
llvmCodeGen :: DynFlags -> ModLocation -> Handle -> UniqSupply
               -> Stream.Stream IO (RawCmmGroup,TickMap) ()
               -> IO ()
llvmCodeGen dflags location h us cmm_stream
  = do bufh <- newBufHandle h

       -- get llvm version, cache for later use
       ver <- getLlvmVersion dflags

       -- warn if unsupported
       when (ver < minSupportLlvmVersion) $
           errorMsg dflags (text "You are using an old version of LLVM that"
                            <> text " isn't supported anymore!"
                            $+$ text "We will try though...")
       when (ver > maxSupportLlvmVersion) $
           putMsg dflags (text "You are using a new version of LLVM that"
                          <> text " hasn't been tested yet!"
                          $+$ text "We will try though...")

       -- run code generation
       runLlvm dflags ver bufh us $
         llvmCodeGen' location (liftStream cmm_stream)

       bFlush bufh

-- | Handle setting up the LLVM version.
getLlvmVersion :: DynFlags -> IO Int
getLlvmVersion dflags = do
        ver <- (fromMaybe defaultLlvmVersion) `fmap` figureLlvmVersion dflags
        -- cache llvm version for later use
        writeIORef (llvmVersion dflags) ver
        when (ver < minSupportLlvmVersion) $
            errorMsg dflags (text "You are using an old version of LLVM that"
                             <> text "isn't supported anymore!"
                             $+$ text "We will try though...")
        when (ver > maxSupportLlvmVersion) $
            putMsg dflags (text "You are using a new version of LLVM that"
                           <> text "hasn't been tested yet!"
                           $+$ text "We will try though...")
        return ver


llvmCodeGen' :: ModLocation -> Stream.Stream LlvmM (RawCmmGroup,TickMap) () -> LlvmM ()
llvmCodeGen' location cmm_stream
  = do  -- Preamble
        renderLlvm pprLlvmHeader
        ghcInternalFunctions
        cmmMetaLlvmPrelude location

        -- Procedures
        let llvmStream = Stream.mapM (llvmGroupLlvmGens location) cmm_stream
        tick_maps <- Stream.collect llvmStream

        -- Declare aliases for forward references
        renderLlvm . pprLlvmData =<< generateAliases

        -- Postamble
        cmmMetaLlvmUnit location
        cmmDebugLlvmGens location (last tick_maps)
        cmmUsedLlvmGens

llvmGroupLlvmGens :: ModLocation -> (RawCmmGroup, TickMap) -> LlvmM TickMap
llvmGroupLlvmGens location (cmm, tick_map) = do

        -- Insert functions into map, collect data
        let split (CmmData s d' )     = return $ Just (s, d')
            split (CmmProc h l live g) = do
              let l' = case mapLookup (g_entry g) h of
                         Nothing                   -> l
                         Just (Statics info_lbl _) -> info_lbl
              lml <- strCLabel_llvm l'
              funInsert lml =<< llvmFunTy live
              labelInsert l l'
              return Nothing
        cdata <- fmap catMaybes $ mapM split cmm

        {-# SCC "llvm_datas_gen" #-}
          cmmDataLlvmGens cdata
        {-# SCC "llvm_procs_gen" #-}
          mapM_ (cmmLlvmGen location tick_map) cmm
        return tick_map

-- -----------------------------------------------------------------------------
-- | Do LLVM code generation on all these Cmms data sections.
--
cmmDataLlvmGens :: [(Section,CmmStatics)] -> LlvmM ()

cmmDataLlvmGens statics
  = do lmdatas <- mapM genLlvmData statics

       let (gss, tss) = unzip lmdatas

       let regGlobal (LMGlobal (LMGlobalVar l ty _ _ _ _) _)
                        = funInsert l ty
           regGlobal _  = return ()
       mapM_ regGlobal (concat gss)

       renderLlvm $ pprLlvmData (concat gss, concat tss)

-- | Complete LLVM code generation phase for a single top-level chunk of Cmm.
cmmLlvmGen :: ModLocation -> TickMap -> RawCmmDecl -> LlvmM ()
cmmLlvmGen mod_loc tick_map cmm@(CmmProc h lbl _ blocks) = do

    -- rewrite assignments to global regs
    dflags <- getDynFlag id
    let fixed_cmm = {-# SCC "llvm_fix_regs" #-}
                    fixStgRegisters dflags cmm

    liftIO $ dumpIfSet_dyn dflags Opt_D_dump_opt_cmm "Optimised Cmm"
        (pprCmmGroup [fixed_cmm])

    -- Find and emit debug info for procedure
    let entryLbl = case mapLookup (g_entry blocks) h of
          Nothing                   -> lbl
          Just (Statics info_lbl _) -> info_lbl
        split = map blockSplit $ toBlockList blocks
    let blockLbls = map (\(CmmEntry id, _, _) -> blockLbl id) split
    annotId <- cmmMetaLlvmProc lbl entryLbl blockLbls mod_loc tick_map

    -- generate llvm code from cmm
    llvmBC <- withClearVars $ genLlvmProc fixed_cmm annotId

    -- allocate IDs for info table and code, so the mangler can later
    -- make sure they end up next to each other.
    itableSection <- freshSectionId
    _codeSection <- freshSectionId

    -- pretty print
    (docs, ivars) <- fmap unzip $ mapM (pprLlvmCmmDecl itableSection) llvmBC

    -- Output, note down used variables
    renderLlvm (vcat docs)
    mapM_ markUsedVar $ concat ivars

cmmLlvmGen _ _ _ = return ()

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
      lmUsedVar = LMGlobalVar (fsLit "llvm.used") ty Appending sectName Nothing Constant
      lmUsed    = LMGlobal lmUsedVar (Just usedArray)
  if null ivars
     then return ()
     else renderLlvm $ pprLlvmData ([lmUsed], [])
