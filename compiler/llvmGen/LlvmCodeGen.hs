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
import qualified Pretty as Prt
import UniqSupply
import Util
import SysTools ( figureLlvmVersion )

import Data.Maybe ( fromMaybe )
import System.IO

-- -----------------------------------------------------------------------------
-- | Top-level of the LLVM Code generator
--
llvmCodeGen :: DynFlags -> ModLocation -> Handle -> UniqSupply -> [RawCmmGroup] -> TickMap -> IO ()
llvmCodeGen dflags location h us cmms tick_map
  = let cmm = concat cmms
        (cdata,env) = foldr split ([],initLlvmEnv (targetPlatform dflags)) cmm
        split (CmmData s d' ) (d,e) = ((s,d'):d,e)
        split (CmmProc i l _) (d,e) =
            let lbl = strCLabel_llvm env $ case i of
                        Nothing                   -> l
                        Just (Statics info_lbl _) -> info_lbl
                env' = funInsert lbl llvmFunTy e
            in (d,env')
    in do
        bufh <- newBufHandle h
        let render = Prt.bufLeftRender bufh . withPprStyleDoc (mkCodeStyle CStyle)

        render pprLlvmHeader
        ver  <- (fromMaybe defaultLlvmVersion) `fmap` figureLlvmVersion dflags
        env' <- cmmDataLlvmGens dflags render (setLlvmVer ver env) cdata []
        env'' <- cmmProcLlvmGens dflags render us env' cmm tick_map 1 []
        cmmMetaLlvmGens dflags location render tick_map env'' cmm
        cmmDebugLlvmGens dflags location render tick_map env'' cmm

        bFlush bufh
        return  ()


-- -----------------------------------------------------------------------------
-- | Do LLVM code generation on all these Cmms data sections.
--
cmmDataLlvmGens :: DynFlags -> (SDoc -> IO ()) -> LlvmEnv -> [(Section,CmmStatics)]
                -> [LlvmUnresData] -> IO ( LlvmEnv )

cmmDataLlvmGens dflags render env [] lmdata
  = let (env', lmdata') = resolveLlvmDatas env lmdata []
        lmdoc = vcat $ map pprLlvmData lmdata'
    in do
        dumpIfSet_dyn dflags Opt_D_dump_llvm "LLVM Code" lmdoc
        render lmdoc
        return env'

cmmDataLlvmGens dflags render env (cmm:cmms) lmdata
  = let lmdata'@(l, _, ty, _) = genLlvmData env cmm
        env' = funInsert (strCLabel_llvm env l) ty env
    in cmmDataLlvmGens dflags render env' cmms (lmdata ++ [lmdata'])


-- -----------------------------------------------------------------------------
-- | Do LLVM code generation on all these Cmms procs.
--
cmmProcLlvmGens :: DynFlags -> (SDoc -> IO ()) -> UniqSupply -> LlvmEnv -> [RawCmmDecl] -> TickMap
      -> Int         -- ^ count, used for generating unique subsections
      -> [[LlvmVar]] -- ^ info tables that need to be marked as 'used'
      -> IO LlvmEnv

cmmProcLlvmGens _ _ _ env [] _ _ []
  = return env

cmmProcLlvmGens _ render _ env [] _ _ ivars
  = let ivars' = concat ivars
        cast x = LMBitc (LMStaticPointer (pVarLift x)) i8Ptr
        ty     = (LMArray (length ivars') i8Ptr)
        usedArray = LMStaticArray (map cast ivars') ty
        sectName  = Just $ fsLit "llvm.metadata"
        lmUsedVar = LMGlobalVar (fsLit "llvm.used") ty Appending sectName Nothing False
        lmUsed    = LMGlobal lmUsedVar (Just usedArray)
    in do render $ pprLlvmData ([lmUsed], [])
          return env

cmmProcLlvmGens dflags render us env ((CmmData _ _) : cmms) tick_map count ivars
 = cmmProcLlvmGens dflags render us env cmms tick_map count ivars

cmmProcLlvmGens dflags render us env ((CmmProc _ _ (ListGraph [])) : cmms) tick_map count ivars
 = cmmProcLlvmGens dflags render us env cmms tick_map count ivars

cmmProcLlvmGens dflags render us env (cmm : cmms) tick_map count ivars = do
    (us', env', llvm) <- cmmLlvmGen dflags us (clearVars env) tick_map cmm
    let (docs, ivar) = mapAndUnzip (pprLlvmCmmDecl env' tick_map count) llvm
    render (vcat docs)
    cmmProcLlvmGens dflags render us' env' cmms tick_map (count + 2) (ivar ++ ivars)


-- | Complete LLVM code generation phase for a single top-level chunk of Cmm.
cmmLlvmGen :: DynFlags -> UniqSupply -> LlvmEnv -> TickMap -> RawCmmDecl
            -> IO ( UniqSupply, LlvmEnv, [LlvmCmmDecl] )
cmmLlvmGen dflags us env tick_map cmm = do
    -- rewrite assignments to global regs
    let fixed_cmm = fixStgRegisters cmm

    dumpIfSet_dyn dflags Opt_D_dump_opt_cmm "Optimised Cmm"
        (pprCmmGroup (targetPlatform dflags) [fixed_cmm])

    -- generate llvm code from cmm
    let ((env', llvmBC), usGen) = initUs us $ genLlvmProc env fixed_cmm

    dumpIfSet_dyn dflags Opt_D_dump_llvm "LLVM Code"
        (vcat $ map (fst . pprLlvmCmmDecl env' tick_map 0) llvmBC)

    return (usGen, env', llvmBC)
