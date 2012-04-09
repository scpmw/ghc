{-# OPTIONS -fno-warn-type-defaults #-}
-- ----------------------------------------------------------------------------
-- | Handle conversion of CmmProc to LLVM code.
--

module LlvmCodeGen.CodeGen ( genLlvmProc ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Base
import LlvmCodeGen.Regs

import LlvmMeta ( genVariableMeta, LlvmAnnotator )

import BlockId
import CgUtils ( activeStgRegs, callerSaves )
import CLabel
import OldCmm
import qualified OldPprCmm as PprCmm

import DynFlags
import FastString
import ForeignCall
import Outputable hiding ( panic, pprPanic )
import qualified Outputable
import Platform
import OrdList
import UniqSupply
import Unique

import Data.List ( nub )

type LlvmStatements = OrdList LlvmStatement

-- -----------------------------------------------------------------------------
-- | Top-level of the LLVM proc Code generator
--
genLlvmProc :: RawCmmDecl -> LlvmAnnotator -> LlvmM [LlvmCmmDecl]
genLlvmProc (CmmProc info lbl (ListGraph blocks)) annotGen = do
    (lmblocks, lmdata) <- basicBlocksCodeGen blocks (annotGen lbl) annotGen
    let proc = CmmProc info lbl (ListGraph lmblocks)
    return (proc:lmdata)

genLlvmProc _ _ = panic "genLlvmProc: case that shouldn't reach here!"

-- -----------------------------------------------------------------------------
-- * Block code generation
--

-- | Generate code for a list of blocks that make up a complete procedure.
basicBlocksCodeGen :: [CmmBasicBlock] -> (LMMetaInt, LMMetaInt) -> LlvmAnnotator
                      -> LlvmM ([LlvmBasicBlock] , [LlvmCmmDecl] )
basicBlocksCodeGen cmmBlocks (blockId, annotId) annotGen
  = do (prologue, tops1) <- funPrologue cmmBlocks blockId
       (blockss, topss) <- fmap unzip $ mapM (basicBlockCodeGen annotGen) cmmBlocks
       let ((BasicBlock bid fstmts):rblks) = concat blockss
       let annot = MetaStmt [(fsLit "dbg", annotId)]
       let fblocks = (BasicBlock bid $ (map annot $ fromOL prologue) ++ fstmts):rblks
       return (fblocks, tops1 ++ concat topss)


-- | Generate code for one block
basicBlockCodeGen :: LlvmAnnotator -> CmmBasicBlock
                     -> LlvmM ( [LlvmBasicBlock], [LlvmCmmDecl] )
basicBlockCodeGen annotGen (BasicBlock id stmts)
  = do (instrs, top) <- stmtsToInstrs stmts
       let annot = MetaStmt [(fsLit "dbg", snd $ annotGen $ blockLbl id)]
       return ([BasicBlock id (map annot $ fromOL instrs)], top)


-- -----------------------------------------------------------------------------
-- * CmmStmt code generation
--

-- A statement conversion return data.
--   * LlvmStatements: The compiled LLVM statements.
--   * LlvmCmmDecl: Any global data needed.
type StmtData = (LlvmStatements, [LlvmCmmDecl])


-- | Convert a list of CmmStmt's to LlvmStatement's
stmtsToInstrs :: [CmmStmt] -> LlvmM StmtData
stmtsToInstrs stmts
   = do (instrss, topss) <- fmap unzip $ mapM stmtToInstrs stmts
        return (concatOL instrss, concat topss)


-- | Convert a CmmStmt to a list of LlvmStatement's
stmtToInstrs :: CmmStmt -> LlvmM StmtData
stmtToInstrs stmt = case stmt of

    CmmNop               -> return (nilOL, [])
    CmmComment _         -> return (nilOL, []) -- nuke comments

    CmmAssign reg src    -> genAssign reg src
    CmmStore addr src    -> genStore addr src

    CmmBranch id         -> genBranch id
    CmmCondBranch arg id -> genCondBranch arg id
    CmmSwitch arg ids    -> genSwitch arg ids

    -- Foreign Call
    CmmCall target res args ret
        -> genCall target res args ret

    -- Tail call
    CmmJump arg live     -> genJump arg live

    -- CPS, only tail calls, no return's
    -- Actually, there are a few return statements that occur because of hand
    -- written Cmm code.
    CmmReturn
        -> return (unitOL $ Return Nothing, [])

-- | Wrapper function to declare an instrinct function, if required
declareInstrinct :: LMString -> LlvmType -> [LlvmType] -> LlvmM (LlvmVar, [LlvmCmmDecl])
declareInstrinct fname retTy parTys = do

    let funSig = LlvmFunctionDecl fname ExternallyVisible CC_Ccc retTy
                    FixedArgs (tysToParams parTys) llvmFunAlign
    let fty = LMFunction funSig

    let fv   = LMGlobalVar fname fty (funcLinkage funSig) Nothing Nothing False

    fn <- funLookup fname
    tops <- case fn of
      Just _  ->
        return []
      Nothing -> do
        funInsert fname fty
        return [CmmData Data [([],[fty])]]

    return (fv, tops)

-- | Memory barrier instruction for LLVM >= 3.0
barrier :: LlvmM StmtData
barrier = do
    let s = Fence False SyncSeqCst
    return (unitOL s, [])

-- | Memory barrier instruction for LLVM < 3.0
oldBarrier :: LlvmM StmtData
oldBarrier = do

    (fv, tops) <- declareInstrinct (fsLit "llvm.memory.barrier") LMVoid [i1, i1, i1, i1, i1]

    let args = [lmTrue, lmTrue, lmTrue, lmTrue, lmTrue]
    let s1 = Expr $ Call StdCall fv args llvmStdFunAttrs

    return (unitOL s1, tops)

    where
        lmTrue :: LlvmVar
        lmTrue  = mkIntLit i1 (-1)

-- | Foreign Calls
genCall :: CmmCallTarget -> [HintedCmmFormal] -> [HintedCmmActual]
              -> CmmReturnInfo -> LlvmM StmtData

-- Write barrier needs to be handled specially as it is implemented as an LLVM
-- intrinsic function.
genCall (CmmPrim MO_WriteBarrier _) _ _ _ = do
    platform <- getLlvmPlatform
    ver <- getLlvmVer
    case () of
     _ | platformArch platform `elem` [ArchX86, ArchX86_64, ArchSPARC]
                    -> return (nilOL, [])
       | ver > 29   -> barrier
       | otherwise  -> oldBarrier

-- Handle popcnt function specifically since GHC only really has i32 and i64
-- types and things like Word8 are backed by an i32 and just present a logical
-- i8 range. So we must handle conversions from i32 to i8 explicitly as LLVM
-- is strict about types.
genCall (CmmPrim op@(MO_PopCnt w) _) [CmmHinted dst _] args _ = do
    let width = widthToLlvmInt w
        dstTy = cmmToLlvmType $ localRegType dst

    fname                       <- cmmPrimOpFunctions op
    (fptr, top3)                <- declareInstrinct fname width [width]

    dstV                        <- getCmmReg (CmmLocal dst)

    (argsV, stmts2, top2)       <- arg_vars args ([], nilOL, [])
    (argsV', stmts4)            <- castVars $ zip argsV [width]
    (retV, s1)                  <- doExpr width $ Call StdCall fptr argsV' []
    ([retV'], stmts5)           <- castVars [(retV,dstTy)]
    let s2                       = Store retV' dstV

    let stmts = stmts2 `appOL` stmts4 `snocOL`
                s1 `appOL` stmts5 `snocOL` s2
    return (stmts, top2 ++ top3)

-- Handle memcpy function specifically since llvm's intrinsic version takes
-- some extra parameters.
genCall t@(CmmPrim op _) [] args CmmMayReturn
 | op == MO_Memcpy ||
   op == MO_Memset ||
   op == MO_Memmove = do
    ver <- getLlvmVer
    let (isVolTy, isVolVal)
              | ver >= 28       = ([i1], [mkIntLit i1 0]) 
              | otherwise       = ([], [])
        argTy | op == MO_Memset = [i8Ptr, i8,    llvmWord, i32] ++ isVolTy
              | otherwise       = [i8Ptr, i8Ptr, llvmWord, i32] ++ isVolTy
        funTy = \name -> LMFunction $ LlvmFunctionDecl name ExternallyVisible
                             CC_Ccc LMVoid FixedArgs (tysToParams argTy) Nothing

    (argVars, stmts1, top1)       <- arg_vars args ([], nilOL, [])
    (fptr, stmts2, top2)          <- getFunPtr funTy t
    (argVars', stmts3)            <- castVars $ zip argVars argTy

    stmts4 <- trashStmts
    let arguments = argVars' ++ isVolVal
        call = Expr $ Call StdCall fptr arguments []
        stmts = stmts1 `appOL` stmts2 `appOL` stmts3
                `appOL` stmts4 `snocOL` call
    return (stmts, top1 ++ top2)

genCall (CmmPrim _ (Just stmts)) _ _ _
    = stmtsToInstrs stmts

-- Handle all other foreign calls and prim ops.
genCall target res args ret = do

    -- parameter types
    let arg_type (CmmHinted _ AddrHint) = i8Ptr
        -- cast pointers to i8*. Llvm equivalent of void*
        arg_type (CmmHinted expr _    ) = cmmToLlvmType $ cmmExprType expr

    -- ret type
    let ret_type ([]) = LMVoid
        ret_type ([CmmHinted _ AddrHint]) = i8Ptr
        ret_type ([CmmHinted reg _])      = cmmToLlvmType $ localRegType reg
        ret_type t = panic $ "genCall: Too many return values! Can only handle"
                        ++ " 0 or 1, given " ++ show (length t) ++ "."

    -- extract Cmm call convention
    let cconv = case target of
            CmmCallee _ conv -> conv
            CmmPrim   _ _    -> PrimCallConv

    -- translate to LLVM call convention
    platform <- getLlvmPlatform
    let lmconv = case cconv of
            StdCallConv  -> case platformArch platform of
                            ArchX86    -> CC_X86_Stdcc
                            ArchX86_64 -> CC_X86_Stdcc
                            _          -> CC_Ccc
            CCallConv    -> CC_Ccc
            CApiConv     -> CC_Ccc
            PrimCallConv -> CC_Ccc
            CmmCallConv  -> panic "CmmCallConv not supported here!"

    {-
        Some of the possibilities here are a worry with the use of a custom
        calling convention for passing STG args. In practice the more
        dangerous combinations (e.g StdCall + llvmGhcCC) don't occur.

        The native code generator only handles StdCall and CCallConv.
    -}

    -- call attributes
    let fnAttrs | ret == CmmNeverReturns = NoReturn : llvmStdFunAttrs
                | otherwise              = llvmStdFunAttrs

    -- fun type
    let ccTy  = StdCall -- tail calls should be done through CmmJump
    let retTy = ret_type res
    let argTy = tysToParams $ map arg_type args
    let funTy = \name -> LMFunction $ LlvmFunctionDecl name ExternallyVisible
                             lmconv retTy FixedArgs argTy llvmFunAlign


    (argVars, stmts1, top1) <- arg_vars args ([], nilOL, [])
    (fptr, stmts2, top2)    <- getFunPtr funTy target

    let retStmt | ccTy == TailCall       = unitOL $ Return Nothing
                | ret == CmmNeverReturns = unitOL $ Unreachable
                | otherwise              = nilOL

    stmts3 <- trashStmts
    let stmts = stmts1 `appOL` stmts2 `appOL` stmts3

    -- make the actual call
    case retTy of
        LMVoid -> do
            let s1 = Expr $ Call ccTy fptr argVars fnAttrs
            let allStmts = stmts `snocOL` s1 `appOL` retStmt
            return (allStmts, top1 ++ top2)

        _ -> do
            (v1, s1) <- doExpr retTy $ Call ccTy fptr argVars fnAttrs
            -- get the return register
            let ret_reg ([CmmHinted reg hint]) = (reg, hint)
                ret_reg t = panic $ "genCall: Bad number of registers! Can only handle"
                                ++ " 1, given " ++ show (length t) ++ "."
            let (creg, _) = ret_reg res
            vreg <- getCmmReg (CmmLocal creg)
            let allStmts = stmts `snocOL` s1
            if retTy == pLower (getVarType vreg)
                then do
                    let s2 = Store v1 vreg
                    return (allStmts `snocOL` s2 `appOL` retStmt,
                                top1 ++ top2)
                else do
                    let ty = pLower $ getVarType vreg
                    let op = case ty of
                            vt | isPointer vt -> LM_Bitcast
                               | isInt     vt -> LM_Ptrtoint
                               | otherwise    ->
                                   panic $ "genCall: CmmReg bad match for"
                                        ++ " returned type!"

                    (v2, s2) <- doExpr ty $ Cast op v1 ty
                    let s3 = Store v2 vreg
                    return (allStmts `snocOL` s2 `snocOL` s3
                                `appOL` retStmt, top1 ++ top2)


-- | Create a function pointer from a target.
getFunPtr :: (LMString -> LlvmType) -> CmmCallTarget
          -> LlvmM ExprData
getFunPtr funTy targ = case targ of
    CmmCallee (CmmLit (CmmLabel lbl)) _ -> do 
        name <- strCLabel_llvm lbl
        litCase name

    CmmCallee expr _ -> do
        (v1, stmts, top) <- exprToVar expr
        let fty = funTy $ fsLit "dynamic"
            cast = case getVarType v1 of
                ty | isPointer ty -> LM_Bitcast
                ty | isInt ty     -> LM_Inttoptr

                ty -> panic $ "genCall: Expr is of bad type for function"
                              ++ " call! (" ++ showSDoc (ppr ty) ++ ")"

        (v2,s1) <- doExpr (pLift fty) $ Cast cast v1 (pLift fty)
        return (v2, stmts `snocOL` s1, top)

    CmmPrim mop _ -> cmmPrimOpFunctions mop >>= litCase

    where
        litCase name = do
            fn <- funLookup name
            case fn of
                Just ty'@(LMFunction sig) -> do
                    -- Function in module in right form
                    let fun = LMGlobalVar name ty' (funcLinkage sig)
                                    Nothing Nothing False
                    return (fun, nilOL, [])

                Just ty' -> do
                    -- label in module but not function pointer, convert
                    let fty@(LMFunction sig) = funTy name
                        fun = LMGlobalVar name (pLift ty') (funcLinkage sig)
                                    Nothing Nothing False
                    (v1, s1) <- doExpr (pLift fty)
                                    $ Cast LM_Bitcast fun (pLift fty)
                    return  (v1, unitOL s1, [])

                Nothing -> do
                    -- label not in module, create external reference
                    let fty@(LMFunction sig) = funTy name
                        fun = LMGlobalVar name fty (funcLinkage sig)
                                    Nothing Nothing False
                        top = [CmmData Data [([],[fty])]]
                    funInsert name fty
                    return (fun, nilOL, top)


-- | Conversion of call arguments.
arg_vars :: [HintedCmmActual]
         -> ([LlvmVar], LlvmStatements, [LlvmCmmDecl])
         -> LlvmM ([LlvmVar], LlvmStatements, [LlvmCmmDecl])

arg_vars [] (vars, stmts, tops)
  = return (vars, stmts, tops)

arg_vars (CmmHinted e AddrHint:rest) (vars, stmts, tops)
  = do (v1, stmts', top') <- exprToVar e
       let op = case getVarType v1 of
               ty | isPointer ty -> LM_Bitcast
               ty | isInt ty     -> LM_Inttoptr

               a  -> panic $ "genCall: Can't cast llvmType to i8*! ("
                           ++ showSDoc (ppr a) ++ ")"

       (v2, s1) <- doExpr i8Ptr $ Cast op v1 i8Ptr
       arg_vars rest (vars ++ [v2], stmts `appOL` stmts' `snocOL` s1,
                               tops ++ top')

arg_vars (CmmHinted e _:rest) (vars, stmts, tops)
  = do (v1, stmts', top') <- exprToVar e
       arg_vars rest (vars ++ [v1], stmts `appOL` stmts', tops ++ top')


-- | Cast a collection of LLVM variables to specific types.
castVars :: [(LlvmVar, LlvmType)]
         -> LlvmM ([LlvmVar], LlvmStatements)
castVars vars = do
                done <- mapM (uncurry castVar) vars
                let (vars', stmts) = unzip done
                return (vars', toOL stmts)

-- | Cast an LLVM variable to a specific type, panicing if it can't be done.
castVar :: LlvmVar -> LlvmType -> LlvmM (LlvmVar, LlvmStatement)
castVar v t | getVarType v == t
            = return (v, Nop)

            | otherwise
            = let op = case (getVarType v, t) of
                      (LMInt n, LMInt m)
                          -> if n < m then LM_Sext else LM_Trunc
                      (vt, _) | isFloat vt && isFloat t
                          -> if llvmWidthInBits vt < llvmWidthInBits t
                                then LM_Fpext else LM_Fptrunc
                      (vt, _) | isInt vt && isFloat t       -> LM_Sitofp
                      (vt, _) | isFloat vt && isInt t       -> LM_Fptosi
                      (vt, _) | isInt vt && isPointer t     -> LM_Inttoptr
                      (vt, _) | isPointer vt && isInt t     -> LM_Ptrtoint
                      (vt, _) | isPointer vt && isPointer t -> LM_Bitcast

                      (vt, _) -> panic $ "castVars: Can't cast this type ("
                                  ++ showSDoc (ppr vt) ++ ") to (" ++ showSDoc (ppr t) ++ ")"
              in doExpr t $ Cast op v t


-- | Decide what C function to use to implement a CallishMachOp
cmmPrimOpFunctions :: CallishMachOp -> LlvmM LMString
cmmPrimOpFunctions mop = do

  ver <- getLlvmVer
  let intrinTy1 = (if ver >= 28
                       then "p0i8.p0i8." else "") ++ showSDoc (ppr llvmWord)
      intrinTy2 = (if ver >= 28
                       then "p0i8." else "") ++ showSDoc (ppr llvmWord)
      unsupported = panic ("cmmPrimOpFunctions: " ++ show mop
                        ++ " not supported here")

  return $ case mop of
    MO_F32_Exp    -> fsLit "expf"
    MO_F32_Log    -> fsLit "logf"
    MO_F32_Sqrt   -> fsLit "llvm.sqrt.f32"
    MO_F32_Pwr    -> fsLit "llvm.pow.f32"

    MO_F32_Sin    -> fsLit "llvm.sin.f32"
    MO_F32_Cos    -> fsLit "llvm.cos.f32"
    MO_F32_Tan    -> fsLit "tanf"

    MO_F32_Asin   -> fsLit "asinf"
    MO_F32_Acos   -> fsLit "acosf"
    MO_F32_Atan   -> fsLit "atanf"

    MO_F32_Sinh   -> fsLit "sinhf"
    MO_F32_Cosh   -> fsLit "coshf"
    MO_F32_Tanh   -> fsLit "tanhf"

    MO_F64_Exp    -> fsLit "exp"
    MO_F64_Log    -> fsLit "log"
    MO_F64_Sqrt   -> fsLit "llvm.sqrt.f64"
    MO_F64_Pwr    -> fsLit "llvm.pow.f64"

    MO_F64_Sin    -> fsLit "llvm.sin.f64"
    MO_F64_Cos    -> fsLit "llvm.cos.f64"
    MO_F64_Tan    -> fsLit "tan"

    MO_F64_Asin   -> fsLit "asin"
    MO_F64_Acos   -> fsLit "acos"
    MO_F64_Atan   -> fsLit "atan"

    MO_F64_Sinh   -> fsLit "sinh"
    MO_F64_Cosh   -> fsLit "cosh"
    MO_F64_Tanh   -> fsLit "tanh"

    MO_CycleCount -> fsLit "llvm.readcyclecounter"

    MO_Memcpy     -> fsLit $ "llvm.memcpy."  ++ intrinTy1
    MO_Memmove    -> fsLit $ "llvm.memmove." ++ intrinTy1
    MO_Memset     -> fsLit $ "llvm.memset."  ++ intrinTy2

    (MO_PopCnt w) -> fsLit $ "llvm.ctpop."  ++ showSDoc (ppr $ widthToLlvmInt w)

    MO_S_QuotRem {} -> unsupported
    MO_U_QuotRem {} -> unsupported
    MO_Add2 {}      -> unsupported
    MO_U_Mul2 {}    -> unsupported
    MO_WriteBarrier -> unsupported
    MO_Touch        -> unsupported

-- | Tail function calls
genJump :: CmmExpr -> Maybe [GlobalReg] -> LlvmM StmtData

-- Call to known function
genJump (CmmLit (CmmLabel lbl)) live = do
    (vf, stmts, top) <- getHsFunc lbl
    (stgRegs, stgStmts) <- funEpilogue live
    let s1  = Expr $ Call TailCall vf stgRegs llvmStdFunAttrs
    let s2  = Return Nothing
    return (stmts `appOL` stgStmts `snocOL` s1 `snocOL` s2, top)


-- Call to unknown function / address
genJump expr live = do
    let fty = llvmFunTy
    (vf, stmts, top) <- exprToVar expr

    let cast = case getVarType vf of
         ty | isPointer ty -> LM_Bitcast
         ty | isInt ty     -> LM_Inttoptr

         ty -> panic $ "genJump: Expr is of bad type for function call! ("
                     ++ showSDoc (ppr ty) ++ ")"

    (v1, s1) <- doExpr (pLift fty) $ Cast cast vf (pLift fty)
    (stgRegs, stgStmts) <- funEpilogue live
    let s2 = Expr $ Call TailCall v1 stgRegs llvmStdFunAttrs
    let s3 = Return Nothing
    return (stmts `snocOL` s1 `appOL` stgStmts `snocOL` s2 `snocOL` s3,
            top)


-- | CmmAssign operation
--
-- We use stack allocated variables for CmmReg. The optimiser will replace
-- these with registers when possible.
genAssign :: CmmReg -> CmmExpr -> LlvmM StmtData
genAssign reg val = do
    vreg <- getCmmReg reg
    (vval, stmts2, top2) <- exprToVar val
    let stmts = stmts2

    let ty = (pLower . getVarType) vreg
    case isPointer ty && getVarType vval == llvmWord of
         -- Some registers are pointer types, so need to cast value to pointer
         True -> do
             (v, s1) <- doExpr ty $ Cast LM_Inttoptr vval ty
             let s2 = Store v vreg
             return (stmts `snocOL` s1 `snocOL` s2, top2)

         False -> do
             let s1 = Store vval vreg
             return (stmts `snocOL` s1, top2)


-- | CmmStore operation
genStore :: CmmExpr -> CmmExpr -> LlvmM StmtData

-- First we try to detect a few common cases and produce better code for
-- these then the default case. We are mostly trying to detect Cmm code
-- like I32[Sp + n] and use 'getelementptr' operations instead of the
-- generic case that uses casts and pointer arithmetic
genStore addr@(CmmReg (CmmGlobal r)) val
    = genStore_fast addr r 0 val

genStore addr@(CmmRegOff (CmmGlobal r) n) val
    = genStore_fast addr r n val

genStore addr@(CmmMachOp (MO_Add _) [
                            (CmmReg (CmmGlobal r)),
                            (CmmLit (CmmInt n _))])
                val
    = genStore_fast addr r (fromInteger n) val

genStore addr@(CmmMachOp (MO_Sub _) [
                            (CmmReg (CmmGlobal r)),
                            (CmmLit (CmmInt n _))])
                val
    = genStore_fast addr r (negate $ fromInteger n) val

-- generic case
genStore addr val
    = do other <- getTBAAMeta otherN
         genStore_slow addr val other

-- | CmmStore operation
-- This is a special case for storing to a global register pointer
-- offset such as I32[Sp+8].
genStore_fast :: CmmExpr -> GlobalReg -> Int -> CmmExpr
              -> LlvmM StmtData
genStore_fast addr r n val
  = do (gv, grt, s1) <- getCmmRegVal (CmmGlobal r)
       meta          <- getTBAARegMeta r
       let (ix,rem) = n `divMod` ((llvmWidthInBits . pLower) grt  `div` 8)
       case isPointer grt && rem == 0 of
            True -> do
                (vval,  stmts, top) <- exprToVar val
                (ptr, s2) <- doExpr grt $ GetElemPtr True gv [toI32 ix]
                -- We might need a different pointer type, so check
                case pLower grt == getVarType vval of
                     -- were fine
                     True  -> do
                         let s3 = MetaStmt meta $ Store vval ptr
                         return (stmts `appOL` s1 `snocOL` s2
                                 `snocOL` s3, top)

                     -- cast to pointer type needed
                     False -> do
                         let ty = (pLift . getVarType) vval
                         (ptr', s3) <- doExpr ty $ Cast LM_Bitcast ptr ty
                         let s4 = MetaStmt meta $ Store vval ptr'
                         return (stmts `appOL` s1 `snocOL` s2
                                 `snocOL` s3 `snocOL` s4, top)

            -- If its a bit type then we use the slow method since
            -- we can't avoid casting anyway.
            False -> genStore_slow addr val meta


-- | CmmStore operation
-- Generic case. Uses casts and pointer arithmetic if needed.
genStore_slow :: CmmExpr -> CmmExpr -> [MetaData] -> LlvmM StmtData
genStore_slow addr val meta = do
    (vaddr, stmts1, top1) <- exprToVar addr
    (vval,  stmts2, top2) <- exprToVar val

    let stmts = stmts1 `appOL` stmts2
    case getVarType vaddr of
        -- sometimes we need to cast an int to a pointer before storing
        LMPointer ty@(LMPointer _) | getVarType vval == llvmWord -> do
            (v, s1) <- doExpr ty $ Cast LM_Inttoptr vval ty
            let s2 = MetaStmt meta $ Store v vaddr
            return (stmts `snocOL` s1 `snocOL` s2, top1 ++ top2)

        LMPointer _ -> do
            let s1 = MetaStmt meta $ Store vval vaddr
            return (stmts `snocOL` s1, top1 ++ top2)

        i@(LMInt _) | i == llvmWord -> do
            let vty = pLift $ getVarType vval
            (vptr, s1) <- doExpr vty $ Cast LM_Inttoptr vaddr vty
            let s2 = MetaStmt meta $ Store vval vptr
            return (stmts `snocOL` s1 `snocOL` s2, top1 ++ top2)

        other -> do
            platform <- getLlvmPlatform
            pprPanic "genStore: ptr not right type!"
                    (PprCmm.pprExpr platform addr <+> text (
                        "Size of Ptr: " ++ show llvmPtrBits ++
                        ", Size of var: " ++ show (llvmWidthInBits other) ++
                        ", Var: " ++ showSDoc (ppr vaddr)))


-- | Unconditional branch
genBranch :: BlockId -> LlvmM StmtData
genBranch id =
    let label = blockIdToLlvm id
    in return (unitOL $ Branch label, [])


-- | Conditional branch
genCondBranch :: CmmExpr -> BlockId -> LlvmM StmtData
genCondBranch cond idT = do
    idF <- runUs $ getUniqueUs
    let labelT = blockIdToLlvm idT
    let labelF = LMLocalVar idF LMLabel
    (vc, stmts, top) <- exprToVarOpt i1Option cond
    if getVarType vc == i1
        then do
            let s1 = BranchIf vc labelT labelF
            let s2 = MkLabel idF
            return $ (stmts `snocOL` s1 `snocOL` s2, top)
        else
            panic $ "genCondBranch: Cond expr not bool! (" ++ showSDoc (ppr vc) ++ ")"


-- | Switch branch
--
-- N.B. We remove Nothing's from the list of branches, as they are 'undefined'.
-- However, they may be defined one day, so we better document this behaviour.
genSwitch :: CmmExpr -> [Maybe BlockId] -> LlvmM StmtData
genSwitch cond maybe_ids = do
    (vc, stmts, top) <- exprToVar cond
    let ty = getVarType vc

    let pairs = [ (ix, id) | (ix,Just id) <- zip [0..] maybe_ids ]
    let labels = map (\(ix, b) -> (mkIntLit ty ix, blockIdToLlvm b)) pairs
    -- out of range is undefied, so lets just branch to first label
    let (_, defLbl) = head labels

    let s1 = Switch vc defLbl labels
    return $ (stmts `snocOL` s1, top)


-- -----------------------------------------------------------------------------
-- * CmmExpr code generation
--

-- | An expression conversion return data:
--   * LlvmVar: The var holding the result of the expression
--   * LlvmStatements: Any statements needed to evaluate the expression
--   * LlvmCmmDecl: Any global data needed for this expression
type ExprData = (LlvmVar, LlvmStatements, [LlvmCmmDecl])

-- | Values which can be passed to 'exprToVar' to configure its
-- behaviour in certain circumstances.
data EOption = EOption {
        -- | The expected LlvmType for the returned variable.
        --
        -- Currently just used for determining if a comparison should return
        -- a boolean (i1) or a int (i32/i64).
        eoExpectedType :: Maybe LlvmType
  }

i1Option :: EOption
i1Option = EOption (Just i1)

wordOption :: EOption
wordOption = EOption (Just llvmWord)


-- | Convert a CmmExpr to a list of LlvmStatements with the result of the
-- expression being stored in the returned LlvmVar.
exprToVar :: CmmExpr -> LlvmM ExprData
exprToVar = exprToVarOpt wordOption

exprToVarOpt :: EOption -> CmmExpr -> LlvmM ExprData
exprToVarOpt opt e = case e of

    CmmLit lit
        -> genLit lit

    CmmLoad e' ty
        -> genLoad e' ty

    -- Cmmreg in expression is the value, so must load. If you want actual
    -- reg pointer, call getCmmReg directly.
    CmmReg r -> do
        (v1, ty, s1) <- getCmmRegVal r
        case isPointer ty of
             True  -> do
                 -- Cmm wants the value, so pointer types must be cast to ints
                 (v2, s2) <- doExpr llvmWord $ Cast LM_Ptrtoint v1 llvmWord
                 return (v2, s1 `snocOL` s2, [])

             False -> return (v1, s1, [])

    CmmMachOp op exprs
        -> genMachOp opt op exprs

    CmmRegOff r i
        -> exprToVar $ expandCmmReg (r, i)

    CmmStackSlot _ _
        -> panic "exprToVar: CmmStackSlot not supported!"


-- | Handle CmmMachOp expressions
genMachOp :: EOption -> MachOp -> [CmmExpr] -> LlvmM ExprData

-- Unary Machop
genMachOp _ op [x] = case op of

    MO_Not w ->
        let all1 = mkIntLit (widthToLlvmInt w) (-1)
        in negate (widthToLlvmInt w) all1 LM_MO_Xor

    MO_S_Neg w ->
        let all0 = mkIntLit (widthToLlvmInt w) 0
        in negate (widthToLlvmInt w) all0 LM_MO_Sub

    MO_F_Neg w ->
        let all0 = LMLitVar $ LMFloatLit (-0) (widthToLlvmFloat w)
        in negate (widthToLlvmFloat w) all0 LM_MO_FSub

    MO_SF_Conv _ w -> fiConv (widthToLlvmFloat w) LM_Sitofp
    MO_FS_Conv _ w -> fiConv (widthToLlvmInt w) LM_Fptosi

    MO_SS_Conv from to
        -> sameConv from (widthToLlvmInt to) LM_Trunc LM_Sext

    MO_UU_Conv from to
        -> sameConv from (widthToLlvmInt to) LM_Trunc LM_Zext

    MO_FF_Conv from to
        -> sameConv from (widthToLlvmFloat to) LM_Fptrunc LM_Fpext

    -- Handle unsupported cases explicitly so we get a warning
    -- of missing case when new MachOps added
    MO_Add _          -> panicOp
    MO_Mul _          -> panicOp
    MO_Sub _          -> panicOp
    MO_S_MulMayOflo _ -> panicOp
    MO_S_Quot _       -> panicOp
    MO_S_Rem _        -> panicOp
    MO_U_MulMayOflo _ -> panicOp
    MO_U_Quot _       -> panicOp
    MO_U_Rem _        -> panicOp

    MO_Eq  _          -> panicOp
    MO_Ne  _          -> panicOp
    MO_S_Ge _         -> panicOp
    MO_S_Gt _         -> panicOp
    MO_S_Le _         -> panicOp
    MO_S_Lt _         -> panicOp
    MO_U_Ge _         -> panicOp
    MO_U_Gt _         -> panicOp
    MO_U_Le _         -> panicOp
    MO_U_Lt _         -> panicOp

    MO_F_Add        _ -> panicOp
    MO_F_Sub        _ -> panicOp
    MO_F_Mul        _ -> panicOp
    MO_F_Quot       _ -> panicOp
    MO_F_Eq         _ -> panicOp
    MO_F_Ne         _ -> panicOp
    MO_F_Ge         _ -> panicOp
    MO_F_Gt         _ -> panicOp
    MO_F_Le         _ -> panicOp
    MO_F_Lt         _ -> panicOp

    MO_And          _ -> panicOp
    MO_Or           _ -> panicOp
    MO_Xor          _ -> panicOp
    MO_Shl          _ -> panicOp
    MO_U_Shr        _ -> panicOp
    MO_S_Shr        _ -> panicOp

    where
        negate ty v2 negOp = do
            (vx, stmts, top) <- exprToVar x
            (v1, s1) <- doExpr ty $ LlvmOp negOp v2 vx
            return (v1, stmts `snocOL` s1, top)

        fiConv ty convOp = do
            (vx, stmts, top) <- exprToVar x
            (v1, s1) <- doExpr ty $ Cast convOp vx ty
            return (v1, stmts `snocOL` s1, top)

        sameConv from ty reduce expand = do
            x'@(vx, stmts, top) <- exprToVar x
            let sameConv' op = do
                (v1, s1) <- doExpr ty $ Cast op vx ty
                return (v1, stmts `snocOL` s1, top)
            let toWidth = llvmWidthInBits ty
            -- LLVM doesn't like trying to convert to same width, so
            -- need to check for that as we do get Cmm code doing it.
            case widthInBits from  of
                 w | w < toWidth -> sameConv' expand
                 w | w > toWidth -> sameConv' reduce
                 _w              -> return x'
        
        panicOp = panic $ "LLVM.CodeGen.genMachOp: non unary op encourntered"
                       ++ "with one argument! (" ++ show op ++ ")"

-- Handle GlobalRegs pointers
genMachOp opt o@(MO_Add _) e@[(CmmReg (CmmGlobal r)), (CmmLit (CmmInt n _))]
    = genMachOp_fast opt o r (fromInteger n) e

genMachOp opt o@(MO_Sub _) e@[(CmmReg (CmmGlobal r)), (CmmLit (CmmInt n _))]
    = genMachOp_fast opt o r (negate . fromInteger $ n) e

-- Generic case
genMachOp opt op e = genMachOp_slow opt op e


-- | Handle CmmMachOp expressions
-- This is a specialised method that handles Global register manipulations like
-- 'Sp - 16', using the getelementptr instruction.
genMachOp_fast :: EOption -> MachOp -> GlobalReg -> Int -> [CmmExpr]
               -> LlvmM ExprData
genMachOp_fast opt op r n e
  = do (gv, grt, s1) <- getCmmRegVal (CmmGlobal r)
       let (ix,rem) = n `divMod` ((llvmWidthInBits . pLower) grt  `div` 8)
       case isPointer grt && rem == 0 of
            True -> do
                (ptr, s2) <- doExpr grt $ GetElemPtr True gv [toI32 ix]
                (var, s3) <- doExpr llvmWord $ Cast LM_Ptrtoint ptr llvmWord
                return (var, s1 `snocOL` s2 `snocOL` s3, [])

            False -> genMachOp_slow opt op e


-- | Handle CmmMachOp expressions
-- This handles all the cases not handle by the specialised genMachOp_fast.
genMachOp_slow :: EOption -> MachOp -> [CmmExpr] -> LlvmM ExprData

-- Binary MachOp
genMachOp_slow opt op [x, y] = case op of

    MO_Eq _   -> genBinComp opt LM_CMP_Eq
    MO_Ne _   -> genBinComp opt LM_CMP_Ne

    MO_S_Gt _ -> genBinComp opt LM_CMP_Sgt
    MO_S_Ge _ -> genBinComp opt LM_CMP_Sge
    MO_S_Lt _ -> genBinComp opt LM_CMP_Slt
    MO_S_Le _ -> genBinComp opt LM_CMP_Sle

    MO_U_Gt _ -> genBinComp opt LM_CMP_Ugt
    MO_U_Ge _ -> genBinComp opt LM_CMP_Uge
    MO_U_Lt _ -> genBinComp opt LM_CMP_Ult
    MO_U_Le _ -> genBinComp opt LM_CMP_Ule

    MO_Add _ -> genBinMach LM_MO_Add
    MO_Sub _ -> genBinMach LM_MO_Sub
    MO_Mul _ -> genBinMach LM_MO_Mul

    MO_U_MulMayOflo _ -> panic "genMachOp: MO_U_MulMayOflo unsupported!"

    MO_S_MulMayOflo w -> isSMulOK w x y

    MO_S_Quot _ -> genBinMach LM_MO_SDiv
    MO_S_Rem  _ -> genBinMach LM_MO_SRem

    MO_U_Quot _ -> genBinMach LM_MO_UDiv
    MO_U_Rem  _ -> genBinMach LM_MO_URem

    MO_F_Eq _ -> genBinComp opt LM_CMP_Feq
    MO_F_Ne _ -> genBinComp opt LM_CMP_Fne
    MO_F_Gt _ -> genBinComp opt LM_CMP_Fgt
    MO_F_Ge _ -> genBinComp opt LM_CMP_Fge
    MO_F_Lt _ -> genBinComp opt LM_CMP_Flt
    MO_F_Le _ -> genBinComp opt LM_CMP_Fle

    MO_F_Add  _ -> genBinMach LM_MO_FAdd
    MO_F_Sub  _ -> genBinMach LM_MO_FSub
    MO_F_Mul  _ -> genBinMach LM_MO_FMul
    MO_F_Quot _ -> genBinMach LM_MO_FDiv

    MO_And _   -> genBinMach LM_MO_And
    MO_Or  _   -> genBinMach LM_MO_Or
    MO_Xor _   -> genBinMach LM_MO_Xor
    MO_Shl _   -> genBinMach LM_MO_Shl
    MO_U_Shr _ -> genBinMach LM_MO_LShr
    MO_S_Shr _ -> genBinMach LM_MO_AShr

    MO_Not _       -> panicOp
    MO_S_Neg _     -> panicOp
    MO_F_Neg _     -> panicOp

    MO_SF_Conv _ _ -> panicOp
    MO_FS_Conv _ _ -> panicOp
    MO_SS_Conv _ _ -> panicOp
    MO_UU_Conv _ _ -> panicOp
    MO_FF_Conv _ _ -> panicOp

    where
        binLlvmOp ty binOp = do
            (vx, stmts1, top1) <- exprToVar x
            (vy, stmts2, top2) <- exprToVar y
            if getVarType vx == getVarType vy
                then do
                    (v1, s1) <- doExpr (ty vx) $ binOp vx vy
                    return (v1, stmts1 `appOL` stmts2 `snocOL` s1,
                            top1 ++ top2)

                else do
                    -- Error. Continue anyway so we can debug the generated ll file.
                    platform <- getLlvmPlatform
                    let cmmToStr = lines . showSDoc . PprCmm.pprExpr platform
                    let dx = Comment $ map fsLit $ cmmToStr x
                    let dy = Comment $ map fsLit $ cmmToStr y
                    (v1, s1) <- doExpr (ty vx) $ binOp vx vy
                    let allStmts = stmts1 `appOL` stmts2 `snocOL` dx
                                    `snocOL` dy `snocOL` s1
                    return (v1, allStmts, top1 ++ top2)

        -- | Need to use EOption here as Cmm expects word size results from
        -- comparisons while LLVM return i1. Need to extend to llvmWord type
        -- if expected
        genBinComp opt cmp = do
            ed@(v1, stmts, top) <- binLlvmOp (\_ -> i1) $ Compare cmp

            if getVarType v1 == i1
                then
                    case eoExpectedType opt of
                         Nothing ->
                             return ed

                         Just t | t == i1 ->
                                    return ed

                                | isInt t -> do
                                    (v2, s1) <- doExpr t $ Cast LM_Zext v1 t
                                    return (v2, stmts `snocOL` s1, top)

                                | otherwise ->
                                    panic $ "genBinComp: Can't case i1 compare"
                                        ++ "res to non int type " ++ showSDoc (ppr t)
                else
                    panic $ "genBinComp: Compare returned type other then i1! "
                        ++ (showSDoc $ ppr $ getVarType v1)

        genBinMach op = binLlvmOp getVarType (LlvmOp op)

        -- | Detect if overflow will occur in signed multiply of the two
        -- CmmExpr's. This is the LLVM assembly equivalent of the NCG
        -- implementation. Its much longer due to type information/safety.
        -- This should actually compile to only about 3 asm instructions.
        isSMulOK :: Width -> CmmExpr -> CmmExpr -> LlvmM ExprData
        isSMulOK _ x y = do
            (vx, stmts1, top1) <- exprToVar x
            (vy, stmts2, top2) <- exprToVar y

            let word  = getVarType vx
            let word2 = LMInt $ 2 * (llvmWidthInBits $ getVarType vx)
            let shift = llvmWidthInBits word
            let shift1 = toIWord (shift - 1)
            let shift2 = toIWord shift

            if isInt word
                then do
                    (x1, s1)     <- doExpr word2 $ Cast LM_Sext vx word2
                    (y1, s2)     <- doExpr word2 $ Cast LM_Sext vy word2
                    (r1, s3)     <- doExpr word2 $ LlvmOp LM_MO_Mul x1 y1
                    (rlow1, s4)  <- doExpr word $ Cast LM_Trunc r1 word
                    (rlow2, s5)  <- doExpr word $ LlvmOp LM_MO_AShr rlow1 shift1
                    (rhigh1, s6) <- doExpr word2 $ LlvmOp LM_MO_AShr r1 shift2
                    (rhigh2, s7) <- doExpr word $ Cast LM_Trunc rhigh1 word
                    (dst, s8)    <- doExpr word $ LlvmOp LM_MO_Sub rlow2 rhigh2
                    let stmts = (unitOL s1) `snocOL` s2 `snocOL` s3 `snocOL` s4
                            `snocOL` s5 `snocOL` s6 `snocOL` s7 `snocOL` s8
                    return (dst, stmts1 `appOL` stmts2 `appOL` stmts,
                        top1 ++ top2)

                else
                    panic $ "isSMulOK: Not bit type! (" ++ showSDoc (ppr word) ++ ")"

        panicOp = panic $ "LLVM.CodeGen.genMachOp_slow: unary op encourntered"
                       ++ "with two arguments! (" ++ show op ++ ")"

-- More then two expression, invalid!
genMachOp_slow _ _ _ = panic "genMachOp: More then 2 expressions in MachOp!"


-- | Handle CmmLoad expression.
genLoad :: CmmExpr -> CmmType -> LlvmM ExprData

-- First we try to detect a few common cases and produce better code for
-- these then the default case. We are mostly trying to detect Cmm code
-- like I32[Sp + n] and use 'getelementptr' operations instead of the
-- generic case that uses casts and pointer arithmetic
genLoad e@(CmmReg (CmmGlobal r)) ty
    = genLoad_fast e r 0 ty

genLoad e@(CmmRegOff (CmmGlobal r) n) ty
    = genLoad_fast e r n ty

genLoad e@(CmmMachOp (MO_Add _) [
                            (CmmReg (CmmGlobal r)),
                            (CmmLit (CmmInt n _))])
                ty
    = genLoad_fast e r (fromInteger n) ty

genLoad e@(CmmMachOp (MO_Sub _) [
                            (CmmReg (CmmGlobal r)),
                            (CmmLit (CmmInt n _))])
                ty
    = genLoad_fast e r (negate $ fromInteger n) ty

-- generic case
genLoad e ty
    = do other <- getTBAAMeta otherN
         genLoad_slow e ty other

-- | Handle CmmLoad expression.
-- This is a special case for loading from a global register pointer
-- offset such as I32[Sp+8].
genLoad_fast :: CmmExpr -> GlobalReg -> Int -> CmmType
                -> LlvmM ExprData
genLoad_fast e r n ty = do
    (gv, grt, s1) <- getCmmRegVal (CmmGlobal r)
    meta          <- getTBAARegMeta r
    let ty'      = cmmToLlvmType ty
        (ix,rem) = n `divMod` ((llvmWidthInBits . pLower) grt  `div` 8)
    case isPointer grt && rem == 0 of
            True  -> do
                (ptr, s2) <- doExpr grt $ GetElemPtr True gv [toI32 ix]
                -- We might need a different pointer type, so check
                case grt == ty' of
                     -- were fine
                     True -> do
                         (var, s3) <- doExpr ty' (MetaExpr meta $ Load ptr)
                         return (var, s1 `snocOL` s2 `snocOL` s3,
                                     [])

                     -- cast to pointer type needed
                     False -> do
                         let pty = pLift ty'
                         (ptr', s3) <- doExpr pty $ Cast LM_Bitcast ptr pty
                         (var, s4) <- doExpr ty' (MetaExpr meta $ Load ptr')
                         return (var, s1 `snocOL` s2 `snocOL` s3
                                    `snocOL` s4, [])

            -- If its a bit type then we use the slow method since
            -- we can't avoid casting anyway.
            False -> genLoad_slow e ty meta


-- | Handle Cmm load expression.
-- Generic case. Uses casts and pointer arithmetic if needed.
genLoad_slow :: CmmExpr -> CmmType -> [MetaData] -> LlvmM ExprData
genLoad_slow e ty meta = do
    (iptr, stmts, tops) <- exprToVar e
    case getVarType iptr of
         LMPointer _ -> do
                    (dvar, load) <- doExpr (cmmToLlvmType ty)
                                           (MetaExpr meta $ Load iptr)
                    return (dvar, stmts `snocOL` load, tops)

         i@(LMInt _) | i == llvmWord -> do
                    let pty = LMPointer $ cmmToLlvmType ty
                    (ptr, cast)  <- doExpr pty $ Cast LM_Inttoptr iptr pty
                    (dvar, load) <- doExpr (cmmToLlvmType ty)
                                           (MetaExpr meta $ Load ptr)
                    return (dvar, stmts `snocOL` cast `snocOL` load, tops)

         other -> do
                  platform <- getLlvmPlatform
                  pprPanic "exprToVar: CmmLoad expression is not right type!"
                        (PprCmm.pprExpr platform e <+> text (
                            "Size of Ptr: " ++ show llvmPtrBits ++
                            ", Size of var: " ++ show (llvmWidthInBits other) ++
                            ", Var: " ++ showSDoc (ppr iptr)))


-- | Handle CmmReg expression. This will return a pointer to the stack
-- location of the register. Throws an error if it isn't allocated on
-- the stack.
getCmmReg :: CmmReg -> LlvmM LlvmVar
getCmmReg (CmmLocal (LocalReg un _))
  = do exists <- varLookup un
       case exists of
         Just ety -> return (LMLocalVar un $ pLift ety)
         Nothing  -> fail $ "getCmmReg: Cmm register " ++ showSDoc (ppr un) ++ " was not allocated!"
           -- This should never happen, as every local variable should
           -- have been assigned a value at some point, triggering
           -- "funPrologue" to allocate it on the stack.

getCmmReg (CmmGlobal g)
  = do onStack <- checkStackReg g
       if onStack
         then return (lmGlobalRegVar g)
         else fail $ "getCmmReg: Cmm register " ++ showSDoc (ppr g) ++ " not stack-allocated!"

-- | Return the value of a given register, as well as its type. Might
-- need to be load from stack.
getCmmRegVal :: CmmReg -> LlvmM (LlvmVar, LlvmType, LlvmStatements)
getCmmRegVal reg =
  case reg of
    CmmGlobal g -> do
      onStack <- checkStackReg g
      if onStack then loadFromStack else do
        let r = lmGlobalRegArg g
        return (r, getVarType r, nilOL)
    _ -> loadFromStack
 where loadFromStack = do
         ptr <- getCmmReg reg
         let ty = pLower $ getVarType ptr
         (v, s) <- doExpr ty (Load ptr)
         return (v, ty, unitOL s)

-- | Allocate a local CmmReg on the stack
allocReg :: CmmReg -> (LlvmVar, LlvmStatements)
allocReg (CmmLocal (LocalReg un ty))
  = let ty' = cmmToLlvmType ty
        var = LMLocalVar un (LMPointer ty')
        alc = Alloca ty' 1
    in (var, unitOL $ Assignment var alc)

allocReg _ = panic $ "allocReg: Global reg encountered! Global registers should"
                    ++ " have been handled elsewhere!"


-- | Generate code for a literal
genLit :: CmmLit -> LlvmM ExprData
genLit (CmmInt i w)
  = return (mkIntLit (LMInt $ widthInBits w) i, nilOL, [])

genLit (CmmFloat r w)
  = return (LMLitVar $ LMFloatLit (fromRational r) (widthToLlvmFloat w),
              nilOL, [])

genLit cmm@(CmmLabel l)
  = do label <- strCLabel_llvm l
       ty <- funLookup label
       let lmty = cmmToLlvmType $ cmmLitType cmm
       case ty of
            -- Make generic external label definition and then pointer to it
            Nothing -> do
                let glob@(LMGlobal var _) = genStringLabelRef label
                let ldata = [CmmData Data [([glob], [])]]
                funInsert label (pLower $ getVarType var)
                (v1, s1) <- doExpr lmty $ Cast LM_Ptrtoint var llvmWord
                return (v1, unitOL s1, ldata)

            -- Referenced data exists in this module, retrieve type and make
            -- pointer to it.
            Just ty' -> do
                let var = LMGlobalVar label (LMPointer ty')
                            ExternallyVisible Nothing Nothing False
                (v1, s1) <- doExpr lmty $ Cast LM_Ptrtoint var llvmWord
                return (v1, unitOL s1, [])

genLit (CmmLabelOff label off) = do
    (vlbl, stmts, stat) <- genLit (CmmLabel label)
    let voff = toIWord off
    (v1, s1) <- doExpr (getVarType vlbl) $ LlvmOp LM_MO_Add vlbl voff
    return (v1, stmts `snocOL` s1, stat)

genLit (CmmLabelDiffOff l1 l2 off) = do
    (vl1, stmts1, stat1) <- genLit (CmmLabel l1)
    (vl2, stmts2, stat2) <- genLit (CmmLabel l2)
    let voff = toIWord off
    let ty1 = getVarType vl1
    let ty2 = getVarType vl2
    if (isInt ty1) && (isInt ty2)
       && (llvmWidthInBits ty1 == llvmWidthInBits ty2)

       then do
            (v1, s1) <- doExpr (getVarType vl1) $ LlvmOp LM_MO_Sub vl1 vl2
            (v2, s2) <- doExpr (getVarType v1 ) $ LlvmOp LM_MO_Add v1 voff
            return (v2, stmts1 `appOL` stmts2 `snocOL` s1 `snocOL` s2,
                        stat1 ++ stat2)

        else
            panic "genLit: CmmLabelDiffOff encountered with different label ty!"

genLit (CmmBlock b)
  = genLit (CmmLabel $ infoTblLbl b)

genLit CmmHighStackMark
  = panic "genStaticLit - CmmHighStackMark unsupported!"


-- -----------------------------------------------------------------------------
-- * Misc
--

-- | Find CmmRegs that get assigned and allocate them on the stack
--
-- Any register that gets written needs to be allcoated on the
-- stack. This avoids having to map a CmmReg to an equivalent SSA form
-- and avoids having to deal with Phi node insertion.  This is also
-- the approach recommended by LLVM developers.
--
-- On the other hand, this is unecessarily verbose if the register in
-- question is never written. Therefore we skip it where we can to
-- save a few lines in the output and hopefully speed compilation up a
-- bit.
funPrologue :: [CmmBasicBlock] -> LMMetaInt -> LlvmM StmtData
funPrologue cmmBlocks scopeId = do

  let getAssignedRegs (CmmAssign reg _)  = [reg]
      -- Calls will trash all registers. Unfortunately, this needs them to
      -- be stack-allocated in the first place.
      getAssignedRegs (CmmCall t rs _ _) = map CmmGlobal trashRegs ++
                                            map formalToReg rs ++
                                            getPrimRegs t
      getAssignedRegs _                  = []
      getPrimRegs (CmmPrim _ (Just ss))  = concatMap getAssignedRegs ss
      getPrimRegs _                      = []
      formalToReg (CmmHinted r _)        = CmmLocal r
      getRegsBlock (BasicBlock _ xs)     = concatMap getAssignedRegs xs
      assignedRegs = nub $ concatMap getRegsBlock cmmBlocks

  stmtss <- flip mapM assignedRegs $ \reg ->
    case reg of
      CmmLocal (LocalReg un _) -> do
        let (newv, stmts) = allocReg reg
        varInsert un (pLower $ getVarType newv)
        return stmts
      CmmGlobal r -> do
        let reg   = lmGlobalRegVar r
            arg   = lmGlobalRegArg r
            alloc = Assignment reg $ Alloca (pLower $ getVarType reg) 1
        markStackReg r
        return $ toOL [alloc, Store arg reg]

  (declStmts, tops) <- declareRegister (CmmGlobal BaseReg) (fsLit "BaseReg") scopeId

  return (concatOL stmtss `appOL` declStmts, tops)


-- | Declares the value of a register as a variable in debugging data
declareRegister :: CmmReg -> LMString -> LMMetaInt -> LlvmM StmtData
declareRegister reg rname scopeId = do

  -- Get instrinct functions
  (declareFn, tops1) <- declareInstrinct (fsLit "llvm.dbg.declare") LMVoid [LMMetaType, LMMetaType]
  (valueFn, tops2) <- declareInstrinct (fsLit "llvm.dbg.value") LMVoid [LMMetaType, i64, LMMetaType]

  -- Check whether register is on stack or as value. Declare
  -- accordingly.
  onStack <- checkStackReg BaseReg
  stmts <- case onStack of
    True -> do
      rvar <- getCmmReg reg
      varMeta <- genVariableMeta rname (pLower $ getVarType rvar) scopeId
      let pars = map LMLitVar [ LMMeta [rvar], varMeta ]
      return $ unitOL $ Expr $ Call StdCall declareFn pars []
    False -> do
      (rvar, ty, ss) <- getCmmRegVal reg
      varMeta <- genVariableMeta rname ty scopeId
      let pars = map LMLitVar [ LMMeta [rvar], LMIntLit 0 i64, varMeta ]
      return $ ss `snocOL` (Expr $ Call StdCall valueFn pars [])

  return (stmts, tops1 ++ tops2)

-- | Function epilogue. Load STG variables to use as argument for call.
-- STG Liveness optimisation done here.
funEpilogue :: Maybe [GlobalReg] -> LlvmM ([LlvmVar], LlvmStatements)
funEpilogue live = do

    -- Have information and liveness optimisation is enabled?
    doRegLiveness <- getDynFlag (dopt Opt_RegLiveness)
    let liveRegs = if doRegLiveness then fmap (alwaysLive ++) live else Nothing

    -- Set to value or "undef" depending on whether the register is
    -- actually live
    let loadExpr r = do
          (v, _, s) <- getCmmRegVal (CmmGlobal r)
          return (v, s)
        loadUndef r = do
          let ty = (pLower . getVarType $ lmGlobalRegVar r)
          return (LMLitVar $ LMUndefLit ty, unitOL Nop)
    loads <- flip mapM activeStgRegs $ \r -> case liveRegs of
      Nothing               -> loadExpr r
      Just rs | r `elem` rs -> loadExpr r
              | otherwise   -> loadUndef r

    let (vars, stmts) = unzip loads
    return (vars, concatOL stmts)


-- | A serries of statements to trash all the STG registers.
--
-- In LLVM we pass the STG registers around everywhere in function calls.
-- So this means LLVM considers them live across the entire function, when
-- in reality they usually aren't. For Caller save registers across C calls
-- the saving and restoring of them is done by the Cmm code generator,
-- using Cmm local vars. So to stop LLVM saving them as well (and saving
-- all of them since it thinks they're always live, we trash them just
-- before the call by assigning the 'undef' value to them. The ones we
-- need are restored from the Cmm local var and the ones we don't need
-- are fine to be trashed.
trashStmts :: LlvmM (LlvmStatements)
trashStmts = fmap toOL $ mapM trashReg trashRegs
    where trashReg r = do
            reg <- getCmmReg (CmmGlobal r)
            let ty    = (pLower . getVarType) reg
            return $ Store (LMLitVar $ LMUndefLit ty) reg

trashRegs :: [GlobalReg]
trashRegs = filter callerSaves activeStgRegs

-- | Get a function pointer to the CLabel specified.
--
-- This is for Haskell functions, function type is assumed, so doesn't work
-- with foreign functions.
getHsFunc :: CLabel -> LlvmM ExprData
getHsFunc lbl
  = do fn <- strCLabel_llvm lbl
       ty <- funLookup fn
       case ty of
        -- Function in module in right form
        Just ty'@(LMFunction sig) -> do
            let fun = LMGlobalVar fn ty' (funcLinkage sig) Nothing Nothing False
            return (fun, nilOL, [])

        -- label in module but not function pointer, convert
        Just ty' -> do
            let fun = LMGlobalVar fn (pLift ty') ExternallyVisible
                            Nothing Nothing False
            (v1, s1) <- doExpr (pLift llvmFunTy) $
                            Cast LM_Bitcast fun (pLift llvmFunTy)
            return (v1, unitOL s1, [])

        -- label not in module, create external reference
        Nothing  -> do
            sig <- llvmFunSig lbl ExternallyVisible
            let ty' = LMFunction sig
            let fun = LMGlobalVar fn ty' ExternallyVisible Nothing Nothing False
            let top = CmmData Data [([],[ty'])]
            funInsert fn ty'
            return (fun, nilOL, [top])


-- | Create a new local var
mkLocalVar :: LlvmType -> LlvmM LlvmVar
mkLocalVar ty = do
    un <- runUs getUniqueUs
    return $ LMLocalVar un ty


-- | Execute an expression, assigning result to a var
doExpr :: LlvmType -> LlvmExpression -> LlvmM (LlvmVar, LlvmStatement)
doExpr ty expr = do
    v <- mkLocalVar ty
    return (v, Assignment v expr)


-- | Expand CmmRegOff
expandCmmReg :: (CmmReg, Int) -> CmmExpr
expandCmmReg (reg, off)
  = let width = typeWidth (cmmRegType reg)
        voff  = CmmLit $ CmmInt (fromIntegral off) width
    in CmmMachOp (MO_Add width) [CmmReg reg, voff]


-- | Convert a block id into a appropriate Llvm label
blockIdToLlvm :: BlockId -> LlvmVar
blockIdToLlvm bid = LMLocalVar (getUnique bid) LMLabel

-- | Create Llvm int Literal
mkIntLit :: Integral a => LlvmType -> a -> LlvmVar
mkIntLit ty i = LMLitVar $ LMIntLit (toInteger i) ty

-- | Convert int type to a LLvmVar of word or i32 size
toI32, toIWord :: Integral a => a -> LlvmVar
toI32 = mkIntLit i32
toIWord = mkIntLit llvmWord


-- | Error functions
panic :: String -> a
panic s = Outputable.panic $ "LlvmCodeGen.CodeGen." ++ s

pprPanic :: String -> SDoc -> a
pprPanic s d = Outputable.pprPanic ("LlvmCodeGen.CodeGen." ++ s) d


-- | Returns TBAA meta data by unique
getTBAAMeta :: LMMetaUnique -> LlvmM [MetaData]
getTBAAMeta u = do
    mi <- getUniqMeta u
    return [(tbaa, i) | Just i <- [mi]]

-- | Returns TBAA meta data for given register
getTBAARegMeta :: GlobalReg -> LlvmM [MetaData]
getTBAARegMeta = getTBAAMeta . getTBAA
