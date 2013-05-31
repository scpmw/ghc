--------------------------------------------------------------------------------
-- | Pretty print LLVM IR Code.
--

module Llvm.PpLlvm (

    -- * Top level LLVM objects.
    ppLlvmModule,
    ppLlvmComments,
    ppLlvmComment,
    ppLlvmGlobals,
    ppLlvmGlobal,
    ppLlvmAliases,
    ppLlvmAlias,
    ppLlvmFunctionDecls,
    ppLlvmFunctionDecl,
    ppLlvmFunctions,
    ppLlvmFunction,

    ) where

#include "HsVersions.h"

import Llvm.AbsSyn
import Llvm.Types

import Data.List ( intersperse )
import Outputable
import Unique
import FastString ( sLit )

--------------------------------------------------------------------------------
-- * Top Level Print functions
--------------------------------------------------------------------------------

-- | Print out a whole LLVM module.
ppLlvmModule :: LlvmModule -> SDoc
ppLlvmModule (LlvmModule comments aliases globals decls funcs)
  = ppLlvmComments comments $+$ newLine
    $+$ ppLlvmAliases aliases $+$ newLine
    $+$ ppLlvmGlobals globals $+$ newLine
    $+$ ppLlvmFunctionDecls decls $+$ newLine
    $+$ ppLlvmFunctions funcs

-- | Print out a multi-line comment, can be inside a function or on its own
ppLlvmComments :: [LMString] -> SDoc
ppLlvmComments comments = vcat $ map ppLlvmComment comments

-- | Print out a comment, can be inside a function or on its own
ppLlvmComment :: LMString -> SDoc
ppLlvmComment com = semi <+> ftext com


-- | Print out a list of global mutable variable definitions
ppLlvmGlobals :: [LMGlobal] -> SDoc
ppLlvmGlobals ls = vcat $ map ppLlvmGlobal ls

-- | Print out a global mutable variable definition
ppLlvmGlobal :: LMGlobal -> SDoc
ppLlvmGlobal (LMGlobal var@(LMGlobalVar _ _ link x a c) dat) =
    let sect = case x of
            Just x' -> ptext (sLit ", section") <+> doubleQuotes (ftext x')
            Nothing -> empty

        align = case a of
            Just a' -> ptext (sLit ", align") <+> int a'
            Nothing -> empty

        rhs = case dat of
            Just stat -> ppr stat
            Nothing   -> ppr (pLower $ getVarType var)

        -- Position of linkage is different for aliases.
        const_link = case c of
          Global   -> ppr link <+> ptext (sLit "global")
          Constant -> ppr link <+> ptext (sLit "constant")
          Alias    -> ptext (sLit "alias") <+> ppr link

    in ppAssignment var $ const_link <+> rhs <> sect <> align
       $+$ newLine

ppLlvmGlobal (LMGlobal var@(LMMetaUnnamed _) (Just val)) =
  ppAssignment var (ppr val)

ppLlvmGlobal (LMGlobal var@(LMMetaNamed _) (Just (LMStaticLit l))) =
  ppAssignment var (ppLit l) -- omit type annotation

ppLlvmGlobal (LMGlobal var val) = sdocWithDynFlags $ \dflags ->
  error $ "Non Global var ppr as global! "
          ++ showSDoc dflags (ppr var) ++ " " ++ showSDoc dflags (ppr val)


-- | Print out a list of LLVM type aliases.
ppLlvmAliases :: [LlvmAlias] -> SDoc
ppLlvmAliases tys = vcat $ map ppLlvmAlias tys

-- | Print out an LLVM type alias.
ppLlvmAlias :: LlvmAlias -> SDoc
ppLlvmAlias (name, ty)
  = char '%' <> ftext name <+> equals <+> ptext (sLit "type") <+> ppr ty


-- | Print out a list of function definitions.
ppLlvmFunctions :: LlvmFunctions -> SDoc
ppLlvmFunctions funcs = vcat $ map ppLlvmFunction funcs

-- | Print out a function definition.
ppLlvmFunction :: LlvmFunction -> SDoc
ppLlvmFunction (LlvmFunction dec args attrs sec body) =
    let attrDoc = ppSpaceJoin attrs
        secDoc = case sec of
                      Just s' -> ptext (sLit "section") <+> (doubleQuotes $ ftext s')
                      Nothing -> empty
    in ptext (sLit "define") <+> ppLlvmFunctionHeader dec args
        <+> attrDoc <+> secDoc
        $+$ lbrace
        $+$ ppLlvmBlocks body
        $+$ rbrace
        $+$ newLine
        $+$ newLine

-- | Print out a function defenition header.
ppLlvmFunctionHeader :: LlvmFunctionDecl -> [LMString] -> SDoc
ppLlvmFunctionHeader (LlvmFunctionDecl n l c r varg p a) args
  = let varg' = case varg of
                      VarArgs | null p    -> sLit "..."
                              | otherwise -> sLit ", ..."
                      _otherwise          -> sLit ""
        align = case a of
                     Just a' -> ptext (sLit " align ") <> ppr a'
                     Nothing -> empty
        args' = map (\((ty,p),n) -> ppr ty <+> ppSpaceJoin p <+> char '%'
                                    <> ftext n)
                    (zip p args)
    in ppr l <+> ppr c <+> ppr r <+> char '@' <> ftext n <> lparen <>
        (hsep $ punctuate comma args') <> ptext varg' <> rparen <> align

-- | Print out a list of function declaration.
ppLlvmFunctionDecls :: LlvmFunctionDecls -> SDoc
ppLlvmFunctionDecls decs = vcat $ map ppLlvmFunctionDecl decs

-- | Print out a function declaration.
-- Declarations define the function type but don't define the actual body of
-- the function.
ppLlvmFunctionDecl :: LlvmFunctionDecl -> SDoc
ppLlvmFunctionDecl (LlvmFunctionDecl n l c r varg p a)
  = let varg' = case varg of
                      VarArgs | null p    -> sLit "..."
                              | otherwise -> sLit ", ..."
                      _otherwise          -> sLit ""
        align = case a of
                     Just a' -> ptext (sLit " align") <+> ppr a'
                     Nothing -> empty
        args = hcat $ intersperse (comma <> space) $
                  map (\(t,a) -> ppr t <+> ppSpaceJoin a) p
    in ptext (sLit "declare") <+> ppr l <+> ppr c <+> ppr r <+> char '@' <>
        ftext n <> lparen <> args <> ptext varg' <> rparen <> align $+$ newLine


-- | Print out a list of LLVM blocks.
ppLlvmBlocks :: LlvmBlocks -> SDoc
ppLlvmBlocks blocks = vcat $ map ppLlvmBlock blocks

-- | Print out an LLVM block.
-- It must be part of a function definition.
ppLlvmBlock :: LlvmBlock -> SDoc
ppLlvmBlock (LlvmBlock blockId stmts) =
  let isLabel (MkLabel _) = True
      isLabel _           = False
      (block, rest)       = break isLabel stmts
      ppRest = case rest of
        MkLabel id:xs -> ppLlvmBlock (LlvmBlock id xs)
        _             -> empty
  in ppLlvmBlockLabel blockId
           $+$ (vcat $ map ppLlvmStatement block)
           $+$ newLine
           $+$ ppRest

-- | Print out an LLVM block label.
ppLlvmBlockLabel :: LlvmBlockId -> SDoc
ppLlvmBlockLabel id = pprUnique id <> colon


-- | Print out an LLVM statement.
ppLlvmStatement :: LlvmStatement -> SDoc
ppLlvmStatement stmt =
  let ind = (ptext (sLit "  ") <>)
  in case stmt of
        Assignment  dst expr      -> ind $ ppAssignment dst (ppLlvmExpression expr)
        Fence       st ord        -> ind $ ppFence st ord
        Branch      target        -> ind $ ppBranch target
        BranchIf    cond ifT ifF  -> ind $ ppBranchIf cond ifT ifF
        Comment     comments      -> ind $ ppLlvmComments comments
        MkLabel     label         -> ppLlvmBlockLabel label
        Store       value ptr     -> ind $ ppStore value ptr
        Switch      scrut def tgs -> ind $ ppSwitch scrut def tgs
        Return      result        -> ind $ ppReturn result
        Expr        expr          -> ind $ ppLlvmExpression expr
        Unreachable               -> ind $ ptext (sLit "unreachable")
        Nop                       -> empty
        MetaStmt    meta s        -> ppMetaStatement meta s


-- | Print out an LLVM expression.
ppLlvmExpression :: LlvmExpression -> SDoc
ppLlvmExpression expr
  = case expr of
        Alloca     tp amount        -> ppAlloca tp amount
        LlvmOp     op left right    -> ppMachOp op left right
        Call       tp fp args attrs -> ppCall tp fp args attrs
        Cast       op from to       -> ppCast op from to
        Compare    op left right    -> ppCmpOp op left right
        Extract    vec idx          -> ppExtract vec idx
        Insert     vec elt idx      -> ppInsert vec elt idx
        GetElemPtr inb ptr indexes  -> ppGetElementPtr inb ptr indexes
        Load       ptr              -> ppLoad ptr
        Malloc     tp amount        -> ppMalloc tp amount
        Phi        tp precessors    -> ppPhi tp precessors
        Asm        asm c ty v se sk -> ppAsm asm c ty v se sk
        MetaExpr   meta expr        -> ppMetaExpr meta expr


--------------------------------------------------------------------------------
-- * Individual print functions
--------------------------------------------------------------------------------

-- | Should always be a function pointer. So a global var of function type
-- (since globals are always pointers) or a local var of pointer function type.
ppCall :: LlvmCallType -> LlvmVar -> [LlvmVar] -> [LlvmFuncAttr] -> SDoc
ppCall ct fptr vals attrs = case fptr of
                           --
    -- if local var function pointer, unwrap
    LMLocalVar _ (LMPointer (LMFunction d)) -> ppCall' d

    -- should be function type otherwise
    LMGlobalVar _ (LMFunction d) _ _ _ _    -> ppCall' d

    -- not pointer or function, so error
    _other -> error $ "ppCall called with non LMFunction type!\nMust be "
                ++ " called with either global var of function type or "
                ++ "local var of pointer function type."

    where
        ppCall' (LlvmFunctionDecl _ _ cc ret argTy params _) =
            let tc = if ct == TailCall then ptext (sLit "tail ") else empty
                ppValues = ppCommaJoin vals
                ppArgTy  = (ppCommaJoin $ map fst params) <>
                           (case argTy of
                               VarArgs   -> ptext (sLit ", ...")
                               FixedArgs -> empty)
                fnty = space <> lparen <> ppArgTy <> rparen <> ptext (sLit "*")
                attrDoc = ppSpaceJoin attrs
            in  tc <> ptext (sLit "call") <+> ppr cc <+> ppr ret
                    <> fnty <+> ppName fptr <> lparen <+> ppValues
                    <+> rparen <+> attrDoc


ppMachOp :: LlvmMachOp -> LlvmVar -> LlvmVar -> SDoc
ppMachOp op left right =
  (ppr op) <+> (ppr (getVarType left)) <+> ppName left
        <> comma <+> ppName right


ppCmpOp :: LlvmCmpOp -> LlvmVar -> LlvmVar -> SDoc
ppCmpOp op left right =
  let cmpOp
        | isInt (getVarType left) && isInt (getVarType right) = ptext (sLit "icmp")
        | isFloat (getVarType left) && isFloat (getVarType right) = ptext (sLit "fcmp")
        | otherwise = ptext (sLit "icmp") -- Just continue as its much easier to debug
        {-
        | otherwise = error ("can't compare different types, left = "
                ++ (show $ getVarType left) ++ ", right = "
                ++ (show $ getVarType right))
        -}
  in cmpOp <+> ppr op <+> ppr (getVarType left)
        <+> ppName left <> comma <+> ppName right


ppAssignment :: LlvmVar -> SDoc -> SDoc
ppAssignment var expr = ppName var <+> equals <+> expr

ppFence :: Bool -> LlvmSyncOrdering -> SDoc
ppFence st ord =
  let singleThread = case st of True  -> ptext (sLit "singlethread")
                                False -> empty
  in ptext (sLit "fence") <+> singleThread <+> ppSyncOrdering ord

ppSyncOrdering :: LlvmSyncOrdering -> SDoc
ppSyncOrdering SyncUnord     = ptext (sLit "unordered")
ppSyncOrdering SyncMonotonic = ptext (sLit "monotonic")
ppSyncOrdering SyncAcquire   = ptext (sLit "acquire")
ppSyncOrdering SyncRelease   = ptext (sLit "release")
ppSyncOrdering SyncAcqRel    = ptext (sLit "acq_rel")
ppSyncOrdering SyncSeqCst    = ptext (sLit "seq_cst")

-- XXX: On x86, vector types need to be 16-byte aligned for aligned access, but
-- we have no way of guaranteeing that this is true with GHC (we would need to
-- modify the layout of the stack and closures, change the storage manager,
-- etc.). So, we blindly tell LLVM that *any* vector store or load could be
-- unaligned. In the future we may be able to guarantee that certain vector
-- access patterns are aligned, in which case we will need a more granular way
-- of specifying alignment.

ppLoad :: LlvmVar -> SDoc
ppLoad var
    | isVecPtrVar var = ptext (sLit "load") <+> ppr var <>
                        comma <+> ptext (sLit "align 1")
    | otherwise       = ptext (sLit "load") <+> ppr var
  where
    isVecPtrVar :: LlvmVar -> Bool
    isVecPtrVar = isVector . pLower . getVarType

ppStore :: LlvmVar -> LlvmVar -> SDoc
ppStore val dst
    | isVecPtrVar dst = ptext (sLit "store") <+> ppr val <> comma <+> ppr dst <>
                        comma <+> ptext (sLit "align 1")
    | otherwise       = ptext (sLit "store") <+> ppr val <> comma <+> ppr dst
  where
    isVecPtrVar :: LlvmVar -> Bool
    isVecPtrVar = isVector . pLower . getVarType


ppCast :: LlvmCastOp -> LlvmVar -> LlvmType -> SDoc
ppCast op from to = ppr op <+> ppr from <+> ptext (sLit "to") <+> ppr to


ppMalloc :: LlvmType -> Int -> SDoc
ppMalloc tp amount =
  let amount' = LMLitVar $ LMIntLit (toInteger amount) i32
  in ptext (sLit "malloc") <+> ppr tp <> comma <+> ppr amount'


ppAlloca :: LlvmType -> Int -> SDoc
ppAlloca tp amount =
  let amount' = LMLitVar $ LMIntLit (toInteger amount) i32
  in ptext (sLit "alloca") <+> ppr tp <> comma <+> ppr amount'


ppGetElementPtr :: Bool -> LlvmVar -> [LlvmVar] -> SDoc
ppGetElementPtr inb ptr idx =
  let indexes = comma <+> ppCommaJoin idx
      inbound = if inb then ptext (sLit "inbounds") else empty
  in ptext (sLit "getelementptr") <+> inbound <+> ppr ptr <> indexes


ppReturn :: Maybe LlvmVar -> SDoc
ppReturn (Just var) = ptext (sLit "ret") <+> ppr var
ppReturn Nothing    = ptext (sLit "ret") <+> ppr LMVoid


ppBranch :: LlvmVar -> SDoc
ppBranch var = ptext (sLit "br") <+> ppr var


ppBranchIf :: LlvmVar -> LlvmVar -> LlvmVar -> SDoc
ppBranchIf cond trueT falseT
  = ptext (sLit "br") <+> ppr cond <> comma <+> ppr trueT <> comma <+> ppr falseT


ppPhi :: LlvmType -> [(LlvmVar,LlvmVar)] -> SDoc
ppPhi tp preds =
  let ppPreds (val, label) = brackets $ ppName val <> comma <+> ppName label
  in ptext (sLit "phi") <+> ppr tp <+> hsep (punctuate comma $ map ppPreds preds)


ppSwitch :: LlvmVar -> LlvmVar -> [(LlvmVar,LlvmVar)] -> SDoc
ppSwitch scrut dflt targets =
  let ppTarget  (val, lab) = ppr val <> comma <+> ppr lab
      ppTargets  xs        = brackets $ vcat (map ppTarget xs)
  in ptext (sLit "switch") <+> ppr scrut <> comma <+> ppr dflt
        <+> ppTargets targets


ppAsm :: LMString -> LMString -> LlvmType -> [LlvmVar] -> Bool -> Bool -> SDoc
ppAsm asm constraints rty vars sideeffect alignstack =
  let asm'  = doubleQuotes $ ftext asm
      cons  = doubleQuotes $ ftext constraints
      rty'  = ppr rty
      vars' = lparen <+> ppCommaJoin vars <+> rparen
      side  = if sideeffect then ptext (sLit "sideeffect") else empty
      align = if alignstack then ptext (sLit "alignstack") else empty
  in ptext (sLit "call") <+> rty' <+> ptext (sLit "asm") <+> side <+> align <+> asm' <> comma
        <+> cons <> vars'

ppExtract :: LlvmVar -> LlvmVar -> SDoc
ppExtract vec idx =
    ptext (sLit "extractelement")
    <+> ppr (getVarType vec) <+> ppName vec <> comma
    <+> ppr idx

ppInsert :: LlvmVar -> LlvmVar -> LlvmVar -> SDoc
ppInsert vec elt idx =
    ptext (sLit "insertelement")
    <+> ppr (getVarType vec) <+> ppName vec <> comma
    <+> ppr (getVarType elt) <+> ppName elt <> comma
    <+> ppr idx

ppMetaStatement :: [MetaData] -> LlvmStatement -> SDoc
ppMetaStatement meta stmt = case stmt of
  Nop{}     -> ppLlvmStatement stmt
  MkLabel{} -> ppLlvmStatement stmt
  _         -> ppLlvmStatement stmt <> ppMetas meta


ppMetaExpr :: [MetaData] -> LlvmExpression -> SDoc
ppMetaExpr meta expr = ppLlvmExpression expr <> ppMetas meta


ppMetas :: [MetaData] -> SDoc
ppMetas meta = hcat $ map ppMeta meta
  where
    ppMeta (name, var)
        = comma <+> exclamation <> ftext name <+> exclamation <> ppr var

--------------------------------------------------------------------------------
-- * Misc functions
--------------------------------------------------------------------------------

-- | Blank line.
newLine :: SDoc
newLine = empty

-- | Exclamation point.
exclamation :: SDoc
exclamation = char '!'
