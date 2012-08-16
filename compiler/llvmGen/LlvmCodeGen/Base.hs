-- ----------------------------------------------------------------------------
-- | Base LLVM Code Generation module
--
-- Contains functions useful through out the code generator.
--

module LlvmCodeGen.Base (

        LlvmCmmDecl, LlvmBasicBlock,
        LlvmUnresData, LlvmData, UnresLabel, UnresStatic,

        LlvmVersion, defaultLlvmVersion, minSupportLlvmVersion,
        maxSupportLlvmVersion,

        LlvmM,
        runLlvm, withClearVars, varLookup, varInsert,
        markStackReg, checkStackReg,
        funLookup, funInsert, getLlvmVer, getDynFlag, getLlvmPlatform,
        renderLlvm, runUs, markUsedVar, getUsedVars,
        ghcInternalFunctions,

        getMetaUniqueId,
        setUniqMeta, getUniqMeta,
        setFileMeta, getFileMeta,
        addProcMeta, getProcMetaIds,

        cmmToLlvmType, widthToLlvmFloat, widthToLlvmInt, llvmFunTy,
        llvmFunSig, llvmStdFunAttrs, llvmFunAlign, llvmInfAlign,
        llvmRegArgPos, llvmPtrBits, mkLlvmFunc, tysToParams,

        strCLabel_llvm, strDisplayName_llvm, strProcedureName_llvm,
        genCmmLabelRef, genStringLabelRef

    ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Regs

import CLabel
import CgUtils ( activeStgRegs )
import Config
import Constants
import FastString
import OldCmm
import qualified Outputable as Outp
import qualified Pretty as Prt
import DynFlags
import Platform
import UniqFM
import Unique
import MonadUtils ( MonadIO(..) )
import BufWrite   ( BufHandle )
import UniqSupply
import ErrUtils

import Data.List  ( elemIndex )

-- ----------------------------------------------------------------------------
-- * Some Data Types
--

type LlvmCmmDecl = GenCmmDecl [LlvmData] (Maybe CmmStatics) (ListGraph LlvmStatement)
type LlvmBasicBlock = GenBasicBlock LlvmStatement

-- | Unresolved code.
-- Of the form: (data label, data type, unresolved data)
type LlvmUnresData = (CLabel, Section, LlvmType, [UnresStatic])

-- | Top level LLVM Data (globals and type aliases)
type LlvmData = ([LMGlobal], [LlvmType])

-- | An unresolved Label.
--
-- Labels are unresolved when we haven't yet determined if they are defined in
-- the module we are currently compiling, or an external one.
type UnresLabel  = CmmLit
type UnresStatic = Either UnresLabel LlvmStatic

-- ----------------------------------------------------------------------------
-- * Type translations
--

-- | Translate a basic CmmType to an LlvmType.
cmmToLlvmType :: CmmType -> LlvmType
cmmToLlvmType ty | isFloatType ty = widthToLlvmFloat $ typeWidth ty
                 | otherwise      = widthToLlvmInt   $ typeWidth ty

-- | Translate a Cmm Float Width to a LlvmType.
widthToLlvmFloat :: Width -> LlvmType
widthToLlvmFloat W32  = LMFloat
widthToLlvmFloat W64  = LMDouble
widthToLlvmFloat W80  = LMFloat80
widthToLlvmFloat W128 = LMFloat128
widthToLlvmFloat w    = panic $ "widthToLlvmFloat: Bad float size: " ++ show w

-- | Translate a Cmm Bit Width to a LlvmType.
widthToLlvmInt :: Width -> LlvmType
widthToLlvmInt w = LMInt $ widthInBits w

-- | GHC Call Convention for LLVM
llvmGhcCC :: DynFlags -> LlvmCallConvention
llvmGhcCC _dflags
          | cGhcUnregisterised == "NO" = CC_Ncc 10
          | otherwise                  = CC_Ccc

-- | Llvm Function type for Cmm function
llvmFunTy :: LlvmM LlvmType
llvmFunTy = return . LMFunction =<< llvmFunSig' (fsLit "a") ExternallyVisible

-- | Llvm Function signature
llvmFunSig :: CLabel -> LlvmLinkageType -> LlvmM LlvmFunctionDecl
llvmFunSig lbl link = do
  lbl' <- strCLabel_llvm lbl
  llvmFunSig' lbl' link

llvmFunSig' :: LMString -> LlvmLinkageType -> LlvmM LlvmFunctionDecl
llvmFunSig' lbl link
  = do let toParams x | isPointer x = (x, [NoAlias, NoCapture])
                      | otherwise   = (x, [])
       dflags <- getDynFlags
       return $ LlvmFunctionDecl lbl link (llvmGhcCC dflags) LMVoid FixedArgs
                                 (map (toParams . getVarType) llvmFunArgs) llvmFunAlign

-- | Create a Haskell function in LLVM.
mkLlvmFunc :: CLabel -> LlvmLinkageType -> LMSection -> LlvmBlocks
           -> LlvmM LlvmFunction
mkLlvmFunc lbl link sec blks
  = do funDec <- llvmFunSig lbl link
       dflags <- getDynFlags
       let funArgs = map (fsLit . Outp.showSDoc dflags . ppPlainName) llvmFunArgs
       return $ LlvmFunction funDec funArgs llvmStdFunAttrs sec blks

-- | Alignment to use for functions
llvmFunAlign :: LMAlign
llvmFunAlign = Just wORD_SIZE

-- | Alignment to use for into tables
llvmInfAlign :: LMAlign
llvmInfAlign = Just wORD_SIZE

-- | A Function's arguments
llvmFunArgs :: [LlvmVar]
llvmFunArgs = map lmGlobalRegArg activeStgRegs

-- | Position of a register in function arguments
llvmRegArgPos :: GlobalReg -> Maybe Int
llvmRegArgPos r = elemIndex r activeStgRegs

-- | Llvm standard fun attributes
llvmStdFunAttrs :: [LlvmFuncAttr]
llvmStdFunAttrs = [NoUnwind]

-- | Convert a list of types to a list of function parameters
-- (each with no parameter attributes)
tysToParams :: [LlvmType] -> [LlvmParameter]
tysToParams = map (\ty -> (ty, []))

-- | Pointer width
llvmPtrBits :: Int
llvmPtrBits = widthInBits $ typeWidth gcWord

-- ----------------------------------------------------------------------------
-- * Llvm Version
--

-- | LLVM Version Number
type LlvmVersion = Int

-- | The LLVM Version we assume if we don't know
defaultLlvmVersion :: LlvmVersion
defaultLlvmVersion = 30

minSupportLlvmVersion :: LlvmVersion
minSupportLlvmVersion = 28

maxSupportLlvmVersion :: LlvmVersion
maxSupportLlvmVersion = 31

-- ----------------------------------------------------------------------------
-- * Environment Handling
--

-- two maps, one for functions and one for local vars.
data LlvmEnv = LlvmEnv
  { envFunMap :: LlvmEnvMap
  , envVarMap :: LlvmEnvMap
  , envStackRegs :: [GlobalReg]
  , envUsedVars :: [LlvmVar]
  , envVersion :: LlvmVersion
  , envDynFlags :: DynFlags
  , envOutput :: BufHandle
  , envUniq :: UniqSupply
  , envFreshMeta :: LMMetaInt
  , envUniqMeta :: UniqFM LMMetaInt
  , envFileMeta :: UniqFM LMMetaInt
  , envProcMeta :: [LMMetaInt]
  }

type LlvmEnvMap = UniqFM LlvmType

-- | The Llvm monad. Wraps @LlvmEnv@ state as well as the @IO@ monad
newtype LlvmM a = LlvmM { runLlvmM :: LlvmEnv -> IO (a, LlvmEnv) }
instance Monad LlvmM where
    return x = LlvmM $ \env -> return (x, env)
    m >>= f  = LlvmM $ \env -> do (x, env') <- runLlvmM m env
                                  runLlvmM (f x) env'
instance Functor LlvmM where
    fmap f m = LlvmM $ \env -> do (x, env') <- runLlvmM m env
                                  return (f x, env')
instance MonadIO LlvmM where
    liftIO m = LlvmM $ \env -> do x <- m
                                  return (x, env)

instance HasDynFlags LlvmM where
    getDynFlags = LlvmM $ \env -> return (envDynFlags env, env)

-- | Get initial Llvm environment.
runLlvm :: DynFlags -> LlvmVersion -> BufHandle -> UniqSupply -> LlvmM () -> IO ()
runLlvm dflags ver out us m = do
    _ <- runLlvmM m env
    return ()
  where env = LlvmEnv { envFunMap = emptyUFM
                      , envVarMap = emptyUFM
                      , envStackRegs = []
                      , envUsedVars = []
                      , envVersion = ver
                      , envDynFlags = dflags
                      , envOutput = out
                      , envUniq = us
                      , envFreshMeta = 0
                      , envUniqMeta = emptyUFM
                      , envFileMeta = emptyUFM
                      , envProcMeta = []
                      }

-- | Clear variables from the environment.
withClearVars :: LlvmM a -> LlvmM a
withClearVars m = LlvmM $ \env -> do
    (x, env') <- runLlvmM m env { envVarMap = emptyUFM, envStackRegs = [] }
    return (x, env' { envVarMap = envVarMap env, envStackRegs = envStackRegs env })

-- | Insert variables or functions into the environment.
varInsert, funInsert :: Uniquable key => key -> LlvmType -> LlvmM ()
varInsert s t = LlvmM $ \env -> return ((), env { envVarMap = addToUFM (envVarMap env) s t } )
funInsert s t = LlvmM $ \env -> return ((), env { envFunMap = addToUFM (envFunMap env) s t } )

-- | Lookup variables or functions in the environment.
varLookup, funLookup :: Uniquable key => key -> LlvmM (Maybe LlvmType)
varLookup s = LlvmM $ \env -> return (lookupUFM (envVarMap env) s, env)
funLookup s = LlvmM $ \env -> return (lookupUFM (envFunMap env) s, env)

-- | Set a register as allocated on the stack
markStackReg :: GlobalReg -> LlvmM ()
markStackReg r = LlvmM $ \env -> return ((), env { envStackRegs = r : envStackRegs env })

-- | Check whether a register is allocated on the stack
checkStackReg :: GlobalReg -> LlvmM Bool
checkStackReg r = LlvmM $ \env -> return (r `elem` envStackRegs env, env)

-- | Allocate a new global unnamed metadata identifier
getMetaUniqueId :: LlvmM LMMetaInt
getMetaUniqueId = LlvmM $ \env -> return (envFreshMeta env, env { envFreshMeta = envFreshMeta env + 1})

-- | Here we pre-initialise some functions that are used internally by GHC
-- so as to make sure they have the most general type in the case that
-- user code also uses these functions but with a different type than GHC
-- internally. (Main offender is treating return type as 'void' instead of
-- 'void *'). Fixes trac #5486.
ghcInternalFunctions :: LlvmM ()
ghcInternalFunctions = sequence_
    [ mk "memcpy" i8Ptr [i8Ptr, i8Ptr, llvmWord]
    , mk "memmove" i8Ptr [i8Ptr, i8Ptr, llvmWord]
    , mk "memset" i8Ptr [i8Ptr, llvmWord, llvmWord]
    , mk "newSpark" llvmWord [i8Ptr, i8Ptr]
    ]
  where
    mk n ret args = do
      let n' = fsLit n
          decl = LlvmFunctionDecl n' ExternallyVisible CC_Ccc ret
                                 FixedArgs (tysToParams args) Nothing
      renderLlvm $ ppLlvmFunctionDecl decl
      funInsert n' (LMFunction decl)

-- | Get the LLVM version we are generating code for
getLlvmVer :: LlvmM LlvmVersion
getLlvmVer = LlvmM $ \env -> return (envVersion env, env)

-- | Get the platform we are generating code for
getDynFlag :: (DynFlags -> a) -> LlvmM a
getDynFlag f = LlvmM $ \env -> return (f $ envDynFlags env, env)

-- | Get the platform we are generating code for
getLlvmPlatform :: LlvmM Platform
getLlvmPlatform = getDynFlag targetPlatform

-- | Prints the given contents to the output handle
renderLlvm :: Outp.SDoc -> LlvmM ()
renderLlvm sdoc = LlvmM $ \env -> do

    -- Write to output
    let doc = Outp.withPprStyleDoc (envDynFlags env) (Outp.mkCodeStyle Outp.CStyle) sdoc
    Prt.bufLeftRender (envOutput env) doc

    -- Dump, if requested
    dumpIfSet_dyn (envDynFlags env) Opt_D_dump_llvm "LLVM Code" sdoc
    return ((), env)

-- | Run a @UniqSM@ action with our unique supply
runUs :: UniqSM a -> LlvmM a
runUs m = LlvmM $ \env -> do
    let (x, us') = initUs (envUniq env) m
    return (x, env { envUniq = us' })

-- | Marks a variable as "used"
markUsedVar :: LlvmVar -> LlvmM ()
markUsedVar v = LlvmM $ \env -> return ((), env { envUsedVars = v : envUsedVars env })

-- | Return all variables marked as "used" so far
getUsedVars :: LlvmM [LlvmVar]
getUsedVars = LlvmM $ \env -> return (envUsedVars env, env)


-- | Convenience functions for defining getters
getLlvmEnv :: (LlvmEnv -> a) -> LlvmM a
getLlvmEnv f = LlvmM $ \env -> return (f env, env)
getLlvmEnvUFM :: Uniquable key => (LlvmEnv -> UniqFM a) -> key -> LlvmM (Maybe a)
getLlvmEnvUFM f s = LlvmM $ \env -> return (lookupUFM (f env) s, env)

-- | Sets metadata node for a given unique string
setUniqMeta :: LMMetaUnique -> LMMetaInt -> LlvmM ()
setUniqMeta f m = LlvmM $ \env -> return ((), env { envUniqMeta = addToUFM (envUniqMeta env) f m })
-- | Gets metadata node for given unique string
getUniqMeta :: LMMetaUnique -> LlvmM (Maybe LMMetaInt)
getUniqMeta = getLlvmEnvUFM envUniqMeta

-- | Allocates a metadata node for given file
setFileMeta :: LMString -> LMMetaInt -> LlvmM ()
setFileMeta f m = LlvmM $ \env -> return ((), env { envFileMeta = addToUFM (envFileMeta env) f m })
-- | Gets metadata node for given file (if any)
getFileMeta :: LMString -> LlvmM (Maybe LMMetaInt)
getFileMeta = getLlvmEnvUFM envFileMeta

-- | Sets metadata node for given procedure
addProcMeta :: LMMetaInt -> LlvmM ()
addProcMeta m = LlvmM $ \env -> return ((), env { envProcMeta = m:envProcMeta env })
-- | Returns all procedure meta data IDs
getProcMetaIds :: LlvmM [LMMetaInt]
getProcMetaIds = getLlvmEnv (reverse . envProcMeta)

-- ----------------------------------------------------------------------------
-- * Label handling
--

-- | Pretty print a 'CLabel'.
strCLabel_llvm :: CLabel -> LlvmM LMString
strCLabel_llvm lbl = do
    platform <- getLlvmPlatform
    dflags <- getDynFlags
    let sdoc = pprCLabel platform lbl
        str = Outp.renderWithStyle dflags sdoc (Outp.mkCodeStyle Outp.CStyle)
    return (fsLit str)

strDisplayName_llvm :: CLabel -> LlvmM LMString
strDisplayName_llvm lbl = do
    platform <- getLlvmPlatform
    dflags <- getDynFlags
    let sdoc = pprCLabel platform lbl
        depth = Outp.PartWay 1
        style = Outp.mkUserStyle (const Outp.NameNotInScope2, const True) depth
        str = Outp.renderWithStyle dflags sdoc style
    return (fsLit (dropInfoSuffix str))

dropInfoSuffix :: String -> String
dropInfoSuffix = go
  where go "_info"        = []
        go "_static_info" = []
        go "_con_info"    = []
        go (x:xs)         = x:go xs
        go []             = []

strProcedureName_llvm :: CLabel -> LlvmM LMString
strProcedureName_llvm lbl = do
    platform <- getLlvmPlatform
    dflags <- getDynFlags
    let sdoc = pprCLabel platform lbl
        depth = Outp.PartWay 1
        style = Outp.mkUserStyle (const Outp.NameUnqual, const False) depth
        str = Outp.renderWithStyle dflags sdoc style
    return (fsLit str)

-- | Create an external definition for a 'CLabel' defined in another module.
genCmmLabelRef :: CLabel -> LlvmM LMGlobal
genCmmLabelRef = fmap genStringLabelRef . strCLabel_llvm

-- | As above ('genCmmLabelRef') but taking a 'LMString', not 'CLabel'.
genStringLabelRef :: LMString -> LMGlobal
genStringLabelRef cl
  = let ty = LMPointer $ LMArray 0 llvmWord
    in LMGlobal (LMGlobalVar cl ty External Nothing Nothing False) Nothing


-- ----------------------------------------------------------------------------
-- * Misc
--

-- | Error function
panic :: String -> a
panic s = Outp.panic $ "LlvmCodeGen.Base." ++ s

