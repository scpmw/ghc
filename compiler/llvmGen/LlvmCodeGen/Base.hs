-- ----------------------------------------------------------------------------
-- | Base LLVM Code Generation module
--
-- Contains functions useful through out the code generator.
--

module LlvmCodeGen.Base (

        LlvmCmmDecl, LlvmBasicBlock,
        LlvmUnresData, LlvmData, UnresLabel, UnresStatic,

        LlvmVersion, defaultLlvmVersion,

        LlvmM,
        runLlvm, withClearVars, varLookup, varInsert,
        funLookup, funInsert, getLlvmVer, getLlvmPlatform,
        renderLlvm, runUs, markUsedVar, getUsedVars,

        cmmToLlvmType, widthToLlvmFloat, widthToLlvmInt, llvmFunTy,
        llvmFunSig, llvmStdFunAttrs, llvmFunAlign, llvmInfAlign,
        llvmPtrBits, mkLlvmFunc, tysToParams,

        strCLabel_llvm, genCmmLabelRef, genStringLabelRef

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
import Platform
import UniqFM
import Unique
import MonadUtils ( MonadIO(..) )
import BufWrite   ( BufHandle )
import UniqSupply

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
llvmGhcCC :: LlvmCallConvention
llvmGhcCC | cGhcUnregisterised == "NO" = CC_Ncc 10
          | otherwise                  = CC_Ccc

-- | Llvm Function type for Cmm function
llvmFunTy :: LlvmType
llvmFunTy = LMFunction $ llvmFunSig' (fsLit "a") ExternallyVisible

-- | Llvm Function signature
llvmFunSig :: CLabel -> LlvmLinkageType -> LlvmM LlvmFunctionDecl
llvmFunSig lbl link = do
  lbl' <- strCLabel_llvm lbl
  return $ llvmFunSig' lbl' link

llvmFunSig' :: LMString -> LlvmLinkageType -> LlvmFunctionDecl
llvmFunSig' lbl link
  = let toParams x | isPointer x = (x, [NoAlias, NoCapture])
                   | otherwise   = (x, [])
    in LlvmFunctionDecl lbl link llvmGhcCC LMVoid FixedArgs
                        (map (toParams . getVarType) llvmFunArgs) llvmFunAlign

-- | Create a Haskell function in LLVM.
mkLlvmFunc :: CLabel -> LlvmLinkageType -> LMSection -> LlvmBlocks -> Maybe Int
           -> LlvmM LlvmFunction
mkLlvmFunc lbl link sec blks instr
  = do funDec <- llvmFunSig lbl link
       let funArgs = map (fsLit . Outp.showSDoc . ppPlainName) llvmFunArgs
       return $ LlvmFunction funDec funArgs llvmStdFunAttrs sec blks instr

-- | Alignment to use for functions
llvmFunAlign :: LMAlign
llvmFunAlign = Just wORD_SIZE

-- | Alignment to use for into tables
llvmInfAlign :: LMAlign
llvmInfAlign = Just wORD_SIZE

-- | A Function's arguments
llvmFunArgs :: [LlvmVar]
llvmFunArgs = map lmGlobalRegArg activeStgRegs

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
defaultLlvmVersion = 28

-- ----------------------------------------------------------------------------
-- * Environment Handling
--

-- two maps, one for functions and one for local vars.
data LlvmEnv = LlvmEnv { envFunMap :: LlvmEnvMap
                       , envVarMap :: LlvmEnvMap
                       , envUsedVars :: [LlvmVar]
                       , envVersion :: LlvmVersion
                       , envPlatform :: Platform
                       , envOutput :: BufHandle
                       , envUniq :: UniqSupply
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

-- | Get initial Llvm environment.
runLlvm :: Platform -> LlvmVersion -> BufHandle -> UniqSupply -> LlvmM () -> IO ()
runLlvm platform ver out us m = runLlvmM m env >> return ()
  where env = LlvmEnv { envFunMap = emptyUFM
                      , envVarMap = emptyUFM
                      , envUsedVars = []
                      , envVersion = ver
                      , envPlatform = platform
                      , envOutput = out
                      , envUniq = us
                      }

-- | Clear variables from the environment.
withClearVars :: LlvmM a -> LlvmM a
withClearVars m = LlvmM $ \env -> do
    (x, env') <- runLlvmM m env { envVarMap = emptyUFM }
    return (x, env' { envVarMap = envVarMap env })

-- | Insert functions into the environment.
varInsert, funInsert :: Uniquable key => key -> LlvmType -> LlvmM ()
varInsert s t = LlvmM $ \env -> return ((), env { envVarMap = addToUFM (envVarMap env) s t } )
funInsert s t = LlvmM $ \env -> return ((), env { envFunMap = addToUFM (envFunMap env) s t } )

-- | Lookup functions in the environment.
varLookup, funLookup :: Uniquable key => key -> LlvmM (Maybe LlvmType)
varLookup s = LlvmM $ \env -> return (lookupUFM (envVarMap env) s, env)
funLookup s = LlvmM $ \env -> return (lookupUFM (envFunMap env) s, env)

-- | Get the LLVM version we are generating code for
getLlvmVer :: LlvmM LlvmVersion
getLlvmVer = LlvmM $ \env -> return (envVersion env, env)

-- | Get the platform we are generating code for
getLlvmPlatform :: LlvmM Platform
getLlvmPlatform = LlvmM $ \env -> return (envPlatform env, env)

-- | Prints the given contents to the output handle
renderLlvm :: Outp.SDoc -> LlvmM ()
renderLlvm sdoc = LlvmM $ \env -> do
    let doc = Outp.withPprStyleDoc (Outp.mkCodeStyle Outp.CStyle) sdoc
    Prt.bufLeftRender (envOutput env) doc
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

-- ----------------------------------------------------------------------------
-- * Label handling
--

-- | Pretty print a 'CLabel'.
strCLabel_llvm :: CLabel -> LlvmM LMString
strCLabel_llvm lbl = do
    platform <- getLlvmPlatform
    let sdoc = pprCLabel platform lbl
        str = Outp.renderWithStyle sdoc (Outp.mkCodeStyle Outp.CStyle)
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

