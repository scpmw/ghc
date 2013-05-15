-- ----------------------------------------------------------------------------
-- | Base LLVM Code Generation module
--
-- Contains functions useful through out the code generator.
--

module LlvmCodeGen.Base (

        LlvmCmmDecl, LlvmBasicBlock,
        LiveGlobalRegs,
        LlvmUnresData, LlvmData, UnresLabel, UnresStatic,

        LlvmVersion, defaultLlvmVersion, minSupportLlvmVersion,
        maxSupportLlvmVersion,

        LlvmM,
        runLlvm, liftStream, withClearVars, varLookup, varInsert,
        markStackReg, checkStackReg,
        funLookup, funInsert, getLlvmVer, getDynFlags, getDynFlag, getLlvmPlatform,
        renderLlvm, runUs, markUsedVar, getUsedVars,
        ghcInternalFunctions,

        getMetaUniqueId,
        setUniqMeta, getUniqMeta,
        setFileMeta, getFileMeta,
        addProcMeta, getProcMetaIds,
        freshSectionId, getModLoc,
        addDebugBlock, getDebugBlocks,

        cmmToLlvmType, widthToLlvmFloat, widthToLlvmInt, llvmFunTy,
        llvmFunSig, llvmStdFunAttrs, llvmFunAlign, llvmInfAlign,
        llvmRegArgPos, llvmPtrBits, mkLlvmFunc, tysToParams,

        strCLabel_llvm, strDisplayName_llvm, strProcedureName_llvm,
        getGlobalPtr, generateAliases,

    ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Regs

import CLabel
import Debug
import CodeGen.Platform ( activeStgRegs )
import DynFlags
import FastString
import Cmm
import qualified Outputable as Outp
import qualified Pretty as Prt
import Platform
import UniqFM
import Unique
import Module ( ModLocation )
import MonadUtils ( MonadIO(..) )
import BufWrite   ( BufHandle )
import UniqSet
import UniqSupply
import ErrUtils
import qualified Stream

import Data.List  ( elemIndex )

-- ----------------------------------------------------------------------------
-- * Some Data Types
--

type LlvmCmmDecl = GenCmmDecl [LlvmData] (Maybe CmmStatics) (ListGraph LlvmStatement)
type LlvmBasicBlock = GenBasicBlock LlvmStatement

-- | Global registers live on proc entry
type LiveGlobalRegs = [GlobalReg]

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
llvmGhcCC dflags
 | platformUnregisterised (targetPlatform dflags) = CC_Ccc
 | otherwise                                      = CC_Ncc 10

-- | Llvm Function type for Cmm function
llvmFunTy :: LiveGlobalRegs -> LlvmM LlvmType
llvmFunTy live = return . LMFunction =<< llvmFunSig' live (fsLit "a") ExternallyVisible

-- | Llvm Function signature
llvmFunSig :: LiveGlobalRegs ->  CLabel -> LlvmLinkageType -> LlvmM LlvmFunctionDecl
llvmFunSig live lbl link = do
  lbl' <- strCLabel_llvm lbl
  llvmFunSig' live lbl' link

llvmFunSig' :: LiveGlobalRegs -> LMString -> LlvmLinkageType -> LlvmM LlvmFunctionDecl
llvmFunSig' live lbl link
  = do let toParams x | isPointer x = (x, [NoAlias, NoCapture])
                      | otherwise   = (x, [])
       dflags <- getDynFlags
       return $ LlvmFunctionDecl lbl link (llvmGhcCC dflags) LMVoid FixedArgs
                                 (map (toParams . getVarType) (llvmFunArgs dflags live))
                                 (llvmFunAlign dflags)

-- | Create a Haskell function in LLVM.
mkLlvmFunc :: LiveGlobalRegs -> CLabel -> LlvmLinkageType -> LMSection -> LlvmBlocks
           -> LlvmM LlvmFunction
mkLlvmFunc live lbl link sec blks
  = do funDec <- llvmFunSig live lbl link
       dflags <- getDynFlags
       let funArgs = map (fsLit . Outp.showSDoc dflags . ppPlainName) (llvmFunArgs dflags live)
       return $ LlvmFunction funDec funArgs llvmStdFunAttrs sec blks

-- | Alignment to use for functions
llvmFunAlign :: DynFlags -> LMAlign
llvmFunAlign dflags = Just (wORD_SIZE dflags)

-- | Alignment to use for into tables
llvmInfAlign :: DynFlags -> LMAlign
llvmInfAlign dflags = Just (wORD_SIZE dflags)

-- | A Function's arguments
llvmFunArgs :: DynFlags -> LiveGlobalRegs -> [LlvmVar]
llvmFunArgs dflags live =
    map (lmGlobalRegArg dflags) (filter isPassed (activeStgRegs platform))
    where platform = targetPlatform dflags
          isPassed r = not (isFloat r) || r `elem` alwaysLive || r `elem` live
          isFloat (FloatReg _)  = True
          isFloat (DoubleReg _) = True
          isFloat _             = False

-- | Position of a register in function arguments
llvmRegArgPos :: DynFlags -> GlobalReg -> Maybe Int
llvmRegArgPos dflags r = elemIndex r (activeStgRegs platform)
    where platform = targetPlatform dflags

-- | Llvm standard fun attributes
llvmStdFunAttrs :: [LlvmFuncAttr]
llvmStdFunAttrs = [NoUnwind]

-- | Convert a list of types to a list of function parameters
-- (each with no parameter attributes)
tysToParams :: [LlvmType] -> [LlvmParameter]
tysToParams = map (\ty -> (ty, []))

-- | Pointer width
llvmPtrBits :: DynFlags -> Int
llvmPtrBits dflags = widthInBits $ typeWidth $ gcWord dflags

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
maxSupportLlvmVersion = 33

-- ----------------------------------------------------------------------------
-- * Environment Handling
--

data LlvmEnv = LlvmEnv
  { envFunMap :: LlvmEnvMap
  , envVarMap :: LlvmEnvMap
  , envStackRegs :: [GlobalReg]
  , envUsedVars :: [LlvmVar]
  , envDelayedTypes :: UniqSet LMString
  , envLabelMap :: [(CLabel, CLabel)]
  , envVersion :: LlvmVersion
  , envDynFlags :: DynFlags
  , envModLoc :: ModLocation
  , envOutput :: BufHandle
  , envUniq :: UniqSupply
  , envFreshMeta :: LMMetaInt
  , envUniqMeta :: UniqFM LMMetaInt
  , envFileMeta :: UniqFM LMMetaInt
  , envProcMeta :: [LMMetaInt]
  , envNextSection :: Int
  , envDebug :: [DebugBlock]
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
runLlvm :: DynFlags -> ModLocation -> LlvmVersion -> BufHandle -> UniqSupply -> LlvmM () -> IO ()
runLlvm dflags mod_loc ver out us m = do
    _ <- runLlvmM m env
    return ()
  where env = LlvmEnv { envFunMap = emptyUFM
                      , envVarMap = emptyUFM
                      , envStackRegs = []
                      , envUsedVars = []
                      , envDelayedTypes = emptyUniqSet
                      , envLabelMap = []
                      , envVersion = ver
                      , envDynFlags = dflags
                      , envModLoc = mod_loc
                      , envOutput = out
                      , envUniq = us
                      , envFreshMeta = 0
                      , envUniqMeta = emptyUFM
                      , envFileMeta = emptyUFM
                      , envProcMeta = []
                      , envNextSection = 1
                      , envDebug = []
                      }

-- | Get environment (internal)
getEnv :: (LlvmEnv -> a) -> LlvmM a
getEnv f = LlvmM (\env -> return (f env, env))

-- | Modify environment (internal)
modifyEnv :: (LlvmEnv -> LlvmEnv) -> LlvmM ()
modifyEnv f = LlvmM (\env -> return ((), f env))

-- | Lift a stream into the LlvmM monad
liftStream :: Stream.Stream IO a x -> Stream.Stream LlvmM a x
liftStream s = Stream.Stream $ do
  r <- liftIO $ Stream.runStream s
  case r of
    Left b        -> return (Left b)
    Right (a, r2) -> return (Right (a, liftStream r2))

-- | Clear variables from the environment for a subcomputation
withClearVars :: LlvmM a -> LlvmM a
withClearVars m = LlvmM $ \env -> do
    (x, env') <- runLlvmM m env { envVarMap = emptyUFM, envStackRegs = [] }
    return (x, env' { envVarMap = emptyUFM, envStackRegs = [] })

-- | Insert variables or functions into the environment.
varInsert, funInsert :: Uniquable key => key -> LlvmType -> LlvmM ()
varInsert s t = modifyEnv $ \env -> env { envVarMap = addToUFM (envVarMap env) s t }
funInsert s t = modifyEnv $ \env -> env { envFunMap = addToUFM (envFunMap env) s t }

-- | Lookup variables or functions in the environment.
varLookup, funLookup :: Uniquable key => key -> LlvmM (Maybe LlvmType)
varLookup s = getEnv (flip lookupUFM s . envVarMap)
funLookup s = getEnv (flip lookupUFM s . envFunMap)

-- | Set a register as allocated on the stack
markStackReg :: GlobalReg -> LlvmM ()
markStackReg r = modifyEnv $ \env -> env { envStackRegs = r : envStackRegs env }

-- | Check whether a register is allocated on the stack
checkStackReg :: GlobalReg -> LlvmM Bool
checkStackReg r = getEnv ((elem r) . envStackRegs)

-- | Allocate a new global unnamed metadata identifier
getMetaUniqueId :: LlvmM LMMetaInt
getMetaUniqueId = LlvmM $ \env -> return (envFreshMeta env, env { envFreshMeta = envFreshMeta env + 1})

-- | Get the LLVM version we are generating code for
getLlvmVer :: LlvmM LlvmVersion
getLlvmVer = getEnv envVersion

-- | Get the platform we are generating code for
getDynFlag :: (DynFlags -> a) -> LlvmM a
getDynFlag f = getEnv (f . envDynFlags)

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
markUsedVar v = modifyEnv $ \env -> env { envUsedVars = v : envUsedVars env }

-- | Return all variables marked as "used" so far
getUsedVars :: LlvmM [LlvmVar]
getUsedVars = getEnv envUsedVars

-- | Saves that at some point we didn't know the type of the label and
-- generated a reference to a type variable instead
delayType :: LMString -> LlvmM ()
delayType lbl = modifyEnv $ \env -> env { envDelayedTypes = addOneToUniqSet (envDelayedTypes env) lbl }

-- | Sets metadata node for a given unique string
setUniqMeta :: LMMetaUnique -> LMMetaInt -> LlvmM ()
setUniqMeta f m = modifyEnv $ \env -> env { envUniqMeta = addToUFM (envUniqMeta env) f m }
-- | Gets metadata node for given unique string
getUniqMeta :: LMMetaUnique -> LlvmM (Maybe LMMetaInt)
getUniqMeta s = getEnv (flip lookupUFM s . envUniqMeta)

-- | Allocates a metadata node for given file
setFileMeta :: LMString -> LMMetaInt -> LlvmM ()
setFileMeta f m = modifyEnv $ \env -> env { envFileMeta = addToUFM (envFileMeta env) f m }
-- | Gets metadata node for given file (if any)
getFileMeta :: LMString -> LlvmM (Maybe LMMetaInt)
getFileMeta s = getEnv (flip lookupUFM s . envFileMeta)

-- | Sets metadata node for given procedure
addProcMeta :: LMMetaInt -> LlvmM ()
addProcMeta m = modifyEnv $ \env -> env { envProcMeta = m:envProcMeta env }
-- | Returns all procedure meta data IDs
getProcMetaIds :: LlvmM [LMMetaInt]
getProcMetaIds = getEnv (reverse . envProcMeta)

-- | Returns a fresh section ID
freshSectionId :: LlvmM Int
freshSectionId = LlvmM $ \env -> return (envNextSection env, env { envNextSection = envNextSection env + 1})

-- | Returns location of current module
getModLoc :: LlvmM ModLocation
getModLoc = getEnv envModLoc

-- | Adds block information to debug data
addDebugBlock :: DebugBlock -> LlvmM ()
addDebugBlock b = modifyEnv $ \e -> e { envDebug = b : envDebug e }

-- | Returns list of block debug information gathered so far
getDebugBlocks :: LlvmM [DebugBlock]
getDebugBlocks = getEnv (reverse . envDebug)

-- ----------------------------------------------------------------------------
-- * Internal functions
--

-- | Here we pre-initialise some functions that are used internally by GHC
-- so as to make sure they have the most general type in the case that
-- user code also uses these functions but with a different type than GHC
-- internally. (Main offender is treating return type as 'void' instead of
-- 'void *'). Fixes trac #5486.
ghcInternalFunctions :: LlvmM ()
ghcInternalFunctions = do
    dflags <- getDynFlags
    mk "memcpy" i8Ptr [i8Ptr, i8Ptr, llvmWord dflags]
    mk "memmove" i8Ptr [i8Ptr, i8Ptr, llvmWord dflags]
    mk "memset" i8Ptr [i8Ptr, llvmWord dflags, llvmWord dflags]
    mk "newSpark" (llvmWord dflags) [i8Ptr, i8Ptr]
  where
    mk n ret args = do
      let n' = fsLit n
          decl = LlvmFunctionDecl n' ExternallyVisible CC_Ccc ret
                                 FixedArgs (tysToParams args) Nothing
      renderLlvm $ ppLlvmFunctionDecl decl
      funInsert n' (LMFunction decl)

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

-- ----------------------------------------------------------------------------
-- * Global variables / forward references
--

-- | Create/get a pointer to a static value. The value type might be
-- an undefined forward type alias if the value in question hasn't
-- been defined yet.
getGlobalPtr :: LMString -> LlvmM LlvmVar
getGlobalPtr llvmLbl = do
  m_ty <- funLookup llvmLbl
  let mkGlbVar lbl ty = LMGlobalVar lbl (LMPointer ty) ExternallyVisible Nothing Nothing
  case m_ty of
    -- Directly reference if we have seen it already
    Just ty -> return $ mkGlbVar llvmLbl ty Global
    -- Otherwise reference a forward alias of it
    Nothing -> do
      delayType llvmLbl
      return $ mkGlbVar
        (llvmLbl `appendFS` fsLit "$alias")
        (LMAlias (llvmLbl `appendFS` fsLit "$type", undefined))
        Alias

-- | Generate aliases for references that were created while compiling.
generateAliases :: LlvmM ([LMGlobal], [LlvmType])
generateAliases = do
  delayed <- getEnv (uniqSetToList . envDelayedTypes)
  dflags <- getDynFlags
  defss <- flip mapM delayed $ \lbl -> do
    -- Defined by now?
    m_ty <- funLookup lbl
    let mkVar ty link = LMGlobalVar lbl (LMPointer ty) link Nothing Nothing Global
        (defs, ty, var, link) = case m_ty of
          Just ty -> ([], ty, mkVar ty ExternallyVisible, Internal)
          Nothing -> let ty = LMArray 0 (llvmWord dflags)
                         var = mkVar ty External
                     in ([LMGlobal var Nothing], ty, var, External)
        aliasLbl = lbl `appendFS` fsLit "$alias"
        tyLbl = lbl `appendFS` fsLit "$type"
        -- See note [Alias Linkage]
        aliasVar = LMGlobalVar aliasLbl (LMPointer ty) link Nothing Nothing Alias
    return ((LMGlobal aliasVar $ Just $ LMStaticPointer var) : defs,
            LMAlias (tyLbl, ty)
            )
  -- Reset forward list
  modifyEnv $ \env -> env { envDelayedTypes = emptyUniqSet }
  let (gss, ts) = unzip defss
  return (concat gss, ts)

-- Note [Llvm Forward References]
--
-- The big issue here is that we might want to refer to values that haven't
-- been defined by this point in the compilation process - and we can't
-- really wait or the whole streaming wouldn't make sense. And after all, LLVM
-- plays really well with forward references, so why not use that?
--
-- Well, the problem is that LLVM is strongly typed, so we positively can't
-- refer to something of which we don't know the type. Sadly, CMM also doesn't
-- carry that kind of information (unless I'm mistaken, of course). So what
-- we do is to define type aliases into the code so we can fill in later what
-- the type in question is expected to be.
--
-- So why do we have to alias the value *itself*? This is actually mainly a
-- workaround, as it turns out that LLVM chokes on this code:
--
--  @ptr = constant %typ* @fun;
--  %typ = type i32 ();
--  define i32 @fun() { ret i32 0; }
--
-- No matter what we do, opt will crash, because it doesn't expect "fun" to have
-- been mentioned with an aliased type. So what we do here is to actually never
-- refer to "fun" itself, but instead refer to a *value* alias of it instead,
-- which we can later set to the proper value without any further hassle:
--
--  @ptr = constant %typ* @fun$alias;
--  define i32 @fun() { ret i32 0; }
--  %typ = type i32 ();
--  @fun$alias = alias %typ* @fun;

-- ----------------------------------------------------------------------------
-- * Misc
--

-- | Error function
panic :: String -> a
panic s = Outp.panic $ "LlvmCodeGen.Base." ++ s

