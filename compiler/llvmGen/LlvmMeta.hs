{-# LANGUAGE CPP #-}

-- -----------------------------------------------------------------------------
-- | Generates meta information about the program useful for debugging and profiling
--

module LlvmMeta (

  cmmMetaLlvmPrelude,
  cmmMetaLlvmUnit,
  cmmMetaLlvmProc,
  cmmMetaLlvmBlock,

  genVariableMeta,

  annotateDebug,

  cmmDebugLlvmGens
  ) where

import Llvm

import LlvmCodeGen.Base
import LlvmCodeGen.Ppr
import LlvmCodeGen.Regs ( stgTBAA )

import CLabel
import Module
import DynFlags
import FastString
import Debug
import Binary
import Dwarf.Constants

import BlockId         ( blockLbl, BlockEnv )
import Config          ( cProjectName, cProjectVersion )
import Cmm
import CmmUtils
import Compiler.Hoopl  ( mapLookup, entryLabel )
import SrcLoc
import MonadUtils      ( MonadIO(..) )
import Outputable      ( showSDoc, ppr, renderWithStyle, mkCodeStyle,  CodeStyle(..) )
import Panic           ( panic )
import Platform        ( platformOS, OS(..) )
import Unique          ( Unique, getKey, getUnique )

import System.Directory( getCurrentDirectory)
import Data.Maybe      ( fromMaybe, fromJust )
import Data.Char       ( ord, chr, isAscii, isPrint, intToDigit)
import Data.Word       ( Word8, Word )
import Data.Bits       ( shiftL)

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable

lLVMDebugVersion :: Word
lLVMDebugVersion = 0x90000

mkDwarfMeta :: Word -> [MetaExpr] -> MetaExpr
mkDwarfMeta tag vars =
  let tagMeta = mkI32 (fromIntegral lLVMDebugVersion + fromIntegral tag)
  in MetaStruct (tagMeta : vars)

renderMeta :: Int -> MetaExpr -> LlvmM ()
renderMeta n expr = renderLlvm $ ppLlvmMeta (MetaUnamed n expr)

-- | Ids for unique global meta data nodes
unitN, fileN :: Unique
unitN = getUnique (fsLit "LlvmMeta.unitN")
fileN = getUnique (fsLit "LlvmMeta.fileN")

-- | Often-used types to cache meta data for
cachedTypeMeta :: LlvmM [(LlvmType, Unique)]
cachedTypeMeta = llvmFunTy [] >>= \funTy -> return
  [ mk funTy       "llvmFunTy"
  , mk i8          "i8"
  , mk i32         "i32"
  , mk i64         "i64"
  , mk (pLift i8)  "i8*"
  , mk (pLift i32) "i32*"
  , mk (pLift i64) "i64*"
  , mk LMFloat     "float"
  , mk LMDouble    "double"
  ]
 where mk ty n = (ty, getUnique (fsLit $ "LlvmMeta.cachedMeta." ++ n))

-- | Allocates global meta data nodes
cmmMetaLlvmPrelude :: LlvmM ()
cmmMetaLlvmPrelude = do
  mod_loc <- getModLoc

  -- Allocate compilation unit meta. It gets emitted later in
  -- cmmMetaLlvmUnit, after all procedures have been written out.
  unitId <- getMetaUniqueId
  setUniqMeta unitN unitId

  -- Allocate source file meta data
  fileId <- emitFileMeta (mkFastString $ fromMaybe "" (ml_hs_file mod_loc))
  setUniqMeta fileN fileId

  -- Allocate meta data ids for type descriptors.
  cached <- cachedTypeMeta
  flip mapM_ cached $ \(_, uniq) -> do
    i <- getMetaUniqueId
    setUniqMeta uniq i

  -- Emit the actual definitions. This is done as a separate step so
  -- the definitions can reference each other.
  flip mapM_ cached $ \(ty, uniq) -> do
    Just i <- getUniqMeta uniq
    tyMeta <- typeToMeta' ty
    renderMeta i tyMeta

  -- Emit TBAA nodes
  flip mapM_ stgTBAA $ \(uniq, name, parent) -> do
    tbaaId <- getMetaUniqueId
    parentId <- maybe (return Nothing) getUniqMeta parent
    renderMeta tbaaId $ MetaStruct
      [ MetaStr name
      , case parentId of
        Just p  -> MetaNode p
        Nothing -> mkNull
      ]
    setUniqMeta uniq tbaaId

-- | Emit debug data about the compilation unit. Should be called
-- after all procedure metadata has been generated.
cmmMetaLlvmUnit :: LlvmM ()
cmmMetaLlvmUnit = do
  mod_loc <- getModLoc

  -- Make lists of enums, retained types, subprograms and globals
  Just unitId <- getUniqMeta unitN
  cached <- cachedTypeMeta
  typeIds <- mapM (fmap fromJust . getUniqMeta . snd) cached
  procIds <- getProcMetaIds
  let toMetaList      = MetaStruct . map MetaNode
      enumTypeMetas   = []
      retainTypeMetas = typeIds
      subprogramMetas = procIds
      globalMetas     = []

  -- Data about compilation
  srcPath <- liftIO $ getCurrentDirectory
  let srcFile  = fromMaybe "" (ml_hs_file mod_loc)
      producerName = cProjectName ++ " " ++ cProjectVersion

  -- Emit compile unit information.
  opt <- getDynFlag optLevel
  renderMeta unitId $ mkDwarfMeta dW_TAG_compile_unit
    [ mkNull                           -- "unused"
    , mkI32 (fromIntegral dW_LANG_Haskell) -- DWARF language identifier
    , MetaStr (fsLit srcFile)          -- Source code name
    , MetaStr (fsLit srcPath)          -- Compilation base directory
    , MetaStr (fsLit producerName)     -- Producer
    , mkI1 True                        -- Main compilation unit?
                                       -- Not setting this causes LLVM to not generate anything at all!
    , mkI1 $ opt > 0                   -- Optimized?
    , MetaStr (fsLit "")          -- Flags (?)
    , mkI32 0                          -- Runtime version (?)
    , toMetaList enumTypeMetas         -- List of enums types
    , toMetaList retainTypeMetas       -- List of retained types
    , toMetaList subprogramMetas       -- List of subprograms
    , toMetaList globalMetas           -- List of global variables
    ]

  let mkNamedMeta name xs = renderLlvm $ ppLlvmMeta $ MetaNamed (fsLit name) xs

  -- This is probably redundant. But judging by what clang produces,
  -- just emitting "llvm.dbg.cu" isn't the only option. So let's be
  -- extra-safe here.
  mkNamedMeta "llvm.dbg.cu"   [unitId]
  mkNamedMeta "llvm.dbg.sp"   subprogramMetas
  mkNamedMeta "llvm.dbg.enum" enumTypeMetas
  mkNamedMeta "llvm.dbg.gv"   globalMetas
  mkNamedMeta "llvm.dbg.ty"   retainTypeMetas

  return ()

emitFileMeta :: FastString -> LlvmM Int
emitFileMeta filePath = do

  -- Already have the file?
  m_fileId <- getFileMeta filePath
  case m_fileId of
    Just fileId -> return fileId
    Nothing     -> do

      fileId <- getMetaUniqueId
      Just unitId <- getUniqMeta unitN
      srcPath <- liftIO $ getCurrentDirectory
      renderMeta fileId $ mkDwarfMeta dW_TAG_file_type
        [ MetaStr (filePath)                    -- Source file name
        , MetaStr (mkFastString srcPath)        -- Source file directory
        , MetaNode unitId                           -- Reference to compile unit
        ]
      setFileMeta filePath fileId

      return fileId

-- | Generates meta data for a procedure, returning its meta data ID
cmmMetaLlvmProc :: RawCmmDecl -> LlvmM (Int, BlockEnv RawTickish)
cmmMetaLlvmProc proc@(CmmProc infos cmmLabel _ graph) = do

  -- Get entry label name
  let entryLabel = case mapLookup (g_entry graph) infos of
        Nothing                  -> cmmLabel
        Just (Statics infoLbl _) -> infoLbl

  -- Find source tick to associate with procedure
  mod_loc <- getModLoc
  let (procTick, blockTicks) = findGoodSourceTicks mod_loc proc
  (file, line, _) <- tickToLoc procTick
  fileId <- emitFileMeta file

  -- it seems like LLVM 3.0 (likely 2.x as well) ignores the procedureName
  -- procedureName <- strProcedureName_llvm entryLabel
  linkageName <- strCLabel_llvm entryLabel
  displayName <- strDisplayName_llvm entryLabel

  funTy <- llvmFunTy []
  funRef <- getGlobalPtr linkageName
  let local = not . externallyVisibleCLabel $ entryLabel
      procedureName = displayName

  opt <- getDynFlag optLevel

  -- get global metadata ids from context
  Just unitId <- getUniqMeta unitN
  procTypeMeta <- typeToMeta funTy

  procId <- getMetaUniqueId
  renderMeta procId $ mkDwarfMeta dW_TAG_subprogram
    [ mkI32 0                     -- "Unused"
    , MetaNode unitId             -- Reference to file
    , MetaStr procedureName       -- Procedure name
    , MetaStr displayName         -- Display name
    , MetaStr linkageName         -- MIPS name
    , MetaNode fileId             -- Reference to file
    , mkI32 $ fromIntegral line   -- Line number
    , procTypeMeta                -- Type descriptor
    , mkI1 local                  -- Local to compile unit
    , mkI1 True                   -- Defined here (not "extern")
    , mkI32 0                     -- Virtuality (none)
    , mkI32 0                     --
    , mkNull                      --
    , mkI1 False                  -- Artificial (?!)
    , mkI1 $ opt > 0              -- Optimized
    , MetaVar funRef              -- Function pointer
    ]
  addProcMeta procId
  return (procId, blockTicks)

cmmMetaLlvmProc _other = panic "cmmMetaLlvmProc: Passed non-proc!"

-- | Make a (file, line, column) tuple from a tick, or fall back to a
-- standard source location where impossible
tickToLoc :: Maybe RawTickish -> LlvmM (FastString, Int, Int)
tickToLoc (Just (SourceNote { sourceSpan = span } )) 
            = return (srcSpanFile span, srcSpanStartLine span, srcSpanStartCol span)
tickToLoc _ = do mod_loc <- getModLoc
                 let unitFile = fromMaybe "** no source file **" (ml_hs_file mod_loc)
                 return (mkFastString unitFile, 1, 0)

-- | Generates meta data for a block and returns a meta data ID to use
-- for annnotating statements
cmmMetaLlvmBlock :: (Int, BlockEnv RawTickish) -> CmmBlock -> LlvmM (Int, Int, Int)
cmmMetaLlvmBlock (procId, blockTicks) block = do

  -- Figure out line information for this tick
  let lbl = entryLabel block
      tick = mapLookup lbl blockTicks
  (file, line, col) <- tickToLoc tick
  fileId <- emitFileMeta file

  -- According to the llvm docs, the main reason it's asking for
  -- source line/column on the blocks is to prevent different
  -- blocks from getting merged. That's plausible, given that
  -- the DWARF standard doesn't even allow giving source
  -- location information for blocks.
  --
  -- As we will be using the same source code location data for
  -- many blocks, we therefore take the liberty here to "cook"
  -- our data so blocks are always unique. Note we have no
  -- reason to do this for the line annotations though - so
  -- generated DWARF should look no different.
  let uniqCol = getKey $ getUnique lbl

  bid <- getMetaUniqueId
  renderMeta bid $ mkDwarfMeta dW_TAG_lexical_block
    [ MetaNode procId
    , mkI32 $ fromIntegral line     -- Source line
    , mkI32 $ fromIntegral uniqCol  -- Source column
    , MetaNode fileId               -- File context
    , mkI32 0                       -- Template parameter index
    ]

  id <- getMetaUniqueId
  renderMeta id $ MetaStruct
    [ mkI32 $ fromIntegral line     -- Source line
    , mkI32 $ fromIntegral col      -- Source column
    , MetaNode bid                  -- Block context
    , mkNull                        -- Inlined from location
    ]

  -- Unfortunately, we actually *want* to be able to identify
  -- individual blocks after compilation - with many of them
  -- sharing the same source line annotation. So we do a little
  -- trick here: We generate a special variable in the scope
  -- above, the name of which will tell the RTS what the block
  -- name actually is.
  dflags <- getDynFlags
  let bname = renderWithStyle dflags (ppr $ blockLbl lbl) (mkCodeStyle CStyle)
      vname = mkFastString ("__debug_ghc_" ++ bname)
  vid <- getMetaUniqueId
  renderMeta vid =<< genVariableMeta vname Nothing i8 bid

  return (bid, id, vid)

-- | Put debug annotations on a list of statements
annotateDebug :: Int -> [LlvmStatement] -> [LlvmStatement]
annotateDebug annotId = map (MetaStmt [MetaAnnot (fsLit "dbg") (MetaNode annotId)])

-- | Gives type description as meta data or a reference to an existing
-- metadata node that contains it.
typeToMeta :: LlvmType -> LlvmM MetaExpr
typeToMeta ty = do
  cached <- cachedTypeMeta
  case Prelude.lookup ty cached of
    Just uniq -> do Just i <- getUniqMeta uniq
                    return (MetaNode i)
    Nothing   -> typeToMeta' ty

-- | Gives type description as meta data
typeToMeta' :: LlvmType -> LlvmM MetaExpr
typeToMeta' ty = case ty of
  LMInt{}       -> baseType dW_ATE_signed
  LMFloat{}     -> baseType dW_ATE_float
  LMDouble{}    -> baseType dW_ATE_float
  LMFloat80{}   -> baseType dW_ATE_float
  LMFloat128{}  -> baseType dW_ATE_float
  (LMPointer t) -> derivedType dW_TAG_pointer_type =<< typeToMeta t
  (LMArray n t) -> compositeType dW_TAG_array_type [subrangeDesc n] =<< typeToMeta t
  (LMVector n t)-> compositeType dW_TAG_array_type [subrangeDesc n] =<< typeToMeta t
  LMLabel       -> derivedType dW_TAG_pointer_type =<< typeToMeta LMVoid
  LMVoid        -> return mkNull
  (LMStruct ts) -> do members <- mapM typeToMeta ts
                      compositeType dW_TAG_structure_type members mkNull
  (LMAlias(_,t))-> derivedType dW_TAG_typedef =<< typeToMeta t
  LMMetadata    -> error "typeToMeta: Meta data has no type representation in DWARF!"
  (LMFunction (LlvmFunctionDecl{ decReturnType=retT, decParams=parTs }))
                -> do ret <- typeToMeta retT
                      pars <- mapM (typeToMeta . fst) parTs
                      compositeType dW_TAG_subroutine_type (ret:pars) mkNull
 where
  mkType tag fields = do
   Just unitMeta <- getUniqMeta unitN
   df <- getDynFlags
   return $ mkDwarfMeta tag $
    [ MetaNode unitMeta                              -- Context
    , MetaStr $ mkFastString $ showSDoc df $ ppr ty  -- Name
    , mkNull                                         -- File reference
    , mkI32 0                                        -- Line number
    , mkI64 $ fromIntegral $ llvmWidthInBits df ty   -- Width in bits
    , mkI64 $ fromIntegral $ llvmWidthInBits df (llvmWord df) -- Alignment in bits
    , mkI64 0                                        -- Offset in bits
    ] ++ fields
  baseType enc = mkType dW_TAG_base_type
    [ mkI32 0                                        -- Flags
    , mkI32 $ fromIntegral enc                       -- DWARF type encoding
    ]
  derivedType tag subty = mkType tag
    [ mkI64 0                                        -- Offset in bits
    , subty                                          -- Referenced type
    ]
  compositeType tag members subty = mkType tag
    [ mkI64 0                                        -- Offset in bits
    , mkI32 0                                        -- Flags
    , subty                                          -- Referenced type
    , MetaStruct members                             -- Member descriptors
    , mkI32 0                                        -- Runtime languages
    ]
  subrangeDesc n = mkDwarfMeta dW_TAG_subrange_type
    [ mkI64 0                                        -- Low value
    , mkI64 (fromIntegral $ n-1)                     -- High value
    ]

genVariableMeta :: LMString -> Maybe Int -> LlvmType -> Int -> LlvmM MetaExpr
genVariableMeta vname par vty scopeId = do
  tyDesc <- typeToMeta vty
  Just fileId <- getUniqMeta fileN
  return $ MetaStruct
    [ mkI32 $ fromIntegral $ case par of
         Nothing -> dW_TAG_auto_variable
         Just _  -> dW_TAG_arg_variable
    , MetaNode scopeId                               -- Context
    , MetaStr vname                                  -- Name
    , MetaNode fileId                                -- File reference
    , mkI32 (fromIntegral (maybe 0 (+1) par `shiftL` 24))
                                                     -- Line / argument number
    , tyDesc                                         -- Type description
    , mkI32 0                                        -- Flags
    ]

-- | Return buffer contents as a LLVM string
bufferAsString :: (Int, ForeignPtr Word8) -> LlvmM LlvmStatic
bufferAsString (len, buf) = liftIO $ do

  -- As we output a string, we need to do escaping. We approximate
  -- here that the escaped string will have double the size of the
  -- original buffer. That should be plenty of space given the fact
  -- that we expect to be converting a lot of text.
  bh <- openBinMem (len * 2)
  let go p q | p == q    = return ()
             | otherwise = peek p >>= escape . fromIntegral >> go (p `plusPtr` 1) q

      -- Note that LLVM escaping is special: The only valid escapes are
      -- "\\" and "\xx", where xx is the hexadecimal ASCII code.
      escape c
        | c == ord '\\'  = putB '\\' >> putB '\\'
        | c == ord '\"'  = putB '\\' >> putB '2' >> putB '2'
        | c == ord '\n'  = putB '\\' >> putB '0' >> putB 'a'
        | c == ord '?'   = putB '\\' >> putB '3' >> putB 'f' -- silence trigraph warnings
        | isAscii (chr c) && isPrint (chr c)
                         = putByte bh $ fromIntegral c
        | otherwise      = do putB '\\'
                              putB $ intToDigit (c `div` 16)
                              putB $ intToDigit (c `mod` 16)
      putB = putByte bh . fromIntegral . ord
  withForeignPtr buf $ \p ->
    go p (p `plusPtr` len)

  -- Pack result into a string
  (elen, ebuf) <- getBinMemBuf bh
  str <- withForeignPtr ebuf $ \p ->
    mkFastStringForeignPtr p ebuf elen

  -- Return static string. Note we need to increment the size by one
  -- because the pretty-printing will append a zero byte.
  return $ LMStaticStr str $ LMArray (len + 1) i8

cmmDebugLlvmGens :: LlvmM ()
cmmDebugLlvmGens = do

  -- Complete debug information structure
  dflags <- getDynFlag id
  modLoc <- getModLoc
  blocks <- getDebugBlocks
  let dmod = DebugModule { dmodPackage = thisPackage dflags
                         , dmodLocation = modLoc
                         , dmodBlocks = blocks }

  -- Write debug data as event log
  dbg <- liftIO $ debugWriteEventlog dflags dmod

  -- Convert to a string
  dbgStr <- bufferAsString dbg

  -- Names for symbol / section
  platform <- getLlvmPlatform
  let debug_sym  = fsLit $ "__debug_ghc"
      sectPrefix = case platformOS platform of
        OSDarwin -> "__DWARF,"
        _        -> "."
      sectName   = Just $ fsLit (sectPrefix ++ "debug_ghc")
      lmDebugVar = LMGlobalVar debug_sym (getStatType dbgStr) Internal sectName Nothing Constant
      lmDebug    = LMGlobal lmDebugVar (Just dbgStr)

  renderLlvm $ pprLlvmData ([lmDebug], [])
  markUsedVar lmDebugVar

-- Convenience functions for constructing certain metadata values

mkI32, mkI64 :: Integer -> MetaExpr
mkI32 n = MetaVar $ LMLitVar $ LMIntLit n i32
mkI64 n = MetaVar $ LMLitVar $ LMIntLit n i64
mkI1 :: Bool -> MetaExpr
mkI1 f = MetaVar $ LMLitVar $ LMIntLit (if f then 1 else 0) i1

mkNull :: MetaExpr
mkNull = MetaVar $ LMLitVar $ LMNullLit i8Ptr
