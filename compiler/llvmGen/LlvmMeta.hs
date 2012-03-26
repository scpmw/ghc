{-# LANGUAGE CPP #-}

-- -----------------------------------------------------------------------------
-- | Generates meta information about the program useful for debugging and profiling
--

module LlvmMeta (

  cmmMetaLlvmPrelude,
  cmmMetaLlvmProc,
  cmmMetaLlvmUnit,

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

import Config          ( cProjectName, cProjectVersion )
import OldCmm
import Platform
import SrcLoc          (srcSpanFile,
                        srcSpanStartLine, srcSpanStartCol,
                        srcSpanEndLine, srcSpanEndCol)
import MonadUtils      ( MonadIO(..) )
import Outputable      ( showSDoc, ppr )

import System.Directory(getCurrentDirectory)
import Data.List       (maximumBy)
import Data.Maybe      (fromMaybe, fromJust)
import Data.Map as Map (lookup)
import Data.Function   (on)
import Data.Char       (ord, chr, isAscii, isPrint, intToDigit)
import Data.Word       (Word8)

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable

-- Constants

lLVMDebugVersion, dW_TAG_compile_unit, dW_TAG_subroutine_type :: Integer
dW_TAG_file_type, dW_TAG_subprogram, dW_TAG_lexical_block :: Integer
dW_TAG_base_type, dW_TAG_structure_type, dW_TAG_pointer_type :: Integer
dW_TAG_array_type, dW_TAG_subrange_type, dW_TAG_typedef, dW_TAG_auto_variable :: Integer
lLVMDebugVersion       = 0x80000
dW_TAG_compile_unit    = 17 + lLVMDebugVersion
dW_TAG_subroutine_type = 32 + lLVMDebugVersion
dW_TAG_file_type       = 41 + lLVMDebugVersion
dW_TAG_subprogram      = 46 + lLVMDebugVersion
dW_TAG_lexical_block   = 11 + lLVMDebugVersion
dW_TAG_base_type       = 36 + lLVMDebugVersion
dW_TAG_array_type      = 1 + lLVMDebugVersion
dW_TAG_structure_type  = 19 + lLVMDebugVersion
dW_TAG_pointer_type    = 15 + lLVMDebugVersion
dW_TAG_subrange_type   = 33 + lLVMDebugVersion
dW_TAG_typedef         = 22 + lLVMDebugVersion

dW_ATE_address, dW_ATE_boolean, dW_ATE_float, dW_ATE_signed,
  dW_ATE_signed_char, dW_ATE_unsigned, dW_ATE_unsigned_char :: Integer
dW_ATE_address       = 1
dW_ATE_boolean       = 2
dW_ATE_float         = 4
dW_ATE_signed        = 5
dW_ATE_signed_char   = 6
dW_ATE_unsigned      = 7
dW_ATE_unsigned_char = 8

dW_LANG_Haskell :: Integer
dW_LANG_Haskell  = 0x8042 -- Chosen arbitrarily

renderMeta :: LMMetaInt -> LlvmLit -> LlvmM ()
renderMeta n val = renderLlvm $ pprLlvmData ([global], [])
  where global = LMGlobal (LMMetaUnnamed n) (Just (LMStaticLit val))

-- | Ids for unique global meta data nodes
unitN, fileN :: LMMetaUnique
unitN = mkMetaUnique (fsLit "LlvmMeta.unitN")
fileN = mkMetaUnique (fsLit "LlvmMeta.fileN")

-- | Often-used types to cache meta data for
cachedTypeMeta :: [(LlvmType, LMMetaUnique)]
cachedTypeMeta =
  [ mk llvmFunTy   "llvmFunTy"
  , mk i8          "i8"
  , mk i32         "i32"
  , mk i64         "i64"
  , mk (pLift i8)  "i8*"
  , mk (pLift i32) "i32*"
  , mk (pLift i64) "i64*"
  , mk LMFloat     "float"
  , mk LMDouble    "double"
  ]
 where mk ty n = (ty, mkMetaUnique (fsLit $ "LlvmMeta.cachedMeta." ++ n))

-- | Allocates global meta data nodes
cmmMetaLlvmPrelude :: ModLocation -> LlvmM ()
cmmMetaLlvmPrelude mod_loc = do

  -- Allocate compilation unit meta. It gets emitted later in
  -- cmmMetaLlvmUnit, after all procedures have been written out.
  unitId <- getMetaUniqueId
  setUniqMeta unitN unitId

  -- Allocate source file meta data
  fileId <- emitFileMeta (mkFastString $ fromMaybe "" (ml_hs_file mod_loc))
  setUniqMeta fileN fileId

  -- Allocate meta data ids for type descriptors.
  flip mapM_ cachedTypeMeta $ \(_, uniq) -> do
    i <- getMetaUniqueId
    setUniqMeta uniq i

  -- Emit the actual definitions. This is done as a separate step so
  -- the definitions can reference each other.
  flip mapM_ cachedTypeMeta $ \(ty, uniq) -> do
    Just i <- getUniqMeta uniq
    tyMeta <- typeToMeta ty
    renderMeta i tyMeta

  -- Emit TBAA nodes
  flip mapM_ stgTBAA $ \(uniq, name, parent) -> do
    tbaaId <- getMetaUniqueId
    parentId <- maybe (return Nothing) getUniqMeta parent
    renderMeta tbaaId $ LMMeta $ map LMLitVar
      [ LMMetaString name
      , case parentId of
        Just p  -> LMMetaRef p
        Nothing -> nullLit
      ]
    setUniqMeta uniq tbaaId

-- | Emit debug data about the compilation unit. Should be called
-- after all procedure metadata has been generated.
cmmMetaLlvmUnit :: ModLocation -> LlvmM ()
cmmMetaLlvmUnit mod_loc = do

  -- Make lists of enums, retained types, subprograms and globals
  Just unitId <- getUniqMeta unitN
  typeIds <- mapM (fmap fromJust . getUniqMeta . snd) cachedTypeMeta
  procIds <- getProcMetaIds
  let toMetaList      = LMMeta . map (LMLitVar . LMMetaRef)
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
  renderMeta unitId $ LMMeta $ map LMLitVar
    [ mkI32 dW_TAG_compile_unit
    , nullLit                  -- "unused"
    , mkI32 dW_LANG_Haskell            -- DWARF language identifier
    , LMMetaString (fsLit srcFile)     -- Source code name
    , LMMetaString (fsLit srcPath)     -- Compilation base directory
    , LMMetaString (fsLit producerName)-- Producer
    , mkI1 True                        -- Main compilation unit?
                                       -- Not setting this causes LLVM to not generate anything at all!
    , mkI1 $ opt > 0                   -- Optimized?
    , LMMetaString (fsLit "")          -- Flags (?)
    , mkI32 0                          -- Runtime version (?)
    , toMetaList enumTypeMetas         -- List of enums types
    , toMetaList retainTypeMetas       -- List of retained types
    , toMetaList subprogramMetas       -- List of subprograms
    , toMetaList globalMetas           -- List of global variables
    ]

  let mkNamedMeta name xs =
        renderLlvm $ pprLlvmData
          ([LMGlobal (LMMetaNamed (fsLit name))
                     (Just $ LMStaticLit $ LMMetaRefs xs)], [])

  -- This is probably redundant. But judging by what clang produces,
  -- just emitting "llvm.dbg.cu" isn't the only option. So let's be
  -- extra-safe here.
  mkNamedMeta "llvm.dbg.cu"   [unitId]
  mkNamedMeta "llvm.dbg.sp"   subprogramMetas
  mkNamedMeta "llvm.dbg.enum" enumTypeMetas
  mkNamedMeta "llvm.dbg.gv"   globalMetas
  mkNamedMeta "llvm.dbg.ty"   retainTypeMetas

  return ()

emitFileMeta :: FastString -> LlvmM LMMetaInt
emitFileMeta filePath = do

  -- Already have the file?
  m_fileId <- getFileMeta filePath
  case m_fileId of
    Just fileId -> return fileId
    Nothing     -> do

      fileId <- getMetaUniqueId
      Just unitId <- getUniqMeta unitN
      srcPath <- liftIO $ getCurrentDirectory
      renderMeta fileId $ LMMeta $ map LMLitVar
        [ mkI32 dW_TAG_file_type
        , LMMetaString (filePath)                    -- Source file name
        , LMMetaString (mkFastString srcPath)        -- Source file directory
        , LMMetaRef unitId                           -- Reference to compile unit
        ]
      setFileMeta filePath fileId

      return fileId

-- | Generates meta data for a procedure. Returns a meta data Id
-- that can be used to annotate instructions as belonging to this
-- procedure.
cmmMetaLlvmProc :: CLabel -> CLabel -> ModLocation -> TickMap -> LlvmM (Maybe LMMetaInt)
cmmMetaLlvmProc cmmLabel entryLabel mod_loc tiMap = do

  -- Find source tick to associate with procedure
  let unitFile = fromMaybe "** no source file **" (ml_hs_file mod_loc)
      procTick = findGoodSourceTick cmmLabel unitFile tiMap
      (line, col) = case fmap sourceSpan procTick of
        Just span -> (srcSpanStartLine span, srcSpanStartCol span)
        _         -> (1, 0)
  fileId <- emitFileMeta (mkFastString unitFile)

  -- it seems like LLVM 3.0 (likely 2.x as well) ignores the procedureName
  -- procedureName <- strProcedureName_llvm entryLabel
  linkageName <- strCLabel_llvm entryLabel
  displayName <- strDisplayName_llvm entryLabel

  let funRef = LMGlobalVar linkageName (LMPointer llvmFunTy) Internal Nothing Nothing True
      local = not . externallyVisibleCLabel $ entryLabel
      procedureName = displayName

  opt <- getDynFlag optLevel

  -- get global metadata ids from context
  Just unitId <- getUniqMeta unitN
  procTypeMeta <- getTypeMeta llvmFunTy

  procId <- getMetaUniqueId
  renderMeta procId $ LMMeta $ map LMLitVar
    [ mkI32 dW_TAG_subprogram
    , mkI32 0                                    -- "Unused"
    , LMMetaRef unitId                           -- Reference to file
    , LMMetaString procedureName                 -- Procedure name
    , LMMetaString displayName                   -- Display name
    , LMMetaString linkageName                   -- MIPS name
    , LMMetaRef fileId                           -- Reference to file
    , mkI32 $ fromIntegral line                  -- Line number
    , procTypeMeta                               -- Type descriptor
    , mkI1 local                                 -- Local to compile unit
    , mkI1 True                                  -- Defined here (not "extern")
    , mkI32 0                                    -- Virtuality (none)
    , mkI32 0                                    --
    , nullLit                       --
    , mkI1 False                                 -- Artificial (?!)
    , mkI1 $ opt > 0                             -- Optimized
    ] ++ [ funRef ]                              -- Function pointer
  addProcMeta procId

  -- Generate source annotation using the given ID (this is used to
  -- reference it from LLVM code).
  blockId <- getMetaUniqueId
  renderMeta blockId $ LMMeta $ map LMLitVar
    [ mkI32 $ dW_TAG_lexical_block
    , LMMetaRef procId
    , mkI32 $ fromIntegral line               -- Source line
    , mkI32 $ fromIntegral col                -- Source column
    , LMMetaRef fileId                        -- File context
    , mkI32 0                                 -- Template parameter index
    ]

  lineId <- getMetaUniqueId
  renderMeta lineId $ LMMeta $ map LMLitVar
    [ mkI32 $ fromIntegral line               -- Source line
    , mkI32 $ fromIntegral col                -- Source column
    , LMMetaRef blockId                       -- Block context
    , nullLit                                 -- Inlined from location
    ]

  return (Just lineId)

-- | Find a "good" tick we could associate the procedure with in the
-- DWARF debugging data. We do this by looking for source ticks at the
-- given procedure as well as the context that it was created from
-- ("parent").
--
-- As this might often give us a whole list of ticks to choose from,
-- we arbitrarily select the biggest source span - preferably from the
-- source file we are currently compiling - and hope that it
-- corresponds to the most useful location in the code. All nothing
-- but guesswork, obviously, but this is meant to be more or lesser
-- filler data anyway.
findGoodSourceTick :: CLabel -> FilePath -> TickMap -> Maybe (Tickish ())
findGoodSourceTick lbl unit tiMap
  | null ticks = Nothing
  | otherwise  = Just $ maximumBy (compare `on` rangeRating) ticks
  where
    unitFS = mkFastString unit
    ticks = findSourceTis (Map.lookup lbl tiMap)
    rangeRating (SourceNote span _) =
      (srcSpanFile span == unitFS,
       srcSpanEndLine span - srcSpanStartLine span,
       srcSpanEndCol span - srcSpanStartCol span)
    rangeRating _non_source_note = error "rangeRating"
    findSourceTis :: Maybe TickMapEntry -> [Tickish ()]
    findSourceTis Nothing    = []
    findSourceTis (Just tim) =
      case filter isSourceTick (timTicks tim) of
        stis@(_:_)  -> stis
        _           -> findSourceTis (timParent tim)

    isSourceTick SourceNote {} = True
    isSourceTick _             = False

-- | Gives type description as meta data or a reference to a metadata
-- node that contains it.
getTypeMeta :: LlvmType -> LlvmM LlvmLit
getTypeMeta ty
  | Just uniq <- Prelude.lookup ty cachedTypeMeta
              = do Just i <- getUniqMeta uniq
                   return (LMMetaRef i)
  | otherwise = typeToMeta ty

-- | Gives type description as meta data
typeToMeta :: LlvmType -> LlvmM LlvmLit
typeToMeta ty = case ty of
  LMInt{}       -> baseType dW_ATE_signed
  LMFloat{}     -> baseType dW_ATE_float
  LMDouble{}    -> baseType dW_ATE_float
  LMFloat80{}   -> baseType dW_ATE_float
  LMFloat128{}  -> baseType dW_ATE_float
  (LMPointer t) -> derivedType dW_TAG_pointer_type =<< getTypeMeta t
  (LMArray n t) -> compositeType dW_TAG_array_type [subrangeDesc n] =<< getTypeMeta t
  LMLabel       -> derivedType dW_TAG_pointer_type =<< getTypeMeta LMVoid
  LMVoid        -> return nullLit
  (LMStruct ts) -> do members <- mapM getTypeMeta ts
                      compositeType dW_TAG_structure_type members nullLit
  (LMAlias(_,t))-> derivedType dW_TAG_typedef =<< typeToMeta t
  LMMetaType    -> error "typeToMeta: Meta data has no type representation in DWARF!"
  (LMFunction (LlvmFunctionDecl{ decReturnType=retT, decParams=parTs }))
                -> do ret <- getTypeMeta retT
                      pars <- mapM (getTypeMeta . fst) parTs
                      compositeType dW_TAG_subroutine_type (ret:pars) nullLit
 where
  mkType tag fields =  return $ LMMeta $ map LMLitVar $
    [ mkI32 tag
    , nullLit                                         -- Context
    , LMMetaString $ mkFastString $ showSDoc $ ppr ty -- Name
    , nullLit                                         -- File reference
    , mkI32 0                                         -- Line number
    , mkI64 $ fromIntegral $ llvmWidthInBits ty       -- Width in bits
    , mkI64 $ fromIntegral $ llvmWidthInBits llvmWord -- Alignment in bits
    ] ++ fields
  baseType enc = mkType dW_TAG_base_type
    [ mkI32 0                                         -- Flags
    , mkI32 enc                                       -- DWARF type encoding
    ]
  derivedType tag subty = mkType tag
    [ mkI64 0                                         -- Offset in bits
    , subty                                           -- Referenced type
    ]
  compositeType tag members subty = mkType tag
    [ mkI64 0                                         -- Offset in bits
    , mkI32 0                                         -- Flags
    , subty                                           -- Referenced type
    , LMMeta (map LMLitVar members)                   -- Member descriptors
    , mkI32 0                                         -- Runtime languages
    ]
  subrangeDesc n = LMMeta $ map LMLitVar $
    [ mkI32 $ dW_TAG_subrange_type
    , mkI64 0                                         -- Low value
    , mkI64 (fromIntegral $ n-1)                      -- High value
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

      -- Note that LLVM escaping is special: The only valid forms are
      -- "\\" and "\xx", where xx is the hexadecimal ASCII code.
      --
      -- Note that we are actually too careful here - the way LLVM
      -- reads strings in, we could actually output arbitrary garbage as
      -- long as it's not '\\' or '\"'. In the interest of readability
      -- and all-around saneness, we don't take advantage of that.
      escape c
        | c == ord '\\'  = putByte bh (ordB '\\') >> putByte bh (ordB '\\')
        | c == ord '\"'  = putByte bh (ordB '\\') >> putByte bh (ordB '2') >> putByte bh (ordB '2')
        | c == ord '\n'  = putByte bh (ordB '\\') >> putByte bh (ordB '0') >> putByte bh (ordB 'a')
        | isAscii (chr c) && isPrint (chr c)
                         = putByte bh $ fromIntegral c
        | otherwise      = do putByte bh (ordB '\\')
                              putByte bh $ ordB $ intToDigit (c `div` 16)
                              putByte bh $ ordB $ intToDigit (c `mod` 16)
      ordB = (fromIntegral . ord) :: Char -> Word8
  withForeignPtr buf $ \p ->
    go p (p `plusPtr` len)

  -- Pack result into a string
  (elen, ebuf) <- getBinMemBuf bh
  str <- withForeignPtr ebuf $ \p ->
    mkFastStringForeignPtr p ebuf elen

  -- Return static string. Note we need to increment the size by one
  -- because the pretty-printing will append a zero byte.
  return $ LMStaticStr str $ LMArray (len + 1) i8

cmmDebugLlvmGens :: ModLocation -> TickMap -> [RawCmmDecl] -> LlvmM ()
cmmDebugLlvmGens mod_loc tick_map cmm = do

  -- Build a list mapping Cmm labels to linker labels
  let proc_lbl (Just (Statics info_lbl _)) _ = info_lbl
      proc_lbl _                           l = l
      lbls = [(l, proc_lbl i l) | CmmProc i l _ <- cmm]

  -- Write debug data as event log
  platform <- getLlvmPlatform
  dbg <- liftIO $ debugWriteEventlog platform mod_loc tick_map lbls

  -- Convert to a string
  dbgStr <- bufferAsString dbg

  -- Names for symbol / section
  let debug_sym  = fsLit $ "__debug_ghc"
      sectPrefix = case platformOS platform of
        OSDarwin -> "__DWARF,"
        _        -> "."
      sectName   = Just $ fsLit (sectPrefix ++ "debug_ghc")
      lmDebugVar = LMGlobalVar debug_sym (getStatType dbgStr) Internal sectName Nothing False
      lmDebug    = LMGlobal lmDebugVar (Just dbgStr)

  renderLlvm $ pprLlvmData ([lmDebug], [])
  markUsedVar lmDebugVar

mkI32, mkI64 :: Integer -> LlvmLit
mkI32 n = LMIntLit n i32
mkI64 n = LMIntLit n i64
mkI1 :: Bool -> LlvmLit
mkI1 f = LMIntLit (if f then 1 else 0) i1

nullLit :: LlvmLit
nullLit = LMNullLit i8Ptr
