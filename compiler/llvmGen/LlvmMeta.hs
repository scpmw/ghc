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

import System.Directory(getCurrentDirectory)
import Data.List       (maximumBy)
import Data.Maybe      (fromMaybe)
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
dW_TAG_base_type, dW_TAG_arg_variable, dW_TAG_structure_type, dW_TAG_pointer_type :: Integer
lLVMDebugVersion = 0x80000
dW_TAG_compile_unit = 17 + lLVMDebugVersion
dW_TAG_subroutine_type = 32 + lLVMDebugVersion
dW_TAG_file_type = 41 + lLVMDebugVersion
dW_TAG_subprogram = 46 + lLVMDebugVersion
dW_TAG_lexical_block = 11 + lLVMDebugVersion
dW_TAG_base_type = 36 + lLVMDebugVersion
dW_TAG_arg_variable = 257 + lLVMDebugVersion
dW_TAG_structure_type = 19 + lLVMDebugVersion
dW_TAG_pointer_type = 15 + lLVMDebugVersion

dW_LANG_Haskell :: Integer
dW_LANG_Haskell  = 0x8042 -- Chosen arbitrarily

renderMeta :: LMMetaInt -> LlvmStatic -> LlvmM ()
renderMeta n val = renderLlvm $ pprLlvmData ([LMGlobal (LMMetaUnnamed n) (Just val)], [])

-- | Ids for unique global meta data nodes
unitN, procTypeN :: LMMetaUnique
unitN     = mkMetaUnique (fsLit "LlvmMeta.unitN")
procTypeN = mkMetaUnique (fsLit "LlvmMeta.procTypeN")

-- | Allocates global meta data nodes
cmmMetaLlvmPrelude :: LlvmM ()
cmmMetaLlvmPrelude = do

  -- Allocate compilation unit meta. It gets emitted later in
  -- cmmMetaLlvmUnit, after all procedures have been written out.
  unitId <- getMetaUniqueId

  -- Emit the subprogram type we use: void (*)()
  srtypeId <- getMetaUniqueId
  renderMeta srtypeId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_subroutine_type)
    , LMMetaRef unitId                           -- Context
    , LMMetaString (fsLit "")                    -- Name (anonymous)
    , LMStaticLit (LMNullLit LMMetaType)         -- File where defined (null)
    , LMStaticLit (mkI32 0)                      -- Line where defined
    , LMStaticLit (mkI64 0)                      -- Size in bits
    , LMStaticLit (mkI64 0)                      -- Alignment in bits
    , LMStaticLit (mkI64 0)                      -- Offset in bits
    , LMStaticLit (mkI32 0)                      -- Flags in bits
    , LMStaticLit (LMNullLit LMMetaType)         -- Type derived from
    , LMMeta [ LMStaticLit (LMNullLit LMMetaType) ] -- Type list (just void)
    , LMStaticLit (mkI32 0)                      -- Runtime languages (?)
    ]

  -- Save Ids into state monad
  setUniqMeta unitN unitId
  setUniqMeta procTypeN srtypeId

-- | Emit debug data about the compilation unit. Should be called
-- after all procedure metadata has been generated.
cmmMetaLlvmUnit :: ModLocation -> LlvmM ()
cmmMetaLlvmUnit mod_loc = do

  -- Make lists of enums, retained types, subprograms and globals
  Just unitId <- getUniqMeta unitN
  Just procTypeId <- getUniqMeta procTypeN
  procIds <- getProcMetaIds
  let toMetaList      = LMMeta . map LMMetaRef
      enumTypeMetas   = []
      retainTypeMetas = [procTypeId]
      subprogramMetas = procIds
      globalMetas     = []

  -- Data about compilation
  srcPath <- liftIO $ getCurrentDirectory
  let srcFile  = fromMaybe "" (ml_hs_file mod_loc)
      producerName = cProjectName ++ " " ++ cProjectVersion

  -- Emit compile unit information.
  opt <- getDynFlag optLevel
  renderMeta unitId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_compile_unit)
    , LMStaticLit (LMNullLit LMMetaType)         -- "unused"
    , LMStaticLit (mkI32 dW_LANG_Haskell)        -- DWARF language identifier
    , LMMetaString (fsLit srcFile)               -- Source code name
    , LMMetaString (fsLit srcPath)               -- Compilation base directory
    , LMMetaString (fsLit producerName)          -- Producer
    , LMStaticLit (mkI1 True)                    -- Main compilation unit?
                                                 -- Not setting this causes LLVM to not generate anything at all!
    , LMStaticLit (mkI1 $ opt > 0)               -- Optimized?
    , LMMetaString (fsLit "")                    -- Flags (?)
    , LMStaticLit (mkI32 0)                      -- Runtime version (?)
    , toMetaList enumTypeMetas                   -- List of enums types
    , toMetaList retainTypeMetas                 -- List of retained types
    , toMetaList subprogramMetas                 -- List of subprograms
    , toMetaList globalMetas                     -- List of global variables
    ]

  let mkNamedMeta name xs =
        renderLlvm $ pprLlvmData
          ([LMGlobal (LMMetaNamed (fsLit name))
                     (Just (LMMetaRefs xs))], [])

  -- This is probably redundant. But judging by what clang produces,
  -- just emitting "llvm.dbg.cu" isn't the only option. So let's be
  -- extra-safe here.
  mkNamedMeta "llvm.dbg.cu"   [unitId]
  mkNamedMeta "llvm.dbg.sp"   subprogramMetas
  mkNamedMeta "llvm.dbg.enum" enumTypeMetas
  mkNamedMeta "llvm.dbg.gv"   globalMetas

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
      renderMeta fileId $ LMMeta
        [ LMStaticLit (mkI32 dW_TAG_file_type)
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
  Just procTypeId <- getUniqMeta procTypeN

  procId <- getMetaUniqueId
  renderMeta procId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_subprogram)
    , LMStaticLit (mkI32 0)                      -- "Unused"
    , LMMetaRef unitId                           -- Reference to compile unit
    , LMMetaString procedureName                 -- Procedure name
    , LMMetaString displayName                   -- Display name
    , LMMetaString linkageName                   -- MIPS name
    , LMMetaRef fileId                           -- Reference to file
    , LMStaticLit (mkI32 $ fromIntegral line)    -- Line number
    , LMMetaRef procTypeId                       -- Type descriptor
    , LMStaticLit (mkI1 local)                   -- Local to compile unit
    , LMStaticLit (mkI1 True)                    -- Defined here (not "extern")
    , LMStaticLit (mkI32 0)                      -- Virtuality (none)
    , LMStaticLit (mkI32 0)                      --
    , LMStaticLit (LMNullLit LMMetaType)         --
    , LMStaticLit (mkI1 False)                   -- Artificial (?!)
    , LMStaticLit (mkI1 $ opt > 0)               -- Optimized
    , LMStaticPointer funRef                     -- Function pointer
    ]
  addProcMeta procId

  -- Generate source annotation using the given ID (this is used to
  -- reference it from LLVM code).
  blockId <- getMetaUniqueId
  renderMeta blockId $ LMMeta $
    [ LMStaticLit (mkI32 $ dW_TAG_lexical_block)
    , LMMetaRef procId
    , LMStaticLit (mkI32 $ fromIntegral line) -- Source line
    , LMStaticLit (mkI32 $ fromIntegral col)  -- Source column
    , LMMetaRef fileId                        -- File context
    , LMStaticLit (mkI32 0)                   -- Template parameter index
    ]

  lineId <- getMetaUniqueId
  renderMeta lineId $ LMMeta $
    [ LMStaticLit (mkI32 $ fromIntegral line) -- Source line
    , LMStaticLit (mkI32 $ fromIntegral col)  -- Source column
    , LMMetaRef blockId                       -- Block context
    , LMStaticLit (LMNullLit LMMetaType)      -- Inlined from location
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

      -- Note that LLVM esaping is special: The only valid forms are
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
mkI32 n = LMIntLit n (LMInt 32)
mkI64 n = LMIntLit n (LMInt 64)
mkI1 :: Bool -> LlvmLit
mkI1 f = LMIntLit (if f then 1 else 0) (LMInt 1)
