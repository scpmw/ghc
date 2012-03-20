{-# LANGUAGE CPP #-}

-- -----------------------------------------------------------------------------
-- | Generates meta information about the program useful for debugging and profiling
--

module LlvmMeta ( cmmMetaLlvmGens, cmmDebugLlvmGens ) where

import Llvm
import Llvm.Types      ( LMMetaInt(..) )

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
import Outputable
import Platform
import SrcLoc          (srcSpanFile,
                        srcSpanStartLine, srcSpanStartCol,
                        srcSpanEndLine, srcSpanEndCol)
import MonadUtils      ( MonadIO(..) )

import System.Directory(getCurrentDirectory)
import Control.Monad   (forM, replicateM_)
import Data.List       (nub, maximumBy)
import Data.Maybe      (fromMaybe, mapMaybe, catMaybes)
import Data.Map as Map (Map, fromList, assocs, lookup, elems)
import Data.Function   (on)
import Data.Char       (ord, chr, isAscii, isPrint, intToDigit)
import Data.Word       (Word8)

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable

-- Constants

lLVMDebugVersion, dW_TAG_compile_unit, dW_TAG_subroutine_type :: Integer
dW_TAG_file_type, dW_TAG_subprogram, dW_TAG_lexical_block :: Integer
dW_TAG_base_type :: Integer
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

pprMeta :: LMMetaInt -> LlvmStatic -> SDoc
pprMeta n val = pprLlvmData ([LMGlobal (LMMetaVar n) (Just val)], [])

cmmMetaLlvmGens :: DynFlags -> ModLocation -> TickMap -> [RawCmmDecl] -> LlvmM ()
cmmMetaLlvmGens dflags mod_loc tiMap cmm = do

  -- We need to be able to find ticks by ID
  let idLabelMap :: Map Int CLabel
      idLabelMap = Map.fromList $ mapMaybe ilm_entry $ assocs tiMap
      ilm_entry (l, TickMapEntry { timInstr = Just i })
                                    = Just (i, l)
      ilm_entry _                   = Nothing

  -- Allocate IDs. The instrumentation numbers will have been used for
  -- line annotations, so we make new IDs start right after them.
  setMetaSeed (LMMetaInt . fromMaybe 0 $ maximum (Nothing:map timInstr (elems tiMap)))
  let freshId = getMetaUniqueId

  -- Emit compile unit information.
  srcPath <- liftIO $ getCurrentDirectory
  let srcFile  = fromMaybe "" (ml_hs_file mod_loc)
      producerName = cProjectName ++ " " ++ cProjectVersion

  unitId <- freshId
  enumTypesId <- freshId
  retainedTypesId <- freshId
  subprogramsId <- freshId
  globalsId <- freshId

  renderLlvm $ pprMeta unitId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_compile_unit)
    , LMStaticLit (LMNullLit LMMetaType)         -- "unused"
    , LMStaticLit (mkI32 dW_LANG_Haskell)        -- DWARF language identifier
    , LMMetaString (fsLit srcFile)               -- Source code name
    , LMMetaString (fsLit srcPath)               -- Compilation base directory
    , LMMetaString (fsLit producerName)          -- Producer
    , LMStaticLit (mkI1 True)                    -- Main compilation unit?
                                                 -- Not setting this causes LLVM to not generate anything at all!
    , LMStaticLit (mkI1 $ optLevel dflags > 0)   -- Optimized?
    , LMMetaString (fsLit "")                    -- Flags (?)
    , LMStaticLit (mkI32 0)                      -- Runtime version (?)
    , LMMetaRef enumTypesId                      -- List of enums types
    , LMMetaRef retainedTypesId                  -- List of retained types
    , LMMetaRef subprogramsId                    -- List of subprograms
    , LMMetaRef globalsId                        -- List of global variables
    ]

  -- Subprogram type we use: void (*)()
  srtypeId <- freshId
  renderLlvm $ pprMeta srtypeId $ LMMeta
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

  -- Emit metadata for all files
  let files = nub $ map (srcSpanFile . sourceSpan) $
              concatMap (filter isSourceTick . timTicks) $
              Map.elems tiMap
  fileMap <- fmap Map.fromList $ forM files $ \file -> do

    -- We somewhat sneakily use the information present in
    -- SrcSpan here.

    -- TODO: Note that right this might come from other modules via
    -- inlining, so we might get bad mixing of base paths here.
    fileId <- freshId
    emitFileMeta fileId unitId (unpackFS file)
    return (file, fileId)

  -- Unless we already have one, emit a "default" file metadata for
  -- the compilation unit. This will be used to annotate all
  -- procedures which have otherwise no associated debug data (so they
  -- won't simply get discarded)
  let unitFile = fromMaybe "** no source file **" (ml_hs_file mod_loc)
  defaultFileId <- case Map.lookup (fsLit unitFile) fileMap of
    Just fileId -> return fileId
    Nothing     -> do
      fileId <- freshId
      emitFileMeta fileId unitId unitFile
      return fileId

  -- Lookup of procedure Cmm data
  let procMap = Map.fromList [ (l, p) | p@(CmmProc _ l _) <- cmm ]

  -- Emit metadata for files and procedures
  procIds <- forM (assocs tiMap) $ \(lbl, tim) -> do

    -- Decide what source code to associate with procedure
    let procTick = findGoodSourceTick lbl unitFile tiMap idLabelMap
        srcFileLookup = flip Map.lookup fileMap . srcSpanFile . sourceSpan
        fileId = fromMaybe defaultFileId (procTick >>= srcFileLookup)
        (line, col) = case fmap sourceSpan procTick of
          Just span -> (srcSpanStartLine span, srcSpanStartCol span)
          _         -> (1, 0)

    -- Find procedure in Cmm data
    case Map.lookup lbl procMap of
      Just (CmmProc infos _ (ListGraph blocks)) | not (null blocks) -> do

        -- Generate metadata for procedure
        let entryLabel = case infos of
              Nothing               -> lbl
              Just (Statics lbl' _) -> lbl'
        procId <- freshId
        emitProcMeta procId unitId srtypeId entryLabel fileId (line, col) dflags

        -- Generate source annotation using the given ID (this is used to
        -- reference it from LLVM code). This information has little
        -- direct use for actual debugging, but prevents LLVM from just
        -- throwing the above debugging information away.
        --
        -- Note that this would end up generating duplicated metadata if
        -- instrumentation IDs weren't unique per procedure!
        case timInstr tim of
          Just i -> do
            blockId <- freshId
            renderLlvm $ pprMeta blockId $ LMMeta $
              [ LMStaticLit (mkI32 $ dW_TAG_lexical_block)
              , LMMetaRef procId
              , LMStaticLit (mkI32 $ fromIntegral line) -- Source line
              , LMStaticLit (mkI32 $ fromIntegral col)  -- Source column
              , LMMetaRef fileId                        -- File context
              , LMStaticLit (mkI32 0)                   -- Template parameter index
              ]
            renderLlvm $ pprMeta (LMMetaInt i) $ LMMeta $
              [ LMStaticLit (mkI32 $ fromIntegral line) -- Source line
              , LMStaticLit (mkI32 $ fromIntegral col)  -- Source column
              , LMMetaRef blockId                       -- Block context
              , LMStaticLit (LMNullLit LMMetaType)      -- Inlined from location
              ]

          Nothing -> return ()

        return $ Just procId

      -- Without CMM source data for the procedure, we are not able to
      -- generate valid DWARF for it
      _otherwise -> return Nothing

  -- Generate a list of all generate subprogram metadata structures
  zeroId <- freshId
  zeroArrayId <- freshId
  let refs xs | null xs'  = LMMeta [LMMetaRef zeroArrayId]
              | otherwise = LMMeta (map LMMetaRef xs')
        where xs' = catMaybes xs

      renderRetainer retainId retainRefs = do
        arrayId <- freshId
        renderLlvm $ pprMeta retainId $ LMMeta [LMMetaRef arrayId]
        renderLlvm $ pprMeta arrayId $ refs retainRefs 

  -- retained debug metadata is a reference to an array
  renderLlvm $ pprMeta zeroArrayId $ LMMeta [LMMetaRef zeroId]
  renderLlvm $ pprMeta zeroId $ LMMeta [LMStaticLit (mkI32 0)]

  renderRetainer enumTypesId []
  renderRetainer retainedTypesId [Just srtypeId]
  renderRetainer subprogramsId procIds
  renderRetainer globalsId []

  -- the DWARF printer prefers all debug metadata
  -- to be referenced from a single global metadata
  renderLlvm $ pprLlvmData
    ([LMGlobal (LMNamedMeta (fsLit "llvm.dbg.cu"))
               (Just (LMMetaRefs [unitId]))], [])

  return ()

emitFileMeta :: LMMetaInt -> LMMetaInt -> FilePath -> LlvmM ()
emitFileMeta fileId unitId filePath = do
  srcPath <- liftIO $ getCurrentDirectory
  renderLlvm $ pprMeta fileId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_file_type)
    , LMMetaString (fsLit filePath)              -- Source file name
    , LMMetaString (fsLit srcPath)               -- Source file directory
    , LMMetaRef unitId                           -- Reference to compile unit
    ]

emitProcMeta :: LMMetaInt -> LMMetaInt -> LMMetaInt -> CLabel -> LMMetaInt
             -> (Int, Int) -> DynFlags -> LlvmM ()
emitProcMeta procId unitId srtypeId entryLabel fileId (line, _) dflags = do
  -- it seems like LLVM 3.0 (likely 2.x as well) ignores the procedureName
  -- procedureName <- strProcedureName_llvm entryLabel
  linkageName <- strCLabel_llvm entryLabel
  displayName <- strDisplayName_llvm entryLabel

  let funRef = LMGlobalVar linkageName (LMPointer llvmFunTy) Internal Nothing Nothing True
      local = not . externallyVisibleCLabel $ entryLabel
      procedureName = displayName

  renderLlvm $ pprMeta procId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_subprogram)
    , LMStaticLit (mkI32 0)                      -- "Unused"
    , LMMetaRef unitId                           -- Reference to compile unit
    , LMMetaString procedureName                 -- Procedure name
    , LMMetaString displayName                   -- Display name
    , LMMetaString linkageName                   -- MIPS name
    , LMMetaRef fileId                           -- Reference to file
    , LMStaticLit (mkI32 $ fromIntegral line)    -- Line number
    , LMMetaRef srtypeId                         -- Type descriptor
    , LMStaticLit (mkI1 local)                   -- Local to compile unit
    , LMStaticLit (mkI1 True)                    -- Defined here (not "extern")
    , LMStaticLit (mkI32 0)                      -- Virtuality (none)
    , LMStaticLit (mkI32 0)                      --
    , LMStaticLit (LMNullLit LMMetaType)         --
    , LMStaticLit (mkI1 False)                   -- Artificial (?!)
    , LMStaticLit (mkI1 $ optLevel dflags > 0)   -- Optimized
    , LMStaticPointer funRef                     -- Function pointer
    ]

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
findGoodSourceTick :: CLabel -> FilePath -> TickMap -> Map Int CLabel -> Maybe (Tickish ())
findGoodSourceTick lbl unit tiMap idLabelMap
  | null ticks = Nothing
  | otherwise  = Just $ maximumBy (compare `on` rangeRating) ticks
  where
    unitFS = mkFastString unit
    ticks = findSourceTis lbl
    rangeRating (SourceNote span _) =
      (srcSpanFile span == unitFS,
       srcSpanEndLine span - srcSpanStartLine span,
       srcSpanEndCol span - srcSpanStartCol span)
    rangeRating _non_source_note = error "rangeRating"
    findSourceTis :: CLabel -> [Tickish ()]
    findSourceTis l = case Map.lookup l tiMap of
      Just tim
        | stis <- filter isSourceTick (timTicks tim), not (null stis)
        -> stis
        | Just p <- timParent tim, Just l' <- Map.lookup p idLabelMap
        -> findSourceTis l'
      _ -> []

isSourceTick :: Tickish () -> Bool
isSourceTick SourceNote {} = True
isSourceTick _             = False

-- | Intelligent constructor, deriving the type of the structure
-- automatically.
mkStaticStruct :: [LlvmStatic] -> LlvmStatic
mkStaticStruct elems = LMStaticStruc elems typ
  where typ = LMStruct $ map getStatType elems

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

cmmDebugLlvmGens :: DynFlags -> ModLocation ->
                    TickMap -> [RawCmmDecl] -> LlvmM ()
cmmDebugLlvmGens dflags mod_loc tick_map cmm = do

  -- Build a list mapping Cmm labels to linker labels
  let proc_lbl (Just (Statics info_lbl _)) _ = info_lbl
      proc_lbl _                           l = l
      lbls = [(l, proc_lbl i l) | CmmProc i l _ <- cmm]

  -- Write debug data as event log
  let platform = targetPlatform dflags
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

mkI8, mkI16, mkI32, mkI64 :: Integer -> LlvmLit
mkI8 n = LMIntLit n (LMInt 8)
mkI16 n = LMIntLit n (LMInt 16)
mkI32 n = LMIntLit n (LMInt 32)
mkI64 n = LMIntLit n (LMInt 64)
mkI1 :: Bool -> LlvmLit
mkI1 f = LMIntLit (if f then 1 else 0) (LMInt 1)
