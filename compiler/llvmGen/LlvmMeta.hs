{-# LANGUAGE CPP #-}

-- -----------------------------------------------------------------------------
-- | Generates meta information about the program useful for debugging and profiling
--

module LlvmMeta ( cmmMetaLlvmGens ) where

import Llvm

import LlvmCodeGen.Base
import LlvmCodeGen.Ppr

import CLabel
import Module
import DynFlags
import FastString

import OldCmm
import Outputable
import CoreSyn
import SrcLoc          (srcSpanFile,
                        srcSpanStartLine, srcSpanStartCol,
                        srcSpanEndLine, srcSpanEndCol)

import System.FilePath (splitFileName)
import Control.Monad   (forM, forM_)
import Data.List       (nubBy, find, maximumBy)
import Data.Maybe      (fromMaybe, mapMaybe)
import Data.Map as Map (Map, fromList, assocs, lookup, elems)
import Data.Function   (on)
import Data.IORef

#define EVENTLOG_CONSTANTS_ONLY
#include "../../includes/rts/EventLogFormat.h"

-- Constants

lLVMDebugVersion, dW_TAG_compile_unit, dW_TAG_subroutine_type :: Integer
dW_TAG_file_type, dW_TAG_subprogram :: Integer
lLVMDebugVersion = 0x80000
dW_TAG_compile_unit = 17 + lLVMDebugVersion
dW_TAG_subroutine_type = 32 + lLVMDebugVersion
dW_TAG_file_type = 41 + lLVMDebugVersion
dW_TAG_subprogram = 46 + lLVMDebugVersion

dW_LANG_Haskell :: Integer
dW_LANG_Haskell  = 0x8042 -- Chosen arbitrarily

pprMeta :: Int -> LlvmStatic -> SDoc
pprMeta n val = pprLlvmData ([LMGlobal (LMMetaVar n) (Just val)], [])

cmmMetaLlvmGens :: DynFlags -> Module -> ModLocation ->
                   (SDoc -> IO ()) -> TickMap -> LlvmEnv -> [RawCmmDecl] -> IO ()
cmmMetaLlvmGens dflags mod location render tiMap env cmm = do

  -- We need to be able to find ticks by ID
  let idLabelMap :: Map Int CLabel
      idLabelMap = Map.fromList $ mapMaybe ilm_entry $ assocs tiMap
      ilm_entry (l, TickMapEntry { timInstr = Just i })
                                    = Just (i, l)
      ilm_entry _                   = Nothing

  -- Allocate IDs. The instrumentation numbers will have been used for
  -- line annotations, so we make new IDs start right after them.
  lastId <- newIORef $ fromMaybe 0 (maximum $ map timInstr $ elems tiMap)
  let freshId = modifyIORef lastId (+1) >> readIORef lastId

  -- Emit compile unit information. A whole lot of stuff the debugger
  -- probably won't even care about.
  let (srcPath, srcFile) = case ml_hs_file location of
        Just path -> splitFileName path
        Nothing   -> ("", "")
  unitId <- freshId
  render $ pprMeta unitId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_compile_unit)
    , LMStaticLit (LMNullLit LMMetaType)         -- "unused"
    , LMStaticLit (mkI32 dW_LANG_Haskell)        -- DWARF language identifier
    , LMMetaString (fsLit srcFile)               -- Source code name
    , LMMetaString (fsLit srcPath)               -- Source code directory
    , LMMetaString (fsLit "GHC")                 -- Producer
    , LMStaticLit (mkI1 $ modulePackageId mod == mainPackageId)
                                                 -- Main compilation unit?
    , LMStaticLit (mkI1 $ optLevel dflags > 0)   -- Optimized?
    , LMMetaString (fsLit "")                    -- Flags (?)
    , LMStaticLit (mkI32 0)                      -- Runtime version (?)
    ]

  -- Subprogram type we use: void (*)()
  srtypeId <- freshId
  render $ pprMeta srtypeId $ LMMeta
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
  let files = nubBy ((==) `on` srcSpanFile . sourceSpan) $
              concatMap (filter isSourceTick . timTicks) $
              Map.elems tiMap
  fileMap <- fmap Map.fromList $ forM files $ \(SourceNote span) -> do

    -- We somewhat sneakily use the information present in
    -- SrcSpan.

    -- TODO: Note that right this might come from other modules via
    -- inlining, so we might get bad mixing of base paths here.
    let filePath = unpackFS (srcSpanFile span)

    fileId <- freshId
    emitFileMeta render fileId unitId filePath
    return (filePath, fileId)

  -- Emit metadata for files and procedures
  forM_ (assocs tiMap) $ \(lbl, tim) -> do

    -- Decide what source code to associate with procedure
    let procTick = findGoodSourceTick lbl tiMap idLabelMap
        (line, col) = case fmap sourceSpan procTick of
          Just span -> (srcSpanStartLine span, srcSpanStartCol span)
          _         -> (0, 0)

    -- Find procedure in CMM data
    let myProc (CmmProc _ l _)  = l == lbl
        myProc _                = False
    case find myProc cmm of
      Just (CmmProc infos _ (ListGraph blocks)) | not (null blocks) -> do

        -- Generate metadata for procedure
        let entryLabel = strCLabel_llvm env $ case infos of
              Nothing               -> lbl
              Just (Statics lbl' _) -> lbl'
        procId <- freshId
        emitProcMeta render procId unitId srtypeId entryLabel procTick (line, col) dflags fileMap

        -- Generate source annotation using the given ID (this is used to
        -- reference it from LLVM code). This information has little
        -- direct use for actual debugging, but prevents LLVM from just
        -- throwing the above debugging information away.
        --
        -- Note that this would end up generating duplicated metadata if
        -- instrumentation IDs weren't unique per procedure!
        case timInstr tim of
          Just i ->
            render $ pprMeta i $ LMMeta $
              [ LMStaticLit (mkI32 $ fromIntegral line) -- Source line (yes, no tag!)
              , LMStaticLit (mkI32 $ fromIntegral col)  -- Source column (ignored)
              , LMMetaRef procId
              , LMStaticLit (LMNullLit LMMetaType)      -- "Original scope"
              ]
          Nothing -> return ()

      -- Without CMM source data for the procedure, we are not able to
      -- generate valid DWARF for it
      _otherwise -> return ()

  return ()

emitFileMeta :: (SDoc -> IO ()) -> Int -> Int -> FilePath -> IO ()
emitFileMeta render fileId unitId filePath = do
  let (fileDir, file) = splitFileName filePath
  render $ pprMeta fileId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_file_type)
    , LMMetaString (fsLit file)                  -- Source file name
    , LMMetaString (fsLit fileDir)               -- Source file directory
    , LMMetaRef unitId                           -- Reference to compile unit
    ]

emitProcMeta ::
  (SDoc -> IO ()) -> Int -> Int -> Int -> LMString -> Maybe (Tickish ()) -> (Int, Int)
  -> DynFlags -> Map String Int
  -> IO ()
emitProcMeta render procId unitId srtypeId entryLabel procTick (line, _) dflags fileMap = do

  let srcFileLookup = flip Map.lookup fileMap . unpackFS . srcSpanFile . sourceSpan
      fileId = fromMaybe unitId (procTick >>= srcFileLookup)
      funRef = LMGlobalVar entryLabel (LMPointer llvmFunTy) Internal Nothing Nothing True

  render $ pprMeta procId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_subprogram)
    , LMStaticLit (mkI32 0)                      -- "Unused"
    , LMMetaRef unitId                           -- Reference to compile unit
    , LMMetaString entryLabel                    -- Procedure name
    , LMMetaString entryLabel                    -- Display name
    , LMMetaString entryLabel                    -- MIPS name
    , LMMetaRef fileId                           -- Reference to file
    , LMStaticLit (mkI32 $ fromIntegral line)    -- Line number
    , LMMetaRef srtypeId                         -- Type descriptor
    , LMStaticLit (mkI1 True)                    -- Local to compile unit
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
-- we arbitrarily select the biggest source span and hope that it
-- corresponds to the most useful location in the code. All nothing
-- but guesswork, obviously, but this is meant to be more or lesser
-- filler data anyway.
findGoodSourceTick :: CLabel -> TickMap -> Map Int CLabel -> Maybe (Tickish ())
findGoodSourceTick lbl tiMap idLabelMap
  | null ticks = Nothing
  | otherwise  = Just $ maximumBy (compare `on` rangeLength) ticks
  where
    ticks = findSourceTis lbl
    rangeLength (SourceNote span) =
      (srcSpanEndLine span - srcSpanStartLine span,
       srcSpanEndCol span - srcSpanStartCol span)
    rangeLength _non_source_note = error "rangeLength"
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

mkI32, mkI64 :: Integer -> LlvmLit
mkI32 n = LMIntLit n (LMInt 32)
mkI64 n = LMIntLit n (LMInt 64)
mkI1 :: Bool -> LlvmLit
mkI1 f = LMIntLit (if f then 1 else 0) (LMInt 1)
