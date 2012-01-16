{-# LANGUAGE CPP #-}

-- -----------------------------------------------------------------------------
-- | Generates meta information about the program useful for debugging and profiling
--

module LlvmMeta ( cmmMetaLlvmGens, cmmDebugLlvmGens ) where

import Llvm

import LlvmCodeGen.Base
import LlvmCodeGen.Ppr

import CLabel
import Module
import DynFlags
import FastString

import Config          ( cProjectName, cProjectVersion )
import Name            ( nameOccName )
import Literal         ( Literal(..) )
import OccName         ( occNameFS )
import Var             ( Var, varName )
import OldCmm
import Outputable
import CoreSyn
import Platform
import SrcLoc          (srcSpanFile,
                        srcSpanStartLine, srcSpanStartCol,
                        srcSpanEndLine, srcSpanEndCol)
import MonadUtils      ( MonadIO(..) )

import System.Directory(getCurrentDirectory)
import Control.Monad   (forM, forM_)
import Data.List       (nub, maximumBy)
import Data.Maybe      (fromMaybe, mapMaybe)
import Data.Map as Map (Map, fromList, assocs, lookup, elems)
import Data.Set as Set (Set, fromList, member)
import Data.Function   (on)
import Data.IORef
import Data.Char       (ord, isAscii, isPrint, intToDigit)
import Data.Word       (Word16)

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
  lastId <- liftIO $ newIORef $ fromMaybe 0 (maximum $ (Nothing:) $ map timInstr $ elems tiMap)
  let freshId = liftIO (modifyIORef lastId (+1) >> readIORef lastId)

  -- Emit compile unit information.
  srcPath <- liftIO $ getCurrentDirectory
  let srcFile  = fromMaybe "" (ml_hs_file mod_loc)
      producerName = cProjectName ++ " " ++ cProjectVersion
  unitId <- freshId
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
  forM_ (assocs tiMap) $ \(lbl, tim) -> do

    -- Decide what source code to associate with procedure
    let procTick = findGoodSourceTick lbl unitFile tiMap idLabelMap
        (line, col) = case fmap sourceSpan procTick of
          Just span -> (srcSpanStartLine span, srcSpanStartCol span)
          _         -> (1, 0)

    -- Find procedure in Cmm data
    case Map.lookup lbl procMap of
      Just (CmmProc infos _ (ListGraph blocks)) | not (null blocks) -> do

        -- Generate metadata for procedure
        entryLabel <- strCLabel_llvm $ case infos of
              Nothing               -> lbl
              Just (Statics lbl' _) -> lbl'
        procId <- freshId
        emitProcMeta procId unitId srtypeId entryLabel procTick defaultFileId (line, col) dflags fileMap

        -- Generate source annotation using the given ID (this is used to
        -- reference it from LLVM code). This information has little
        -- direct use for actual debugging, but prevents LLVM from just
        -- throwing the above debugging information away.
        --
        -- Note that this would end up generating duplicated metadata if
        -- instrumentation IDs weren't unique per procedure!
        case timInstr tim of
          Just i ->
            renderLlvm $ pprMeta i $ LMMeta $
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

emitFileMeta :: Int -> Int -> FilePath -> LlvmM ()
emitFileMeta fileId unitId filePath = do
  srcPath <- liftIO $ getCurrentDirectory
  renderLlvm $ pprMeta fileId $ LMMeta
    [ LMStaticLit (mkI32 dW_TAG_file_type)
    , LMMetaString (fsLit filePath)              -- Source file name
    , LMMetaString (fsLit srcPath)               -- Source file directory
    , LMMetaRef unitId                           -- Reference to compile unit
    ]

emitProcMeta ::
  Int -> Int -> Int -> LMString -> Maybe (Tickish ()) -> Int
  -> (Int, Int) -> DynFlags -> Map FastString Int
  -> LlvmM ()
emitProcMeta procId unitId srtypeId entryLabel procTick defaultFileId (line, _) dflags fileMap = do

  let srcFileLookup = flip Map.lookup fileMap . srcSpanFile . sourceSpan
      fileId = fromMaybe defaultFileId (procTick >>= srcFileLookup)
      funRef = LMGlobalVar entryLabel (LMPointer llvmFunTy) Internal Nothing Nothing True

  renderLlvm $ pprMeta procId $ LMMeta
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

-- | Automatically calculates the correct size of the string
mkStaticString :: String -> LlvmStatic
-- It seems strings aren't really supported in the LLVM back-end right
-- now - probably mainly because LLVM outputs Haskell strings as
-- arrays. So this is a bit bizarre: We need to escape the string
-- first, as well as account for the fact that the backend adds a
-- "\\00" that we actually neither want nor need. I am a bit unsure
-- though what the "right thing to do" is here, therefore I'll just
-- hack around it for the moment. Also: This is inefficient. -- PMW
--
-- Note: The terminating '\0' is now required by the RTS so it can
-- treat pointers into the event log as null-terminated C strings.
mkStaticString str = LMStaticStr (mkFastString (concatMap esc str)) typ
  where typ = LMArray (length str + 1) i8
        esc '\\'   = "\\\\"
        esc '\"'   = "\\22"
        esc '\n'   = "\\0a"
        esc c | isAscii c && isPrint c = [c]
        esc c      = ['\\', intToDigit (ord c `div` 16), intToDigit (ord c `mod` 16)]

-- | Collapses a tree of structures into a single structure, which has the same
-- data layout, but is quicker to produce
flattenStruct :: LlvmStatic -> LlvmStatic
flattenStruct start = mkStaticStruct $ go start []
  where go (LMStaticStruc elems _) xs = foldr go xs elems
        go other                   xs = other:xs

-- | Outputs a 16 bit word in big endian. This is required for all
-- values that the RTS will just copy into the event log later
mkLit16BE :: Int -> LlvmStatic
 -- This is obviously not portable. I suppose you'd have to either
 -- generate a structure or detect our current alignment.
mkLit16BE n = LMStaticLit $ mkI16 $ fromIntegral $ (b1 + 256 * b2)
  where (b1, b2) = (fromIntegral n :: Word16) `divMod` 256

-- | Packs the given static value into a (variable-length) event-log
-- packet.
mkEvent :: Int -> LlvmStatic -> LlvmStatic
mkEvent id cts
  = mkStaticStruct [ LMStaticLit $ mkI8 $ fromIntegral id
                   , LMStaticLit $ mkI16 $ fromIntegral size
                   , cts]
  where size = (llvmWidthInBits (getStatType cts) + 7) `div` 8

mkModuleEvent :: ModLocation -> LlvmStatic
mkModuleEvent mod_loc
  = mkEvent EVENT_DEBUG_MODULE $ mkStaticStruct
      [ mkStaticString $ case ml_hs_file mod_loc of
           Just file -> file
           _         -> "??"
      ]

mkProcedureEvent :: Platform -> TickMapEntry -> CLabel -> LlvmStatic
mkProcedureEvent platform tim lbl
  = mkEvent EVENT_DEBUG_PROCEDURE $ mkStaticStruct
      [ mkLit16BE $ fromMaybe none $ timInstr tim
      , mkLit16BE $ fromMaybe none $ timParent tim
      , mkStaticString $ showSDocC  $ pprCLabel platform lbl
      ]
  where none = 0xffff
        showSDocC = flip renderWithStyle (mkCodeStyle CStyle)

mkAnnotEvent :: Set Var -> Tickish () -> [LlvmStatic]
mkAnnotEvent _ (SourceNote ss names)
  = [mkEvent EVENT_DEBUG_SOURCE $ mkStaticStruct
      [ mkLit16BE $ srcSpanStartLine ss
      , mkLit16BE $ srcSpanStartCol ss
      , mkLit16BE $ srcSpanEndLine ss
      , mkLit16BE $ srcSpanEndCol ss
      , mkStaticString $ unpackFS $ srcSpanFile ss
      , mkStaticString names
      ]]

mkAnnotEvent bnds (CoreNote lbl (ExprPtr core))
  = [mkEvent EVENT_DEBUG_CORE $ mkStaticStruct
      [ mkStaticString $ showSDoc $ ppr lbl
      , mkStaticString $ take 10000 $ showSDoc $ ppr $ stripCore bnds core
      ]]
mkAnnotEvent _ _ = []

mkEvents :: Platform -> Set Var ->
            ModLocation -> TickMap -> [RawCmmDecl] -> LlvmStatic
mkEvents platform bnds mod_loc tick_map cmm
  = mkStaticStruct $
      [ mkModuleEvent mod_loc ] ++
      concat [ mkProcedureEvent platform tim (proc_lbl i l)
               : concatMap (mkAnnotEvent bnds) (timTicks tim)
             | CmmProc i l _ <- cmm
             , Just tim <- [Map.lookup l tick_map]] ++
      [ LMStaticLit $ mkI8 0 ]
  where proc_lbl (Just (Statics info_lbl _)) _ = info_lbl
        proc_lbl _                           l = l

collectBinds :: Tickish () -> [Var]
collectBinds (CoreNote bnd _) = [bnd]
collectBinds _                = []

cmmDebugLlvmGens :: DynFlags -> ModLocation ->
                    TickMap -> [RawCmmDecl] -> LlvmM ()
cmmDebugLlvmGens dflags mod_loc tick_map cmm = do

  let collect tim = concatMap collectBinds $ timTicks tim
      binds =  Set.fromList $ concatMap collect $ elems tick_map

  let platform = targetPlatform dflags

  let events = flattenStruct $ mkEvents platform binds mod_loc tick_map cmm

  -- Names for symbol / section
  let debug_sym  = fsLit $ "__debug_ghc"
      sectPrefix = case platformOS platform of
        OSDarwin -> "__DWARF,"
        _        -> "."
      sectName   = Just $ fsLit (sectPrefix ++ "debug_ghc")
      lmDebugVar = LMGlobalVar debug_sym (getStatType events) Internal sectName Nothing False
      lmDebug    = LMGlobal lmDebugVar (Just events)

  renderLlvm $ pprLlvmData ([lmDebug], [])
  markUsedVar lmDebugVar

mkI8, mkI16, mkI32, mkI64 :: Integer -> LlvmLit
mkI8 n = LMIntLit n (LMInt 8)
mkI16 n = LMIntLit n (LMInt 16)
mkI32 n = LMIntLit n (LMInt 32)
mkI64 n = LMIntLit n (LMInt 64)
mkI1 :: Bool -> LlvmLit
mkI1 f = LMIntLit (if f then 1 else 0) (LMInt 1)

placeholder :: Var -> CoreExpr
placeholder = Lit . MachStr . occNameFS . nameOccName . varName -- for now

stripCore :: Set Var -> CoreExpr -> CoreExpr
stripCore bs (App e1 e2) = App (stripCore bs e1) (stripCore bs e2)
stripCore bs (Lam b e)
  | b `member` bs        = Lam b (placeholder b)
  | otherwise            = Lam b (stripCore bs e)
stripCore bs (Let es e)  = Let (stripLet bs es) (stripCore bs e)
stripCore bs (Tick _ e)  = stripCore bs e -- strip out
stripCore bs (Case e b t as)
  | b `member` bs        = Case (stripCore bs e) b t [(DEFAULT,[],placeholder b)]
  | otherwise            = Case (stripCore bs e) b t (map stripAlt as)
  where stripAlt (a, bn, e) = (a, bn, stripCore bs e)
stripCore bs (CoreSyn.Cast e _)  = stripCore bs e -- strip out
stripCore _  other       = other

stripLet :: Set Var -> CoreBind -> CoreBind
stripLet bs (NonRec b e)
  | b `member` bs        = NonRec b (placeholder b)
  | otherwise            = NonRec b (stripCore bs e)
stripLet bs (Rec ps)     = Rec (map f ps)
  where
    f (b, e)
      | b `member` bs    = (b, placeholder b)
      | otherwise        = (b, stripCore bs e)
