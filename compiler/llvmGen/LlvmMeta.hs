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

import Name            ( Name, nameOccName )
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

import System.FilePath (splitFileName)
import Control.Monad   (forM, forM_)
import Data.List       (nubBy, find, maximumBy)
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

mkModuleEvent :: Module -> ModLocation -> LlvmStatic
mkModuleEvent _mod loc
  = mkEvent EVENT_DEBUG_MODULE $ mkStaticStruct
      [ mkStaticString $ case ml_hs_file loc of
           Just file -> file
           _         -> "??"
      ]

mkProcedureEvent :: Platform -> TickMapEntry -> CLabel -> LlvmStatic
mkProcedureEvent platform tim lbl
  = mkEvent EVENT_DEBUG_PROCEDURE $ mkStaticStruct
      [ mkLit16BE $ fromMaybe none $ timInstr tim
      , mkLit16BE $ fromMaybe none $ timParent tim
      , mkStaticString $ showSDoc $ pprCLabel platform lbl
        -- TODO: Hack!
      ]
  where none = 0xffff

mkAnnotEvent :: Set Name -> Tickish () -> [LlvmStatic]
mkAnnotEvent _ (SourceNote ss)
  = [src_ev]
    --if null names then [src_ev] else [name_ev, src_ev]
  where
    src_ev = mkEvent EVENT_DEBUG_SOURCE $ mkStaticStruct
             [ mkLit16BE $ srcSpanStartLine ss
             , mkLit16BE $ srcSpanStartCol ss
             , mkLit16BE $ srcSpanEndLine ss
             , mkLit16BE $ srcSpanEndCol ss
               -- TODO: File!
             ]
{-
    name_ev = mkEvent EVENT_DEBUG_NAME $ mkStaticStruct
              [mkStaticString $ intercalate "/" names]
-}
mkAnnotEvent bnds (CoreNote lbl (ExprPtr core))
  = [mkEvent EVENT_DEBUG_CORE $ mkStaticStruct
      [ mkStaticString $ showSDoc $ ppr lbl
      , mkStaticString $ showSDoc $ ppr $ stripCore bnds core
      ]]
mkAnnotEvent _ _ = []

mkEvents :: Platform -> Set Name -> Module -> ModLocation -> TickMap -> LlvmStatic
mkEvents platform bnds mod loc tick_map
  = mkStaticStruct $
      [ mkModuleEvent mod loc ] ++
      concat [ mkProcedureEvent platform tim lbl
               : concatMap (mkAnnotEvent bnds) (timTicks tim)
             | (lbl, tim) <- assocs tick_map] ++
      [ LMStaticLit $ mkI8 0 ]

collectBinds :: Tickish () -> [Name]
--collectBinds (CoreTick bnd _) = [bnd]
collectBinds _                = []

cmmDebugLlvmGens :: DynFlags -> Module -> ModLocation ->
                    (SDoc -> IO ()) -> TickMap -> LlvmEnv -> IO ()
cmmDebugLlvmGens dflags mod loc render tick_map _env = do

  let collect tim = concatMap collectBinds $ timTicks tim
      binds =  Set.fromList $ concatMap collect $ elems tick_map

  let platform = targetPlatform dflags

  let events     = flattenStruct $ mkEvents platform binds mod loc tick_map
      ty         = getStatType events
      debug_sym  = fsLit $ renderWithStyle (pprCLabel platform (mkHpcDebugData mod)) (mkCodeStyle CStyle)
      sectName   = Just $ fsLit ".__ghc_debug"
      lmDebugVar = LMGlobalVar debug_sym ty ExternallyVisible sectName Nothing False
      lmDebug    = LMGlobal lmDebugVar (Just events)

  render $ pprLlvmData ([lmDebug], [])

mkI8, mkI16, mkI32, mkI64 :: Integer -> LlvmLit
mkI8 n = LMIntLit n (LMInt 8)
mkI16 n = LMIntLit n (LMInt 16)
mkI32 n = LMIntLit n (LMInt 32)
mkI64 n = LMIntLit n (LMInt 64)
mkI1 :: Bool -> LlvmLit
mkI1 f = LMIntLit (if f then 1 else 0) (LMInt 1)

placeholder :: Var -> CoreExpr
placeholder = Lit . MachStr . occNameFS . nameOccName . varName -- for now

stripCore :: Set Name -> CoreExpr -> CoreExpr
stripCore bs (App e1 e2) = App (stripCore bs e1) (stripCore bs e2)
stripCore bs (Lam b e)
  | varName b `member` bs= Lam b (placeholder b)
  | otherwise            = Lam b (stripCore bs e)
stripCore bs (Let es e)  = Let (stripLet bs es) (stripCore bs e)
stripCore bs (Tick _ e)  = stripCore bs e -- strip out
stripCore bs (Case e b t as)
  | varName b `member` bs= Case (stripCore bs e) b t [(DEFAULT,[],placeholder b)]
  | otherwise            = Case (stripCore bs e) b t (map stripAlt as)
  where stripAlt (a, bn, e) = (a, bn, stripCore bs e)
stripCore bs (CoreSyn.Cast e _)  = stripCore bs e -- strip out
stripCore _  other       = other

stripLet :: Set Name -> CoreBind -> CoreBind
stripLet bs (NonRec b e)
  | varName b `member` bs= NonRec b (placeholder b)
  | otherwise            = NonRec b (stripCore bs e)
stripLet bs (Rec ps)     = Rec (map f ps)
  where
    f (b, e)
      | varName b `member` bs = (b, placeholder b)
      | otherwise        = (b, stripCore bs e)
