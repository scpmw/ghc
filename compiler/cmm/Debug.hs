{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
--
-- Debugging data
--
-- Association of debug data on the Cmm level, with methods to encode it in
-- event log format for later inclusion in profiling event logs.
--
-----------------------------------------------------------------------------

module Debug (

  RawTickish, Tickish(..), -- reexported

  DebugModule(..), DebugBlock(..),
  cmmProcDebug,
  debugWriteEventlog

  ) where

import Binary
import BlockId         ( blockLbl )
import CLabel
import Cmm
import CmmUtils
import DynFlags
import FastString      ( unpackFS )
import Module
import CoreSyn
import Outputable
import PprCmmExpr      ( pprExpr )
import SrcLoc
import UniqFM
import Util            ( seqList )
import Var

import Compiler.Hoopl

import Control.Monad ( forM, forM_, foldM )

import Data.Word
import Data.Maybe
import Data.Char     ( ord )
import Data.List     ( find )

import Foreign.ForeignPtr

#define EVENTLOG_CONSTANTS_ONLY
#include "../../includes/rts/EventLogFormat.h"

-- | Packs the given static value into a (variable-length) event-log
-- packet.
putEvent :: BinHandle -> Word8 -> IO a -> IO a
putEvent bh id cts = catchSize bh 0x10000 wrap return
 where wrap = do
         put_ bh id
         -- Put placeholder for size
         sizePos <- put bh (0 :: Word16)
         -- Put contents
         a <- cts
         -- Put final size
         endPos <- tellBin bh
         putAt bh sizePos $ fromIntegral $ (endPos `diffBin` sizePos) - 2
         -- Seek back
         seekBin bh endPos
         return a

-- | Puts an alternate version if the first one is bigger than the
-- given limit.
--
-- This is a pretty crude way of handling oversized
-- packets... Can't think of a better way right now though.
catchSize :: BinHandle -> Int -> IO a -> (a -> IO a) -> IO a
catchSize bh limit cts1 cts2 = do

  -- Put contents, note how much size it uses
  start <- tellBin bh :: IO (Bin ())
  a <- cts1
  end <- tellBin bh

  -- Seek back and put second version if size is over limit
  if (end `diffBin` start) >= limit
    then do seekBin bh start
            cts2 a
    else return a

-- | Holds identities of core pieces we have decided to output
type CoreMap = UniqFM [AltCon]

elemCoreMap :: (Var, AltCon) -> CoreMap -> Bool
elemCoreMap (bind, con) m = case lookupUFM m bind of
  Just cs -> con `elem` cs
  Nothing -> False

addToCoreMap :: Var -> AltCon -> CoreMap -> CoreMap
addToCoreMap b a d = addToUFM_C (\o _ -> a:o) d b [a]

unionCoreMap :: CoreMap -> CoreMap -> CoreMap
unionCoreMap = plusUFM_C (++)

data DebugModule = DebugModule { dmodPackage :: PackageId
                               , dmodLocation :: ModLocation
                               , dmodBlocks :: [DebugBlock]
                               }

-- | Debug information about a block of code. Can be nested to show
-- context.
data DebugBlock =
  DebugBlock
  { dblProcedure  :: Bool                -- ^ Top-level procedure?
  , dblLabel      :: Label               -- ^ Hoopl label
  , dblCLabel     :: CLabel              -- ^ Output label
  , dblHasInfoTbl :: !Bool               -- ^ Has an info table?
  , dblTicks      :: ![RawTickish]       -- ^ Ticks defined in this block
  , dblSourceTick :: !(Maybe RawTickish) -- ^ Best source tick covering this block
  , dblPosition   :: !(Maybe Int)        -- ^ Output position relative to other blocks in proc.
                                         --   @Nothing@ means the block has been optimized out.
  , dblStackOff   :: !(Maybe Int)        -- ^ Unwind information
  , dblBlocks     :: [DebugBlock]        -- ^ Nested blocks
  }

instance Outputable DebugBlock where
  ppr blk = (if dblProcedure blk then text "proc "
             else if dblHasInfoTbl blk then text "pp-blk " else text "blk ") <>
            ppr (dblLabel blk) <+> parens (ppr (dblCLabel blk)) <+>
            (maybe empty ppr (dblSourceTick blk)) <+>
            (maybe empty ppr (find isCore (dblTicks blk))) <+>
            (maybe (text "removed") ((text "pos " <>) . ppr) (dblPosition blk)) $$
            (if null (dblBlocks blk) then empty else ppr (dblBlocks blk))
    where isCore CoreNote{} = True
          isCore _other     = False

-- | Extract debug data from a procedure
cmmProcDebug :: ModLocation -> [RawCmmDecl] -> (i -> Bool)
                -> [GenCmmDecl d g (ListGraph i)]
                -> [DebugBlock]
cmmProcDebug loc decls isMeta nats =
  let isProc CmmProc{} = True
      isProc _other    = False
      procs = filter isProc decls

      -- Check whether blocks were actually generated (likely, but we
      -- don't want to run into problems when late-stage optimizations
      -- for some reason remove things)
      getBlocks (CmmProc _ _ _ (ListGraph bs)) = bs
      getBlocks _other                         = []
      allMeta (BasicBlock _ instrs) = all isMeta instrs
      natBlockMap :: LabelMap Int
      natBlockMap = mapFromList $ flip zip [0..] $ map blockId $ filter (not . allMeta) $
                    concatMap getBlocks nats

      -- Combined maps for all procs
      entryMap :: LabelMap RawCmmDecl
      entryMap = mapFromList $ map (\p@(CmmProc _ _ _ g) -> (g_entry g, p)) procs

      -- Find a procedure's stack offset
      stackOff :: [CmmNode O O] -> Maybe Int
      stackOff []                     = Nothing
      stackOff (CmmUnwind Sp so : _)  = case evalCmmExpr so of
                                          (Just Sp, o) -> Just $! o
                                          (_      , _) -> Nothing
      stackOff (_               : xs) = stackOff xs
      blockMid b = let (_, mid, _) = blockSplit b
                   in blockToList mid

      -- Combined map of source ticks for all blocks
      blockSrc = mapUnions $ map (snd . findGoodSourceTicks loc) procs

      -- Info tables
      infos = mapUnions $ map (\(CmmProc i _ _ _) -> i) procs
      hasInfoTable l = l `mapMember` infos

      blockMap = mapUnions $ map (\(CmmProc _ _ _ g) -> toBlockMap g) procs
      dbgBlockMap = mapMapWithKey mkDbgBlock blockMap
      mkDbgBlock l b =
        let ticks  = blockTicks b
            prc    = mapLookup l entryMap
        in seqList ticks $
           DebugBlock { dblProcedure    = isJust prc
                      , dblLabel        = l
                      , dblCLabel       = case prc of
                          Just (CmmProc infos el _ _) | Just (Statics il _) <- mapLookup l infos
                                        -> il
                            | otherwise -> el
                          _otherwise    -> blockLbl l
                      , dblHasInfoTbl   = hasInfoTable l
                      , dblTicks        = ticks
                      , dblPosition     = mapLookup l natBlockMap
                      , dblStackOff     = stackOff $ blockMid b
                      , dblSourceTick   = mapLookup l blockSrc
                      , dblBlocks       = mapMaybe (flip mapLookup dbgBlockMap) $ blockContexts b
                      }

      -- Find all blocks that are not in the context of another
      topLevelBlocks :: LabelSet
      topLevelBlocks = mapFold removeNested (setFromList $ mapKeys dbgBlockMap) dbgBlockMap
      removeNested dbg lbls = lbls `setDifference` setFromList (map dblLabel $ dblBlocks dbg)

  in mapMaybe (flip mapLookup dbgBlockMap) $ setElems topLevelBlocks

-- | Very limited evaluation of constant Cmm expressions - we assume
-- it must reduce to something like "reg + off".
evalCmmExpr :: CmmExpr -> (Maybe GlobalReg, Int)
evalCmmExpr (CmmLit (CmmInt i _))       = (Nothing, fromIntegral i)
evalCmmExpr (CmmRegOff (CmmGlobal g) i) = (Just g,  i)
evalCmmExpr (CmmReg (CmmGlobal g))      = (Just g,  0)
evalCmmExpr e@(CmmMachOp op [e1, e2])
  = let (r1, o1) = evalCmmExpr e1
        (r2, o2) = evalCmmExpr e2
    in ( case (r1, r2) of
            (Just _, Just _) -> pprPanic "Unwind expressions can only use one register!" (pprExpr e)
            (Nothing, x    ) -> x
            (x     , _     ) -> x
       , case op of
            MO_Add{} -> o1 + o2
            MO_Sub{} -> o1 - o2
            MO_Mul{} -> o1 * o2
            _other   -> pprPanic "Unsupported operator in unwind expression!" (pprExpr e)
       )
evalCmmExpr e
  = pprPanic "Unsupported unwind expression!" (ppr e)

-- | Put a string C-style - null-terminated. We assume that the string
-- is ASCII.
--
-- This could well be subject to change in future...
putString :: BinHandle -> String -> IO ()
putString bh str = do
  mapM_ (putByte bh . fromIntegral . ord) str
  putByte bh 0

putModule :: BinHandle -> DynFlags -> DebugModule -> IO ()
putModule bh dflags (DebugModule package mod_loc blocks)  = do
  putEvent bh EVENT_DEBUG_MODULE $ do
    putString bh $ packageIdString package
    putString bh $ fromMaybe "???" $ ml_hs_file mod_loc
  foldM (putBlock bh dflags maxBound) (0, emptyUFM) blocks
    >> return ()

type BlockId = Word16

putBlock :: BinHandle -> DynFlags -> BlockId -> (BlockId, CoreMap) -> DebugBlock
         -> IO (BlockId, CoreMap)
putBlock bh dflags pid (bid, coreDone) block = do
  -- Put sub-blocks
  (bid', coreDoneSub) <- foldM (putBlock bh dflags bid) (bid+1, emptyUFM) (dblBlocks block)
  -- Write our own data
  putEvent bh EVENT_DEBUG_PROCEDURE $ do
    put_ bh bid
    put_ bh pid
    let showSDocC = flip (renderWithStyle dflags) (mkCodeStyle CStyle)
    putString bh $ showSDocC $ ppr (dblCLabel block)
  -- Write annotations.
  coreDoneBlock <- foldM (putAnnotEvent bh dflags coreDoneSub) emptyUFM (dblTicks block)
  return (bid', coreDone `unionCoreMap` coreDoneSub `unionCoreMap` coreDoneBlock)

putAnnotEvent :: BinHandle -> DynFlags -> CoreMap -> CoreMap -> RawTickish -> IO CoreMap
putAnnotEvent bh _ _ coreDone (SourceNote ss names _) = do
  putEvent bh EVENT_DEBUG_SOURCE $ do
    put_ bh $ encLoc $ srcSpanStartLine ss
    put_ bh $ encLoc $ srcSpanStartCol ss
    put_ bh $ encLoc $ srcSpanEndLine ss
    put_ bh $ encLoc $ srcSpanEndCol ss
    putString bh $ unpackFS $ srcSpanFile ss
    putString bh names
  return coreDone
 where encLoc x = fromIntegral x :: Word16

putAnnotEvent bh dflags coreDoneSub coreDone (CoreNote lbl con corePtr)
  -- This piece of core was already covered earlier in this block?
  | not $ (lbl, con) `elemCoreMap` coreDone
  = putEvent bh EVENT_DEBUG_CORE $ do
      putString bh $ showSDocDump dflags $ ppr lbl
      putString bh $ case con of
        DEFAULT -> ""
        _       -> showSDoc dflags $ ppr con
      -- Emit core, leaving out (= referencing) any core pieces
      -- that were emitted from sub-blocks
      doneNew <- case corePtr of
        ExprPtr core -> putCoreExpr bh dflags coreDoneSub core
        AltPtr  alt  -> putCoreAlt bh dflags coreDoneSub alt
      return $ addToCoreMap lbl con (coreDone `unionCoreMap` doneNew)

putAnnotEvent _ _ _ coreDone _ = return coreDone

-- | Generates debug data into a buffer
debugWriteEventlog :: DynFlags -> DebugModule -> IO (Int, ForeignPtr Word8)
debugWriteEventlog dflags mod = do

  -- Write data into a binary memory handle
  bh <- openBinMem $ 1024 * 1024
  putModule bh dflags mod
  getBinMemBuf bh

-- | Constants for core binary representation
coreMisc, coreApp, coreRef, coreLam, coreLet, coreCase, coreAlt :: Word8
coreMisc = 0
coreApp  = 1
coreRef  = 2
coreLam  = 3
coreLet  = 4
coreCase = 5
coreAlt  = 6

putCoreExpr :: BinHandle -> DynFlags -> CoreMap -> CoreExpr -> IO CoreMap
putCoreExpr bh dflags bs (App e1 e2) = do
  put_ bh coreApp
  d1 <- putCoreExpr bh dflags bs e1
  d2 <- putCoreExpr bh dflags bs e2
  return $ d1 `unionCoreMap` d2
putCoreExpr bh dflags bs (Lam b e) = do
  put_ bh coreLam
  putString bh $ showSDoc dflags $ ppr b
  putString bh $ showSDoc dflags $ ppr $ varType b
  putCoreExpr bh dflags bs e
putCoreExpr bh dflags bs (Let es e) = do
  put_ bh coreLet
  d1 <- putCoreLet bh dflags bs es
  d2 <- putCoreExpr bh dflags bs e
  return $ d1 `unionCoreMap` d2
putCoreExpr bh dflags bs (Case expr bind _ alts) = do
  put_ bh coreCase
  d <- putCoreExpr bh dflags bs expr
  putString bh $ showSDoc dflags $ ppr bind
  putString bh $ showSDoc dflags $ ppr $ varType bind
  put_ bh (fromIntegral (length alts) :: Word16)
  fmap (foldr unionCoreMap d) $
    forM alts $ \alt@(a, _, _) ->
      checkCoreRef bh dflags bs (bind, a) $
        putCoreAlt bh dflags bs alt
putCoreExpr bh dflags bs (Cast e _) = putCoreExpr bh dflags bs e
putCoreExpr bh dflags bs (Tick _ e) = putCoreExpr bh dflags bs e
-- All other elements are supposed to have a simple "pretty printed"
-- representation that we can simply output verbatim.
putCoreExpr bh dflags _ other = do
  put_ bh coreMisc
  putString bh $ showSDoc dflags $ ppr other
  return emptyUFM

putCoreAlt :: BinHandle -> DynFlags -> CoreMap -> CoreAlt -> IO CoreMap
putCoreAlt bh dflags bs (a,binds,e) = do
  put_ bh coreAlt
  putString bh $ case a of
    DEFAULT -> ""
    _       -> showSDoc dflags $ ppr a
  put_ bh (fromIntegral (length binds) :: Word16)
  forM_ binds $ \b -> do
    putString bh . showSDoc dflags . ppr $ b
    putString bh . showSDoc dflags . ppr . varType $ b
  putCoreExpr bh dflags bs e

putCoreLet :: BinHandle -> DynFlags -> CoreMap -> CoreBind -> IO CoreMap
putCoreLet bh dflags bs (NonRec b e) = do
  put_ bh (1 :: Word16) -- could use 0 to mark non-recursive case?
  putString bh $ showSDoc dflags $ ppr b
  putString bh $ showSDoc dflags $ ppr $ varType b
  checkCoreRef bh dflags bs (b, DEFAULT) $
    putCoreExpr bh dflags bs e
putCoreLet bh dflags bs (Rec ps) = do
  put_ bh (fromIntegral (length ps) :: Word16)
  fmap (foldr unionCoreMap emptyUFM) $
    forM ps $ \(b, e) -> do
      putString bh $ showSDoc dflags $ ppr b
      putString bh $ showSDoc dflags $ ppr $ varType b
      checkCoreRef bh dflags bs (b, DEFAULT) $
        putCoreExpr bh dflags bs e

-- | Generate reference to core piece that was output elsewhere... Or
-- proceed with given code otherwise.
checkCoreRef :: BinHandle -> DynFlags -> CoreMap -> (Var, AltCon) -> IO CoreMap -> IO CoreMap
checkCoreRef bh dflags bs (b,a) code
  | (b,a) `elemCoreMap` bs  = do
      put_ bh coreRef
      putString bh $ showSDocDump dflags $ ppr b
      putString bh $ case a of
        DEFAULT -> ""
        _       -> showSDoc dflags $ ppr a
      return emptyUFM
  | otherwise = fmap (addToCoreMap b a) code
