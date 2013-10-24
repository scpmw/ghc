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

  DebugBlock(..), dblIsEntry,
  UnwindTable, UnwindExpr(..),
  cmmDebugGen,
  cmmDebugLink,
  debugToMap,
  writeDebugToEventlog

  ) where

import Binary
import BlockId         ( blockLbl, BlockEnv )
import CLabel
import Cmm
import CmmUtils
import CoreSyn
import DynFlags
import FastString      ( nilFS, mkFastString, unpackFS )
import Module
import Outputable
import PprCore         ()
import PprCmmExpr      ( pprExpr )
import SrcLoc
import UniqFM
import Var             ( Var, varType )

import Compiler.Hoopl

import Control.Monad   ( foldM, forM, forM_, void )

import Data.Char     ( ord)
import Data.Maybe
import Data.List     ( find, minimumBy )
import Data.Ord      ( comparing )
import qualified Data.Map as Map
import Data.Word     ( Word8, Word16 )

import Foreign.ForeignPtr

#define EVENTLOG_CONSTANTS_ONLY
#include "../../includes/rts/EventLogFormat.h"

-- | Debug information about a block of code. Context is encoded through nesting.
data DebugBlock =
  DebugBlock
  { dblProcedure  :: !Label              -- ^ Entry label of containing producedure
  , dblLabel      :: !Label              -- ^ Hoopl label
  , dblCLabel     :: !CLabel             -- ^ Output label
  , dblHasInfoTbl :: !Bool               -- ^ Has an info table?
  , dblTicks      :: ![RawTickish]       -- ^ Ticks defined in this block
  , dblSourceTick :: !(Maybe RawTickish) -- ^ Best source tick covering this block
  , dblPosition   :: !(Maybe Int)        -- ^ Output position relative to other blocks in proc.
                                         --   @Nothing@ means the block has been optimized out.
  , dblUnwind     :: !UnwindTable        -- ^ Unwind information
  , dblBlocks     :: ![DebugBlock]       -- ^ Nested blocks
  }

dblIsEntry :: DebugBlock -> Bool
dblIsEntry blk = dblProcedure blk == dblLabel blk

instance Outputable DebugBlock where
  ppr blk = (if dblHasInfoTbl blk
             then if dblProcedure blk == dblLabel blk
                  then text "proc "
                  else text "pp-blk "
             else text "blk ") <>
            ppr (dblLabel blk) <+> parens (ppr (dblCLabel blk)) <+>
            (maybe empty ppr (dblSourceTick blk)) <+>
            (maybe empty ppr (find isCore (dblTicks blk))) <+>
            (maybe (text "removed") ((text "pos " <>) . ppr) (dblPosition blk)) <+>
            pprUwMap (dblUnwind blk) $$
            (if null (dblBlocks blk) then empty else ppr (dblBlocks blk))
    where isCore CoreNote{} = True
          isCore _other     = False
          pprUw (g, expr) = ppr g <> char '=' <> ppr expr
          pprUwMap = braces . hsep . punctuate comma . map pprUw . Map.toList

-- | Extract debug data from a group of procedures
cmmDebugGen :: ModLocation -> RawCmmGroup -> [DebugBlock]
cmmDebugGen loc decls =
  let isProc CmmProc{} = True
      isProc _other    = False
      procs = filter isProc decls

      -- Map of blocks to the procedure they were declared in
      procMap :: LabelMap RawCmmDecl
      procMap = mapFromList $ concatMap procMappings procs
      procMappings p = [ (entryLabel b, p) | CmmProc _ _ _ g <- [p], b <- toBlockList g]

      -- Info tables
      infos = mapUnions $ map (\(CmmProc i _ _ _) -> i) procs
      hasInfoTable l = l `mapMember` infos

      -- Combined block and context maps
      blockMap :: BlockEnv CmmBlock
      blockMap = mapUnions $ map (\(CmmProc _ _ _ g) -> toBlockMap g) procs
      contextMap :: BlockEnv Label
      contextMap = mapUnions $ map (\(CmmProc _ _ _ g) -> getContextMap g) procs

      topBlocks :: BlockEnv CmmBlock
      topBlocks = blockMap `mapDifference` mapMap (const undefined) contextMap -- ugly

      -- Helper: Best source ticks from a list
      --
      -- This is somewhat arbitrary -- we select the first source
      -- span, while preferring source ticks from the same source
      -- file.  Furthermore, dumps take priority (if we generated one,
      -- we probably want debug information to refer to it).
      bestSrcTick = minimumBy (comparing rangeRating)
      rangeRating (SourceNote span _ _)
        | isDumpSrcSpan span           = 0
        | srcSpanFile span == thisFile = 1
        | otherwise                    = 2 :: Int
      rangeRating _non_source_note     = error "rangeRating"
      thisFile = maybe nilFS mkFastString $ ml_hs_file loc
      isSourceTick SourceNote {} = True
      isSourceTick _             = False

      mkDbgBlock cstick cproc lbl block
        -- Make sure we never have a block in the context tree that's
        -- not a direct or indirect child of its procedure entry
        -- block. This might fail for two reasons:
        -- * cproc is Nothing, in which case this must be a naked
        --   block without context. This is probably CodeGen
        --   forgetting to generate a suitable CmmContext directive
        --   for a new block.
        -- * Otherwise, the CmmContext led us to an internal block
        --   from another procedure. While this is not fatal at this
        --   point, it's just no good idea to refer to internal labels
        --   from another procedure.
        | procEntry /= lbl && Just procEntry /= cproc
        = pprPanic "cmmDebugGen: Block has missing or inconsistent procedure context! "
          (ppr lbl <> text ": expected " <> ppr procEntry <> text ", got " <> ppr cproc)
        | otherwise
        = DebugBlock { dblProcedure    = procEntry
                     , dblLabel        = lbl
                     , dblCLabel       =
                         if g_entry graph == lbl
                         then case mapLookup lbl infos of
                                Just (Statics il _) -> il
                                _other              -> el
                         else blockLbl lbl
                     , dblHasInfoTbl   = hasInfoTable lbl
                     , dblTicks        = ticks
                     , dblPosition     = Nothing -- updated later by cmmDebugLink
                     , dblUnwind       = extractUnwind block
                     , dblSourceTick   = stick
                     , dblBlocks       = mapMaybe mkByLabel (blockContexts block)
                     }
        where mkByLabel l = fmap (mkDbgBlock stick (Just procEntry) l) (mapLookup l blockMap)
              Just (CmmProc infos el _ graph) = mapLookup lbl procMap
              procEntry = g_entry graph
              -- A source tick scopes over nested blocks as long as
              -- they don't have source ticks of their own, which
              -- otherwise take priority.
              ticks  = blockTicks block
              sticks = filter isSourceTick ticks
              stick  = if null sticks then cstick else Just $! bestSrcTick sticks

  in map (uncurry (mkDbgBlock Nothing Nothing)) $ mapToList topBlocks

-- | Sets position fields in the debug block tree according to native
-- generated code.
cmmDebugLink :: (i -> Bool) -> GenCmmGroup d g (ListGraph i)
                -> [DebugBlock] -> [DebugBlock]
cmmDebugLink isMeta nats blocks =
  let -- Find order in which procedures will be generated by the
      -- back-end (important for DWARF).
      --
      -- Note that we might encounter blocks that are missing or only
      -- consist of meta instructions -- we will declare them missing,
      -- which will prevent debug data generation without messing up
      -- the block hierarchy.
      getBlocks (CmmProc _ _ _ (ListGraph bs)) = bs
      getBlocks _other                         = []
      allMeta (BasicBlock _ instrs) = all isMeta instrs
      blockPosition :: LabelMap Int
      blockPosition = mapFromList $ flip zip [0..] $ map blockId $ filter (not . allMeta) $
                      concatMap getBlocks nats

      link block = block { dblPosition = mapLookup (dblLabel block) blockPosition
                         , dblBlocks   = map link (dblBlocks block)
                         }
   in map link blocks

-- | Converts debug blocks into a label map for easier lookups
debugToMap :: [DebugBlock] -> LabelMap DebugBlock
debugToMap = mapUnions . map go
   where go b = mapInsert (dblLabel b) b $ mapUnions $ map go (dblBlocks b)

-- | Maps registers to expressions that yield their "old" values
-- further up the stack. Most interesting for the stack pointer Sp,
-- but might be useful to document saved registers, too.
type UnwindTable = Map.Map GlobalReg UnwindExpr

-- | Expressions, used for unwind information
data UnwindExpr = UwConst Int                   -- ^ literal value
                | UwReg GlobalReg Int           -- ^ register plus offset
                | UwDeref UnwindExpr            -- ^ pointer dereferencing
                | UwPlus UnwindExpr UnwindExpr
                | UwMinus UnwindExpr UnwindExpr
                | UwTimes UnwindExpr UnwindExpr
                deriving (Eq)

instance Outputable UnwindExpr where
  pprPrec _ (UwConst i)     = ppr i
  pprPrec _ (UwReg g 0)     = ppr g
  pprPrec p (UwReg g x)     = pprPrec p (UwPlus (UwReg g 0) (UwConst x))
  pprPrec _ (UwDeref e)     = char '*' <> pprPrec 3 e
  pprPrec p (UwPlus e0 e1)  | p <= 0
                            = pprPrec 0 e0 <> char '+' <> pprPrec 0 e1
  pprPrec p (UwMinus e0 e1) | p <= 0
                            = pprPrec 1 e0 <> char '-' <> pprPrec 1 e1
  pprPrec p (UwTimes e0 e1) | p <= 1
                            = pprPrec 2 e0 <> char '*' <> pprPrec 2 e1
  pprPrec _ other           = parens (pprPrec 0 other)

extractUnwind :: CmmBlock -> UnwindTable
extractUnwind b = go $ blockToList mid
  where (_, mid, _) = blockSplit b
        go :: [CmmNode O O] -> UnwindTable
        go []       = Map.empty
        go (x : xs) = case x of
          CmmUnwind g so -> Map.insert g (toUnwindExpr so) $! go xs
          CmmTick {}     -> go xs
          CmmContext {}  -> go xs
          _other         -> Map.empty -- TODO: Unwind statements after actual instructions

-- | Conversion of Cmm expressions to unwind expressions. We check for
-- unsupported operator usages and simplify the expression as far as
-- possible.
toUnwindExpr :: CmmExpr -> UnwindExpr
toUnwindExpr (CmmLit (CmmInt i _))       = UwConst (fromIntegral i)
toUnwindExpr (CmmRegOff (CmmGlobal g) i) = UwReg g i
toUnwindExpr (CmmReg (CmmGlobal g))      = UwReg g 0
toUnwindExpr (CmmLoad e _)               = UwDeref (toUnwindExpr e)
toUnwindExpr e@(CmmMachOp op [e1, e2])   =
  case (op, toUnwindExpr e1, toUnwindExpr e2) of
    (MO_Add{}, UwReg r x, UwConst y) -> UwReg r (x + y)
    (MO_Sub{}, UwReg r x, UwConst y) -> UwReg r (x - y)
    (MO_Add{}, UwConst x, UwReg r y) -> UwReg r (x + y)
    (MO_Add{}, UwConst x, UwConst y) -> UwConst (x + y)
    (MO_Sub{}, UwConst x, UwConst y) -> UwConst (x - y)
    (MO_Mul{}, UwConst x, UwConst y) -> UwConst (x * y)
    (MO_Add{}, u1,        u2       ) -> UwPlus u1 u2
    (MO_Sub{}, u1,        u2       ) -> UwMinus u1 u2
    (MO_Mul{}, u1,        u2       ) -> UwTimes u1 u2
    _otherwise                       -> pprPanic "Unsupported operator in unwind expression!" (pprExpr e)
toUnwindExpr e
  = pprPanic "Unsupported unwind expression!" (ppr e)

-- | Generates debug data into a buffer
writeDebugToEventlog :: DynFlags -> ModLocation -> [DebugBlock] -> IO (Int, ForeignPtr Word8)
writeDebugToEventlog dflags mod_loc blocks = do

  -- Write data into a binary memory handle
  bh <- openBinMem $ 1024 * 1024
  putEvent bh EVENT_DEBUG_MODULE $ do
    putString bh $ packageIdString (thisPackage dflags)
    putString bh $ fromMaybe "???" $ ml_hs_file mod_loc
  void $ foldM (putBlock bh dflags maxBound) (0, emptyUFM) blocks
  getBinMemBuf bh

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

type BlockId = Word16

putBlock :: BinHandle -> DynFlags -> BlockId -> (BlockId, CoreMap) -> DebugBlock
         -> IO (BlockId, CoreMap)
putBlock bh dflags pid (bid, coreDone) block = do
  -- Put sub-blocks
  (bid', coreDoneSub) <- foldM (putBlock bh dflags bid) (bid+1, emptyUFM) (dblBlocks block)
  -- Write our own data
  putEvent bh EVENT_DEBUG_BLOCK $ do
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

putAnnotEvent bh dflags coreDoneSub coreDone (CoreNote lbl corePtr)
  -- This piece of core was already covered earlier in this block?
  | not $ (lbl, exprPtrCons corePtr) `elemCoreMap` coreDone
  = putEvent bh EVENT_DEBUG_CORE $ do
      putString bh $ showSDocDump dflags $ ppr lbl
      -- Emit core, leaving out (= referencing) any core pieces
      -- that were emitted from sub-blocks
      doneNew <- case corePtr of
        ExprPtr core -> putCoreExpr bh dflags coreDoneSub core
        AltPtr  alt  -> putCoreAlt bh dflags coreDoneSub alt
      return $ addToCoreMap lbl (exprPtrCons corePtr) (coreDone `unionCoreMap` doneNew)

putAnnotEvent _ _ _ coreDone _ = return coreDone

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

-- | Put a C-style string (null-terminated). We assume that the string
-- is ASCII.
--
-- This could well be subject to change in future...
putString :: BinHandle -> String -> IO ()
putString bh str = do
  mapM_ (putByte bh . fromIntegral . ord) str
  putByte bh 0

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
