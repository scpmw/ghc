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
  debugToMap

  ) where

import BlockId         ( blockLbl )
import CLabel
import Cmm
import CmmUtils
import CoreSyn
import FastString      ( nilFS, mkFastString )
import Module
import Outputable
import PprCore         ()
import PprCmmExpr      ( pprExpr )
import SrcLoc
import Util

import Compiler.Hoopl

import Data.Maybe
import Data.List     ( find, minimumBy )
import Data.Ord      ( comparing )
import qualified Data.Map as Map

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
  ppr blk = (if dblProcedure blk == dblLabel blk
             then text "proc "
             else if dblHasInfoTbl blk
                  then text "pp-blk "
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

type BlockContext = (CmmBlock, RawCmmDecl, UnwindTable)

-- | Extract debug data from a group of procedures
cmmDebugGen :: ModLocation -> RawCmmGroup -> [DebugBlock]
cmmDebugGen modLoc decls = map (blocksForScope Nothing) topScopes
  where
      blockCtxs = blockContexts decls

      -- Analyse tick scope structure: Each one is either a top-level
      -- tick scope, or the child of another. Note that we are using
      -- "postfix" instead of "subset" relation here, implicitly
      -- reducing the graph to a tree.
      (topScopes, childScopes)
        = splitEithers $ map (\a -> findP a a) $ Map.keys blockCtxs
      findP tsc []                                  = Left tsc
      findP tsc (_:sc) | sc `Map.member` blockCtxs  = Right (sc, tsc)
                       | otherwise                  = findP tsc sc
      scopeMap = foldr (uncurry insertMulti) Map.empty childScopes

      -- Finding the "best" source tick is somewhat arbitrary -- we
      -- select the first source span, while preferring source ticks
      -- from the same source file.  Furthermore, dumps take priority
      -- (if we generated one, we probably want debug information to
      -- refer to it).
      bestSrcTick = minimumBy (comparing rangeRating)
      rangeRating (SourceNote span _)
        | isDumpSrcSpan span           = 0
        | srcSpanFile span == thisFile = 1
        | otherwise                    = 2 :: Int
      rangeRating _non_source_note     = error "rangeRating"
      thisFile = maybe nilFS mkFastString $ ml_hs_file modLoc

      -- Returns block tree for this scope as well as all nested
      -- scopes. Note that if there are multiple blocks in the (exact)
      -- same scope we elect one as the "branch" node and add the rest
      -- as children.
      blocksForScope cstick scope = mkBlock True (head bctxs)
        where bctxs = fromJust $ Map.lookup scope blockCtxs
              nested = fromMaybe [] $ Map.lookup scope scopeMap
              childs = map (mkBlock False) (tail bctxs) ++
                       map (blocksForScope stick) nested
              mkBlock top (block, prc, unwind)
                = DebugBlock { dblProcedure    = g_entry graph
                             , dblLabel        = label
                             , dblCLabel       = case info of
                                 Just (Statics infoLbl _)   -> infoLbl
                                 Nothing
                                   | g_entry graph == label -> entryLbl
                                   | otherwise              -> blockLbl label
                             , dblHasInfoTbl   = isJust info
                             , dblTicks        = ticks
                             , dblPosition     = Nothing -- updated in cmmDebugLink
                             , dblUnwind       = unwind
                             , dblSourceTick   = stick
                             , dblBlocks       = if top then childs else []
                             }
                where (CmmProc infos entryLbl _ graph) = prc
                      label = entryLabel block
                      info = mapLookup label infos

              -- A source tick scopes over all nested blocks. However
              -- their source ticks might take priority.
              isSourceTick SourceNote {} = True
              isSourceTick _             = False
              ticks = concatMap (blockTicks . fstOf3) bctxs
              stick = case filter isSourceTick ticks of
                []     -> cstick
                sticks -> Just $! bestSrcTick (sticks ++ maybeToList cstick)

-- | Build a map of blocks sorted by their tick scopes
--
-- This involves a pre-order traversal, as we want blocks in rough
-- control flow order (so ticks have a chance to be sorted in the
-- right order). We also use this opportunity to have blocks inherit
-- unwind information from their predecessor blocks where it is
-- lacking.
blockContexts :: RawCmmGroup -> Map.Map [CmmTickScope] [BlockContext]
blockContexts decls = Map.map reverse $ foldr walkProc Map.empty decls
  where walkProc CmmData{}                 m = m
        walkProc prc@(CmmProc _ _ _ graph) m
          | mapNull blocks = m
          | otherwise      = snd $ walkBlock prc entry Map.empty (emptyLbls, m)
          where blocks = toBlockMap graph
                entry  = [mapFind (g_entry graph) blocks]
                emptyLbls = setEmpty :: LabelSet
        walkBlock _   []             _      c            = c
        walkBlock prc (block:blocks) unwind (visited, m)
          | lbl `setMember` visited
          = walkBlock prc blocks unwind (visited, m)
          | otherwise
          = walkBlock prc blocks unwind $
            walkBlock prc succs unwind' (lbl `setInsert` visited,
                                         insertMulti scope (block, prc, unwind') m)
          where CmmEntry lbl scope = firstNode block
                unwind' = extractUnwind block `Map.union` unwind
                (CmmProc _ _ _ graph) = prc
                succs = map (flip mapFind (toBlockMap graph))
                            (successors (lastNode block))
        mapFind = mapFindWithDefault (error "contextTree: block not found!")

insertMulti :: Ord k => k -> a -> Map.Map k [a] -> Map.Map k [a]
insertMulti k v = Map.insertWith (const (v:)) k [v]

-- | Sets position fields in the debug block tree according to native
-- generated code.
cmmDebugLink :: (i -> Bool) -> GenCmmGroup d g (ListGraph i)
                -> [DebugBlock] -> [DebugBlock]
cmmDebugLink isMeta nats blocks =
  let -- Find order in which procedures will be generated by the
      -- back-end (that actually matters for DWARF generation).
      --
      -- Note that we might encounter blocks that are missing or only
      -- consist of meta instructions -- we will declare them missing,
      -- which will skip debug data generation without messing up the
      -- block hierarchy.
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

