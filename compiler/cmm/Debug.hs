
module Debug (

  TickMapEntry(..), TickMap,
  Tickish(..), -- reexported

  pprTickMap, getTicksByParent, getInstrId,

  debugWriteEventlog

  ) where

import Binary
import CLabel
import Platform
import Module
import CoreSyn
import PprCore      ( pprCoreAlt )
import Outputable
import Var          ( Var( varName ) )
import UniqSet
import SrcLoc
import FastString   ( unpackFS, mkFastString )
import Literal      ( Literal( MachStr ) )
import FastString   ( sLit )

import Control.Monad ( forM_ )

import Data.Word
import Data.Maybe
import Data.Map as M ( Map, elems, lookup, split, size )
import Data.Char    ( ord )

import Foreign.ForeignPtr

#define EVENTLOG_CONSTANTS_ONLY
#include "../../includes/rts/EventLogFormat.h"

data TickMapEntry = TickMapEntry {
  timLabel :: CLabel,              -- ^ Label of this entry
  timParent :: Maybe TickMapEntry, -- ^ Parent context, if any
  timTicks :: [Tickish ()]         -- ^ Debug ticks found in the context
  }
type TickMap = Map CLabel TickMapEntry

instance Eq TickMapEntry where
  tim1 == tim2  = timLabel tim1 == timLabel tim2

-- | Shows the tick map in a nice tree form
pprTickMap :: Platform -> TickMap -> SDoc
pprTickMap p tick_map =
  let lvl p pre = vcat $ map (pp pre) $ getTicksByParent tick_map p
      pp pre tim
        = pre <> pprPlatform p (timLabel tim) <+> ppr (timTicks tim)
          $$ nest 3 (lvl (Just tim) (ptext (sLit "> ")))
  in lvl Nothing empty

-- | Gets child ticks of a tick map entry. If @Nothing@ is passed,
-- returns all top-level tick map entryies.
--
-- Note this is not very eficient.
getTicksByParent :: TickMap -> Maybe TickMapEntry -> [TickMapEntry]
getTicksByParent tick_map tim = filter ((==tim) . timParent) $ M.elems tick_map

-- | Instrumentation number is the position in the tick map.
--
-- Note that has, in fact, O(log n) complexity due to using Data.Map
-- instead of Data.IntMap/UniqFM.
getInstrId :: TickMap -> TickMapEntry -> Int
getInstrId tick_map tim = M.size low
  where (low, _high) = M.split (timLabel tim) tick_map

-- | Packs the given static value into a (variable-length) event-log
-- packet.
putEvent :: BinHandle -> Word8 -> IO () -> IO ()
putEvent bh id cts = do
  put_ bh id
  -- Put placeholder for size
  sizePos <- put bh (0 :: Word16)
  -- Put contents
  cts
  -- Put final size
  endPos <- tellBin bh
  putAt bh sizePos $ fromIntegral $ (endPos `diffBin` sizePos) - 2
  -- Seek back
  seekBin bh endPos

-- | Put a string C-style - null-terminated. We assume that the string
-- is ASCII.
--
-- This could well be subject to change in future...
putString :: BinHandle -> String -> IO ()
putString bh str = do
  mapM_ (putByte bh . fromIntegral . ord) str
  putByte bh 0

putModuleEvent :: BinHandle -> ModLocation -> IO ()
putModuleEvent bh mod_loc =
  putEvent bh EVENT_DEBUG_MODULE $ do
    putString bh $ fromMaybe "???" $ ml_hs_file mod_loc

putProcedureEvent :: BinHandle -> Platform -> TickMap -> TickMapEntry -> CLabel -> IO ()
putProcedureEvent bh platform tick_map tim lbl =
  putEvent bh EVENT_DEBUG_PROCEDURE $ do
    put_ bh $ encInstr $ Just tim
    put_ bh $ encInstr $ timParent tim
    putString bh $ showSDocC  $ pprCLabel platform lbl
 where encInstr tim = case fmap (getInstrId tick_map) tim of
         Just i  -> fromIntegral i
         Nothing -> 0xffff :: Word16
       showSDocC = flip renderWithStyle (mkCodeStyle CStyle)

putAnnotEvent :: BinHandle -> UniqSet Var -> Maybe Var -> Tickish () -> IO ()
putAnnotEvent bh _ _ (SourceNote ss names) =
  putEvent bh EVENT_DEBUG_SOURCE $ do
    put_ bh $ encLoc $ srcSpanStartLine ss
    put_ bh $ encLoc $ srcSpanStartCol ss
    put_ bh $ encLoc $ srcSpanEndLine ss
    put_ bh $ encLoc $ srcSpanEndCol ss
    putString bh $ unpackFS $ srcSpanFile ss
    putString bh names
 where encLoc x = fromIntegral x :: Word16

putAnnotEvent bh bnds mbind (CoreNote lbl corePtr)
  | mbind == Just lbl =
      putEvent bh EVENT_DEBUG_CORE $ do
        putString bh $ showSDocDump $ ppr lbl
        let sDocStr = take 0x8000 . showSDoc
        putString bh $ case corePtr of
          ExprPtr core -> sDocStr $ ppr $ stripCore bnds core
          AltPtr  alt  -> sDocStr $ pprCoreAlt $ stripAlt bnds alt

putAnnotEvent _ _ _ _ = return ()

-- | Get core name from tickishs. Note that we might often have many,
-- many core notes in the list, as Core2Stg annotates every point
-- where it could see code generation generating a new proc. On the
-- other hand, if codegen does its job right, many of these will
-- actually be "inlined", leaving us with rather unwieldingly
-- fine-grained core annotations.
--
-- Luckily, we know that the first core tick we find (more often than
-- not even the first tickish we have) will be one of the top-level
-- ticks. If we just ignore all with other names, we cover all
-- interesting Core without having to split everything in millions of
-- tiny core pieces.
getMainCoreBind :: [Tickish ()] -> Maybe Var
getMainCoreBind (CoreNote bnd _:_) = Just bnd
getMainCoreBind (_:xs)             = getMainCoreBind xs
getMainCoreBind _                  = Nothing

-- | Generates debug data into a buffer
debugWriteEventlog ::
  Platform -> ModLocation
  -> TickMap
  -> [(CLabel, CLabel)]  -- ^ (label in cmm/tick map, code label in assembler)
  -> IO (Int, ForeignPtr Word8)
debugWriteEventlog platform mod_loc tick_map lbls = do

  -- Collect all bindings that we want to output core pieces for. We
  -- will use this map to make sure that we don't output a piece of
  -- core twice (see stripCore).
  let collect tim = getMainCoreBind (timTicks tim)
      binds = mkUniqSet $ mapMaybe collect $ elems tick_map

  -- Open a binary memory handle
  bh <- openBinMem $ 1024 * 1024

  -- Put data
  putModuleEvent bh mod_loc
  forM_ lbls $ \(cmml, asml) ->
    case M.lookup cmml tick_map of
      Just tim -> do
        putProcedureEvent bh platform tick_map tim asml
        let mbind = getMainCoreBind (timTicks tim)
        mapM_ (putAnnotEvent bh binds mbind) (timTicks tim)
      Nothing  -> return ()

  -- Return buffer
  getBinMemBuf bh

-- | This "strips" the core of all information that's uninteresting or
-- redundant in the context of debug output. This means:
--
--  * Annotations that clutter up the view unecessarily, such as casts
--
--  * Any sub-tree of core that gets emitted seperately. In this case
--    we emit a placeholder so a program reading it can link the two
--    pieces of core together later
stripCore :: UniqSet Var -> CoreExpr -> CoreExpr
stripCore bs (App e1 e2) = App (stripCore bs e1) (stripCore bs e2)
stripCore bs (Lam b e)
  | b `elemSet` bs       = Lam b (placeholder b)
  | otherwise            = Lam b (stripCore bs e)
stripCore bs (Let es e)  = Let (stripLet bs es) (stripCore bs e)
stripCore bs (Tick _ e)  = stripCore bs e -- strip out
stripCore bs (Case e b t as)
  | b `elemSet` bs       = Case (stripCore bs e) b t [(DEFAULT,[],placeholder b)]
  | otherwise            = Case (stripCore bs e) b t (map (stripAlt bs) as)
stripCore bs (CoreSyn.Cast e _)  = stripCore bs e -- strip out
stripCore _  other       = other

stripAlt :: UniqSet Var -> CoreAlt -> CoreAlt
stripAlt bs (a, bn, e) = (a, bn, stripCore bs e)

stripLet :: UniqSet Var -> CoreBind -> CoreBind
stripLet bs (NonRec b e)
  | b `elemSet` bs       = NonRec b (placeholder b)
  | otherwise            = NonRec b (stripCore bs e)
stripLet bs (Rec ps)     = Rec (map f ps)
  where
    f (b, e)
      | b `elemSet` bs   = (b, placeholder b)
      | otherwise        = (b, stripCore bs e)

-- | Placeholder string. FIXME: This *might* collide with existing strings
placeholder :: Var -> CoreExpr
placeholder = Lit . MachStr . mkFastString .
              ("__Core__" ++) . showSDocDump . ppr . varName

elemSet :: Var -> UniqSet Var -> Bool
elemSet = elementOfUniqSet
