
-----------------------------------------------------------------------------
--
-- Debugging data
--
-- Association of debug data on the Cmm level, with methods to encode it in
-- event log format for later inclusion in profiling event logs.
--
-----------------------------------------------------------------------------

module Debug (

  TickMapEntry(..), TickMap,
  Tickish(..), -- reexported

  pprTickMap, getTicksByParent, getInstrId,

  debugWriteEventlog

  ) where

import Binary
import CLabel
import DynFlags
import Platform
import Module
import CoreSyn
import Outputable
import UniqFM
import SrcLoc
import FastString    ( unpackFS, sLit )
import Var

import Control.Monad ( forM_ )

import Data.Word
import Data.Maybe
import Data.Map as M ( Map, elems, lookup, split, size )
import Data.Char     ( ord )

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
        = pre <> ppr (timLabel tim) <+> ppr (timTicks tim)
          $$ nest 3 (lvl (Just tim) (ptext (sLit "> ")))
  in lvl Nothing empty

-- | Gets child ticks of a tick map entry. If @Nothing@ is passed,
-- returns all top-level tick map entries.
--
-- Note this is not very efficient.
getTicksByParent :: TickMap -> Maybe TickMapEntry -> [TickMapEntry]
getTicksByParent tick_map tim = filter ((==tim) . timParent) $ M.elems tick_map

-- | Instrumentation number is the position in the tick map.
--
-- Note this has, in fact, O(log n) complexity due to using Data.Map
-- instead of Data.IntMap/UniqFM.
getInstrId :: TickMap -> TickMapEntry -> Int
getInstrId tick_map tim = M.size low
  where (low, _high) = M.split (timLabel tim) tick_map

-- | Packs the given static value into a (variable-length) event-log
-- packet.
putEvent :: BinHandle -> Word8 -> IO () -> IO ()
putEvent bh id cts = catchSize bh 0x10000 wrap omit
 where wrap = do
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
       omit = return ()

-- | Puts an alternate version if the first one is bigger than the
-- given limit.
--
-- This is a pretty crude way of handling oversized
-- packets... Can't think of a better way right now though.
catchSize :: BinHandle -> Int -> IO () -> IO () -> IO ()
catchSize bh limit cts1 cts2 = do

  -- Put contents, note how much size it uses
  start <- tellBin bh :: IO (Bin ())
  cts1
  end <- tellBin bh

  -- Seek back and put second version if size is over limit
  if (end `diffBin` start) >= limit
    then do seekBin bh start
            cts2
    else return ()

-- | Holds identities of core pieces we have decided to output
type CoreMap = UniqFM [AltCon]

mkCoreMap :: [Tickish()] -> CoreMap
mkCoreMap = listToUFM_C (++) . map mkEntry
  where mkEntry (CoreNote bind con _) = (bind, [con])
        mkEntry _                     = error "mkCoreMap: Non-core tickish!"

elemCoreMap :: (Var, AltCon) -> CoreMap -> Bool
elemCoreMap (bind, con) m = case lookupUFM m bind of
  Just cs -> con `elem` cs
  Nothing -> False

-- | Put a string C-style - null-terminated. We assume that the string
-- is ASCII.
--
-- This could well be subject to change in future...
putString :: BinHandle -> String -> IO ()
putString bh str = do
  mapM_ (putByte bh . fromIntegral . ord) str
  putByte bh 0

putModuleEvent :: BinHandle -> PackageId -> ModLocation -> IO ()
putModuleEvent bh package mod_loc =
  putEvent bh EVENT_DEBUG_MODULE $ do
    putString bh $ packageIdString package
    putString bh $ fromMaybe "???" $ ml_hs_file mod_loc

putProcedureEvent :: BinHandle -> DynFlags -> TickMap -> TickMapEntry -> CLabel -> IO ()
putProcedureEvent bh dflags tick_map tim lbl =
  putEvent bh EVENT_DEBUG_PROCEDURE $ do
    put_ bh $ encInstr $ Just tim
    put_ bh $ encInstr $ timParent tim
    putString bh $ showSDocC  $ ppr lbl
 where encInstr tim = case fmap (getInstrId tick_map) tim of
         Just i  -> fromIntegral i
         Nothing -> 0xffff :: Word16
       showSDocC = flip (renderWithStyle dflags) (mkCodeStyle CStyle)

putAnnotEvent :: BinHandle -> DynFlags -> CoreMap -> Maybe (Tickish ()) -> Tickish () -> IO ()
putAnnotEvent bh _ _ _ (SourceNote ss names _) =
  putEvent bh EVENT_DEBUG_SOURCE $ do
    put_ bh $ encLoc $ srcSpanStartLine ss
    put_ bh $ encLoc $ srcSpanStartCol ss
    put_ bh $ encLoc $ srcSpanEndLine ss
    put_ bh $ encLoc $ srcSpanEndCol ss
    putString bh $ unpackFS $ srcSpanFile ss
    putString bh names
 where encLoc x = fromIntegral x :: Word16

putAnnotEvent bh dflags bnds mbind c@(CoreNote lbl con corePtr)
  | mbind == Just c =
      putEvent bh EVENT_DEBUG_CORE $ do
        putString bh $ showSDocDump dflags $ ppr lbl
        putString bh $ case con of
          DEFAULT -> ""
          _       -> showSDoc dflags $ ppr con
        case corePtr of
          ExprPtr core -> putCoreExpr bh dflags bnds core
          AltPtr  alt  -> putCoreAlt bh dflags bnds alt

putAnnotEvent _ _ _ _ _ = return ()

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
getMainCoreBind :: [Tickish ()] -> Maybe (Tickish ())
getMainCoreBind (c@CoreNote{}:_) = Just c
getMainCoreBind (_:xs)           = getMainCoreBind xs
getMainCoreBind _                = Nothing

-- | Generates debug data into a buffer
debugWriteEventlog ::
  DynFlags -> ModLocation
  -> TickMap
  -> [(CLabel, CLabel)]  -- ^ (label in cmm/tick map, code label in assembler)
  -> IO (Int, ForeignPtr Word8)
debugWriteEventlog dflags mod_loc tick_map lbls = do

  -- Collect all bindings that we want to output core pieces for. We
  -- will use this map to make sure that we don't output a piece of
  -- core twice (see stripCore).
  let collect tim = getMainCoreBind (timTicks tim)
      binds = mkCoreMap $ mapMaybe collect $ elems tick_map

  -- Open a binary memory handle
  bh <- openBinMem $ 1024 * 1024

  -- Put data
  putModuleEvent bh (thisPackage dflags) mod_loc
  forM_ lbls $ \(cmml, asml) ->
    case M.lookup cmml tick_map of
      Just tim -> do
        putProcedureEvent bh dflags tick_map tim asml
        let mbind = getMainCoreBind (timTicks tim)
        mapM_ (putAnnotEvent bh dflags binds mbind) (timTicks tim)
      Nothing  -> return ()

  -- Return buffer
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

putCoreExpr :: BinHandle -> DynFlags -> CoreMap -> CoreExpr -> IO ()
putCoreExpr bh dflags bs (App e1 e2) = do
  put_ bh coreApp
  putCoreExpr bh dflags bs e1
  putCoreExpr bh dflags bs e2
putCoreExpr bh dflags bs (Lam b e) = do
  put_ bh coreLam
  putString bh $ showSDoc dflags $ ppr b
  putCoreExpr bh dflags bs e
putCoreExpr bh dflags bs (Let es e) = do
  put_ bh coreLet
  putCoreLet bh dflags bs es
  putCoreExpr bh dflags bs e
putCoreExpr bh dflags bs (Case expr bind ty alts) = do
  put_ bh coreCase
  putCoreExpr bh dflags bs expr
  putString bh $ showSDoc dflags $ ppr bind
  putString bh $ showSDoc dflags $ ppr ty
  put_ bh (fromIntegral (length alts) :: Word16)
  forM_ alts $ \alt@(a, _, _) -> checkCoreRef bh dflags bs (bind, a) $
    putCoreAlt bh dflags bs alt
putCoreExpr bh dflags bs (Cast e _) = putCoreExpr bh dflags bs e
putCoreExpr bh dflags bs (Tick _ e) = putCoreExpr bh dflags bs e
-- All other elements are supposed to have a simple "pretty printed"
-- representation that we can simply output verbatim.
putCoreExpr bh dflags _ other = do
  put_ bh coreMisc
  putString bh $ showSDoc dflags $ ppr other

putCoreAlt :: BinHandle -> DynFlags -> CoreMap -> CoreAlt -> IO ()
putCoreAlt bh dflags bs (a,b,e) = do
  put_ bh coreAlt
  putString bh $ case a of
    DEFAULT -> ""
    _       -> showSDoc dflags $ ppr a
  put_ bh (fromIntegral (length b) :: Word16)
  mapM_ (putString bh . showSDoc dflags . ppr) b
  putCoreExpr bh dflags bs e

putCoreLet :: BinHandle -> DynFlags -> CoreMap -> CoreBind -> IO ()
putCoreLet bh dflags bs (NonRec b e) = do
  put_ bh (1 :: Word16) -- could use 0 to mark non-recursive case?
  putString bh $ showSDoc dflags $ ppr b
  putString bh $ showSDoc dflags $ ppr $ varType b
  checkCoreRef bh dflags bs (b, DEFAULT) $
    putCoreExpr bh dflags bs e
putCoreLet bh dflags bs (Rec ps) = do
  put_ bh (fromIntegral (length ps) :: Word16)
  forM_ ps $ \(b, e) -> do
    putString bh $ showSDoc dflags $ ppr b
    putString bh $ showSDoc dflags $ ppr $ varType b
    checkCoreRef bh dflags bs (b, DEFAULT) $
      putCoreExpr bh dflags bs e

-- | Generate reference to core piece that was output elsewhere... Or
-- proceed with given code otherwise.
checkCoreRef :: BinHandle -> DynFlags -> CoreMap -> (Var, AltCon) -> IO () -> IO ()
checkCoreRef bh dflags bs (b,a) code
  | (b,a) `elemCoreMap` bs  = do
      put_ bh coreRef
      putString bh $ showSDocDump dflags $ ppr b
      putString bh $ case a of
        DEFAULT -> ""
        _       -> showSDoc dflags $ ppr a
  | otherwise =
      code
