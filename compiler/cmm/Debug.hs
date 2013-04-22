
-----------------------------------------------------------------------------
--
-- Debugging data
--
-- Association of debug data on the Cmm level, with methods to encode it in
-- event log format for later inclusion in profiling event logs.
--
-----------------------------------------------------------------------------

module Debug (

  Tickish(..), -- reexported

  DebugModule(..), DebugBlock(..),
  debugWriteEventlog

  ) where

import Binary
import CLabel
import DynFlags
import Module
import CoreSyn
import Outputable
import UniqFM
import SrcLoc
import FastString    ( unpackFS )
import Var

import Control.Monad ( forM, forM_, foldM )

import Data.Word
import Data.Maybe
import Data.Char     ( ord )

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

data DebugModule = DebugModule { dmodPackage :: PackageId
                               , dmodLocation :: ModLocation
                               , dmodBlocks :: [DebugBlock]
                               }

-- | Debug information about a block of code. Can be nested to show
-- context.
data DebugBlock = DebugBlock { dblLabel :: CLabel
                             , dblTicks :: [Tickish ()]
                             , dblBlocks :: [DebugBlock]
                             }

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
putBlock bh dflags pid (bid, coreDone) (DebugBlock lbl ticks blocks) = do
  -- Put sub-blocks
  (bid', coreDone') <- foldM (putBlock bh dflags bid) (bid+1, coreDone) blocks
  -- Write our own data
  putEvent bh EVENT_DEBUG_PROCEDURE $ do
    put_ bh bid
    put_ bh pid
    let showSDocC = flip (renderWithStyle dflags) (mkCodeStyle CStyle)
    putString bh $ showSDocC  $ ppr lbl
  -- Write annotations, keeping track of core that was already written
  coreDone'' <- foldM (putAnnotEvent bh dflags) coreDone' ticks
  return (bid', coreDone'')

putAnnotEvent :: BinHandle -> DynFlags -> CoreMap -> Tickish () -> IO CoreMap
putAnnotEvent bh _ coreDone (SourceNote ss names _) = do
  putEvent bh EVENT_DEBUG_SOURCE $ do
    put_ bh $ encLoc $ srcSpanStartLine ss
    put_ bh $ encLoc $ srcSpanStartCol ss
    put_ bh $ encLoc $ srcSpanEndLine ss
    put_ bh $ encLoc $ srcSpanEndCol ss
    putString bh $ unpackFS $ srcSpanFile ss
    putString bh names
  return coreDone
 where encLoc x = fromIntegral x :: Word16

putAnnotEvent bh dflags coreDone (CoreNote lbl con corePtr)
  | not $ (lbl, con) `elemCoreMap` coreDone
  = do doneNew <- putEvent bh EVENT_DEBUG_CORE $ do
         putString bh $ showSDocDump dflags $ ppr lbl
         putString bh $ case con of
           DEFAULT -> ""
           _       -> showSDoc dflags $ ppr con
         case corePtr of
           ExprPtr core -> putCoreExpr bh dflags coreDone core
           AltPtr  alt  -> putCoreAlt bh dflags coreDone alt
       return $ coreDone `plusUFM` doneNew

putAnnotEvent _ _ coreDone _ = return coreDone

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
  return $ d1 `plusUFM` d2
putCoreExpr bh dflags bs (Lam b e) = do
  put_ bh coreLam
  putString bh $ showSDoc dflags $ ppr b
  putString bh $ showSDoc dflags $ ppr $ varType b
  putCoreExpr bh dflags bs e
putCoreExpr bh dflags bs (Let es e) = do
  put_ bh coreLet
  d1 <- putCoreLet bh dflags bs es
  d2 <- putCoreExpr bh dflags bs e
  return $ d1 `plusUFM` d2
putCoreExpr bh dflags bs (Case expr bind _ alts) = do
  put_ bh coreCase
  d <- putCoreExpr bh dflags bs expr
  putString bh $ showSDoc dflags $ ppr bind
  putString bh $ showSDoc dflags $ ppr $ varType bind
  put_ bh (fromIntegral (length alts) :: Word16)
  fmap (foldr plusUFM d) $
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
  fmap (foldr plusUFM emptyUFM) $
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
  | otherwise = do
      d <- code
      return $ addToUFM_C (const (a:)) d b [a]
