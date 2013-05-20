-- -----------------------------------------------------------------------------
--
-- (c) The University of Glasgow 1993-2004
--
-- The native code generator's monad.
--
-- -----------------------------------------------------------------------------

module NCGMonad (
        NatM_State(..), mkNatM_State,

        NatM, -- instance Monad
        initNat,
        addImportNat,
        getUniqueNat,
        mapAccumLNat,
        getModLoc,
        setDeltaNat,
        getDeltaNat,
        getBlockIdNat,
        getNewLabelNat,
        getNewRegNat,
        getNewRegPairNat,
        getPicBaseMaybeNat,
        getPicBaseNat,
        getDynFlags,
        getFileId
)

where

#include "HsVersions.h"

import Reg
import Size
import TargetReg
import Dwarf.Types

import BlockId
import CLabel           ( CLabel, mkAsmTempLabel )
import FastString       ( FastString )
import UniqFM
import UniqSupply
import Unique           ( Unique )
import DynFlags
import Module           ( ModLocation )

data NatM_State
        = NatM_State {
                natm_us      :: UniqSupply,
                natm_delta   :: Int,
                natm_imports :: [(CLabel)],
                natm_pic     :: Maybe Reg,
                natm_fileid  :: DwarfFiles,
                natm_dflags  :: DynFlags,
                natm_modloc  :: ModLocation
        }

newtype NatM result = NatM (NatM_State -> (result, NatM_State))

unNat :: NatM a -> NatM_State -> (a, NatM_State)
unNat (NatM a) = a

mkNatM_State :: UniqSupply -> Int -> DwarfFiles -> DynFlags -> ModLocation -> NatM_State
mkNatM_State us delta fileIds dflags modloc
        = NatM_State us delta [] Nothing fileIds dflags modloc

initNat :: NatM_State -> NatM a -> (a, NatM_State)
initNat init_st m
        = case unNat m init_st of { (r,st) -> (r,st) }


instance Monad NatM where
  (>>=) = thenNat
  return = returnNat


thenNat :: NatM a -> (a -> NatM b) -> NatM b
thenNat expr cont
        = NatM $ \st -> case unNat expr st of
                        (result, st') -> unNat (cont result) st'

returnNat :: a -> NatM a
returnNat result
        = NatM $ \st ->  (result, st)

mapAccumLNat :: (acc -> x -> NatM (acc, y))
                -> acc
                -> [x]
                -> NatM (acc, [y])

mapAccumLNat _ b []
  = return (b, [])
mapAccumLNat f b (x:xs)
  = do (b__2, x__2)  <- f b x
       (b__3, xs__2) <- mapAccumLNat f b__2 xs
       return (b__3, x__2:xs__2)

getUniqueNat :: NatM Unique
getUniqueNat = NatM $ \ st ->
    case takeUniqFromSupply $ natm_us st of
    (uniq, us') -> (uniq, st {natm_us = us'})

instance HasDynFlags NatM where
    getDynFlags = NatM $ \ st -> (natm_dflags st, st)

getModLoc :: NatM ModLocation
getModLoc
        = NatM $ \ st -> (natm_modloc st, st)

getDeltaNat :: NatM Int
getDeltaNat = NatM $ \ st -> (natm_delta st, st)


setDeltaNat :: Int -> NatM ()
setDeltaNat delta = NatM $ \ st -> ((), st {natm_delta = delta})


addImportNat :: CLabel -> NatM ()
addImportNat imp
        = NatM $ \ st -> ((), st {natm_imports = imp : natm_imports st})


getBlockIdNat :: NatM BlockId
getBlockIdNat
 = do   u <- getUniqueNat
        return (mkBlockId u)


getNewLabelNat :: NatM CLabel
getNewLabelNat
 = do   u <- getUniqueNat
        return (mkAsmTempLabel u)


getNewRegNat :: Size -> NatM Reg
getNewRegNat rep
 = do u <- getUniqueNat
      dflags <- getDynFlags
      return (RegVirtual $ targetMkVirtualReg (targetPlatform dflags) u rep)


getNewRegPairNat :: Size -> NatM (Reg,Reg)
getNewRegPairNat rep
 = do u <- getUniqueNat
      dflags <- getDynFlags
      let vLo = targetMkVirtualReg (targetPlatform dflags) u rep
      let lo  = RegVirtual $ targetMkVirtualReg (targetPlatform dflags) u rep
      let hi  = RegVirtual $ getHiVirtualRegFromLo vLo
      return (lo, hi)


getPicBaseMaybeNat :: NatM (Maybe Reg)
getPicBaseMaybeNat
        = NatM (\state -> (natm_pic state, state))


getPicBaseNat :: Size -> NatM Reg
getPicBaseNat rep
 = do   mbPicBase <- getPicBaseMaybeNat
        case mbPicBase of
                Just picBase -> return picBase
                Nothing
                 -> do
                        reg <- getNewRegNat rep
                        NatM (\state -> (reg, state { natm_pic = Just reg }))

getFileId :: FastString -> NatM Int
getFileId f = NatM $ \st ->
  case lookupUFM (natm_fileid st) f of
    Just (_,n) -> (n, st)
    Nothing    -> let !n = 1 + sizeUFM (natm_fileid st)
                      !fids = addToUFM (natm_fileid st) f (f,n)
                  in (n, st { natm_fileid = fids  })
