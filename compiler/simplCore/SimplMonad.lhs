%
% (c) The AQUA Project, Glasgow University, 1993-1998
%
\section[SimplMonad]{The simplifier Monad}

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module SimplMonad (
	-- The monad
	SimplM,
	initSmpl,
	getDOptsSmpl, getSimplRules, getFamEnvs,

        -- Unique supply
        MonadUnique(..), newId,

	-- Counting
	SimplCount, tick, freeTick, checkedTick,
	getSimplCount, zeroSimplCount, pprSimplCount, 
        plusSimplCount, isZeroSimplCount
    ) where

import Id		( Id, mkSysLocal )
import Type             ( Type )
import FamInstEnv	( FamInstEnv )
import Rules		( RuleBase )
import UniqSupply
import DynFlags		( DynFlags( simplTickFactor ) )
import CoreMonad
import Outputable
import FastString
\end{code}

%************************************************************************
%*									*
\subsection{Monad plumbing}
%*									*
%************************************************************************

For the simplifier monad, we want to {\em thread} a unique supply and a counter.
(Command-line switches move around through the explicitly-passed SimplEnv.)

\begin{code}
newtype SimplM result
  =  SM  { unSM :: SimplTopEnv	-- Envt that does not change much
		-> UniqSupply	-- We thread the unique supply because
				-- constantly splitting it is rather expensive
		-> SimplCount 
		-> (result, UniqSupply, SimplCount)}

data SimplTopEnv 
  = STE	{ st_flags :: DynFlags 
     	, st_max_ticks :: Int  -- Max #ticks in this simplifier run
	  	       	       -- Zero means infinity!
	, st_rules :: RuleBase
	, st_fams  :: (FamInstEnv, FamInstEnv) }
\end{code}

\begin{code}
initSmpl :: DynFlags -> RuleBase -> (FamInstEnv, FamInstEnv) 
	 -> UniqSupply		-- No init count; set to 0
	 -> Int			-- Size of the bindings
	 -> SimplM a
	 -> (a, SimplCount, Maybe SDoc)

initSmpl dflags rules fam_envs us size m
  = case unSM m env us (zeroSimplCount dflags) of
    (result, _, count) ->
        let mWarning = if st_max_ticks env <= simplCountN count
                       then Just (msg count)
                       else Nothing
        in (result, count, mWarning)
  where
    env = STE { st_flags = dflags, st_rules = rules
    	      , st_max_ticks = computeMaxTicks dflags size
              , st_fams = fam_envs }
    msg sc = vcat [ ptext (sLit "Warning: Simplifier ticks exhausted.")
                  , ptext (sLit "To increase the limit, use -fsimpl-tick-factor=N (default 100)")
                  , ptext (sLit "If you need to do this, let GHC HQ know, and what factor you needed")
                  , pp_details sc
                  , pprSimplCount sc ]
    pp_details sc
      | hasDetailedCounts sc = empty
      | otherwise = ptext (sLit "To see detailed counts use -ddump-simpl-stats")


computeMaxTicks :: DynFlags -> Int -> Int
-- Compute the max simplifier ticks as
--     (base-size + pgm-size) * magic-multiplier * tick-factor/100
-- where 
--    magic-multiplier is a constant that gives reasonable results
--    base-size is a constant to deal with size-zero programs
computeMaxTicks dflags size
  = fromInteger ((toInteger (size + base_size)
                  * toInteger (tick_factor * magic_multiplier))
          `div` 100)
  where
    tick_factor      = simplTickFactor dflags 
    base_size        = 100
    magic_multiplier = 40
	-- MAGIC NUMBER, multiplies the simplTickFactor
	-- We can afford to be generous; this is really
	-- just checking for loops, and shouldn't usually fire
	-- A figure of 20 was too small: see Trac #553

{-# INLINE thenSmpl #-}
{-# INLINE thenSmpl_ #-}
{-# INLINE returnSmpl #-}

instance Monad SimplM where
   (>>)   = thenSmpl_
   (>>=)  = thenSmpl
   return = returnSmpl

returnSmpl :: a -> SimplM a
returnSmpl e = SM (\_st_env us sc -> (e, us, sc))

thenSmpl  :: SimplM a -> (a -> SimplM b) -> SimplM b
thenSmpl_ :: SimplM a -> SimplM b -> SimplM b

thenSmpl m k 
  = SM (\ st_env us0 sc0 ->
	  case (unSM m st_env us0 sc0) of 
		(m_result, us1, sc1) -> unSM (k m_result) st_env us1 sc1 )

thenSmpl_ m k 
  = SM (\st_env us0 sc0 ->
	 case (unSM m st_env us0 sc0) of 
		(_, us1, sc1) -> unSM k st_env us1 sc1)

-- TODO: this specializing is not allowed
-- {-# SPECIALIZE mapM         :: (a -> SimplM b) -> [a] -> SimplM [b] #-}
-- {-# SPECIALIZE mapAndUnzipM :: (a -> SimplM (b, c)) -> [a] -> SimplM ([b],[c]) #-}
-- {-# SPECIALIZE mapAccumLM   :: (acc -> b -> SimplM (acc,c)) -> acc -> [b] -> SimplM (acc, [c]) #-}
\end{code}


%************************************************************************
%*									*
\subsection{The unique supply}
%*									*
%************************************************************************

\begin{code}
instance MonadUnique SimplM where
    getUniqueSupplyM
       = SM (\_st_env us sc -> case splitUniqSupply us of
                                (us1, us2) -> (us1, us2, sc))

    getUniqueM
       = SM (\_st_env us sc -> case splitUniqSupply us of
                                (us1, us2) -> (uniqFromSupply us1, us2, sc))

    getUniquesM
        = SM (\_st_env us sc -> case splitUniqSupply us of
                                (us1, us2) -> (uniqsFromSupply us1, us2, sc))

getDOptsSmpl :: SimplM DynFlags
getDOptsSmpl = SM (\st_env us sc -> (st_flags st_env, us, sc))

getSimplRules :: SimplM RuleBase
getSimplRules = SM (\st_env us sc -> (st_rules st_env, us, sc))

getFamEnvs :: SimplM (FamInstEnv, FamInstEnv)
getFamEnvs = SM (\st_env us sc -> (st_fams st_env, us, sc))

newId :: FastString -> Type -> SimplM Id
newId fs ty = do uniq <- getUniqueM
                 return (mkSysLocal fs uniq ty)
\end{code}


%************************************************************************
%*									*
\subsection{Counting up what we've done}
%*									*
%************************************************************************

\begin{code}
getSimplCount :: SimplM SimplCount
getSimplCount = SM (\_st_env us sc -> (sc, us, sc))

tick :: Tick -> SimplM ()
tick t = SM (\_st_env us sc -> let sc' = doSimplTick t sc 
                               in sc' `seq` ((), us, sc'))

checkedTick :: Tick -> SimplM ()
-- Try to take a tick, but fail if too many
checkedTick t 
  = SM (\_st_env us sc ->
                         {-
                         This error is disabled for now due to #5539.
                         We will still print a warning at the callsites
                         of initSmpl.

                         if st_max_ticks st_env <= simplCountN sc
                         then pprPanic "Simplifier ticks exhausted" (msg sc)
                         else
                         -}
                              let sc' = doSimplTick t sc 
                              in sc' `seq` ((), us, sc'))
{-
  where
    msg sc = vcat [ ptext (sLit "When trying") <+> ppr t
                  , ptext (sLit "To increase the limit, use -fsimpl-tick-factor=N (default 100)")
                  , ptext (sLit "If you need to do this, let GHC HQ know, and what factor you needed")
                  , pp_details sc
                  , pprSimplCount sc ]
    pp_details sc
      | hasDetailedCounts sc = empty
      | otherwise = ptext (sLit "To see detailed counts use -ddump-simpl-stats")
-}

freeTick :: Tick -> SimplM ()
-- Record a tick, but don't add to the total tick count, which is
-- used to decide when nothing further has happened
freeTick t 
   = SM (\_st_env us sc -> let sc' = doFreeSimplTick t sc
                           in sc' `seq` ((), us, sc'))
\end{code}
