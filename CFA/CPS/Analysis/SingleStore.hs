{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.SingleStore where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

import Debug.Trace

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis
import CFA.CPS.Analysis.Runner
--import CFA.CPS.Analysis.SingleStore.SingleStoreGC

import Util

type SharedAnalysis s0 s g = ReaderT g (SharedStateListT (s, s0) Identity)
-- type SharedAnalysis s0 s g = ReaderT g (SharedStateListT (s0, s) Identity))
-- type SharedAnalysis s0 s g = ReaderT g (SharedStateListT s (StateT s0 Identity))
-- type SharedAnalysis s0 s g = g -> s -> s0 -> (s0, s, [(a]))

-- SharedAnalysis s0 s g a =
--                        SharedStateListT s (State (g, s0)) a
--                        s -> (g, s0) -> ((s, [a]), (g, s0))

instance (Addressable a t, StoreLike a s (D a), Lattice s, Lattice s0, Show a, Show s) =>
         Analysis (SharedAnalysis s0 s (ProcCh a, t)) a where
     fun ρ (Lam l) = return $ Clo(l, ρ)
     fun ρ (Ref v) = getsNDSet $ flip fetch (ρ!v) . fst
        
     arg ρ (Lam l) = return $ Clo(l, ρ)   
     arg ρ (Ref v) = getsNDSet $ flip fetch (ρ!v) . fst
     
     a $= d = modify $ mapFst $ \ σ -> bind σ a (Set.singleton d)

     alloc v = asks (valloc v . snd)
     
     tick proc ps = local $ \(_, t) -> (Just proc, advance proc ps t)


instance (Ord a, StoreLike a s (D a), Lattice s0, Show s, Show a) 
  => GarbageCollector (SharedAnalysis s0 s g) (PΣ a) where
  gc m = mapReaderT mergeSharedState $ do
    ps <- m
    σ <- gets fst
    let rs = Set.map (\(v, a) -> a) (reachable ps σ)
    modify $ mapFst $ \ σ -> filterStore σ (\a -> Set.member a rs)
    return ps
    
instance (Ord g, Ord a, Lattice s, Show a) =>
         FPCalc (SharedAnalysis (Set (PΣ a, g), s) s g) (PΣ a) where
  hasSeen p = do
    s <- gets fst
    (s0, sOld) <- gets snd
    g <- ask
    let seen = Set.member (p,g) s0 && s ⊑ sOld
    return seen
  markSeen p = do
    g <- ask
    s <- gets fst
    lift $ modify $ mapSnd $
      \(seenStates, prevStore) -> (Set.insert (p, g) seenStates, s ⊔ prevStore)

