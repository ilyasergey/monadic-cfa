{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.ReallyNonShared where

import Data.Maybe
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Foldable as Foldable
import Data.Traversable
import Control.Monad.State
import Control.Monad.ListT
import Control.Monad.Identity
import Control.Monad.Reader

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis
import CFA.CPS.Analysis.Runner

import Util

type ReallyNonSharedAnalysis s g = StateT g (StateT s (ListT Identity))

-- ReallyNonSharedAnalysis s0 s g a =
--   SharedStateListT s (StateT g (SharedStateListT s0 Identity)) 
--   s -> StateT g (SharedStateListT s0 Identity) (s, [a])
--   s -> g -> s0 -> (s0, [(g, (s, [a]))])

-- instance (Addressable a t, StoreLike a s (D a), 
--           MonadState (s, ProcCh a, t) m, MonadPlus m) 
--   => Analysis m a

instance (Addressable a t, StoreLike a s (D a)) 
  => Analysis (ReallyNonSharedAnalysis s (ProcCh a, t)) a
              where
     fun ρ (Lam l) = return $ Clo(l, ρ)
     fun ρ (Ref v) = lift $ getsNDSet $ (flip fetch $ ρ!v) 
        
     arg ρ (Lam l) = return $ Clo(l, ρ)   
     arg ρ (Ref v) = lift $ getsNDSet $ flip fetch (ρ!v) 
     
     a $= d = lift $ modify $ \ σ -> bind σ a (Set.singleton d)

     alloc v = gets (valloc v . snd)
     
     tick proc ps k = do modify $ \(_, t) -> (Just proc, advance proc ps t)
                         k

--     exit = mzero

-- Garbage Collection
instance (Lattice s, Eq a, StoreLike a s (D a), Ord a) =>
         GarbageCollector (ReallyNonSharedAnalysis s (ProcCh a, t)) (PΣ a) where
  gc m = do
    ps <- m
    σ <- lift get
    let rs = Set.map (\(v, a) -> a) (reachable ps σ)
    lift $ modify $ \ σ -> filterStore σ (\a -> Set.member a rs)
    return ps

-- instance (Lattice s, Ord a, Ord g, Ord s) => 
--          FPCalc (ReallyNonSharedAnalysis (Set (PΣ a, s, g)) s g) (PΣ a) where
--   hasSeen p =
--     do s <- get
--        g <- lift $ lift $ ask
--        lift $ gets $ Set.member (p, s, g)
--   markSeen p = 
--     do s <- get
--        g <- lift $ lift ask
--        lift $ modify $ Set.insert (p, s, g)

-- rnsAnalysis :: 
--   (Ord s, Ord a, Ord t, StoreLike a s (D a), Show a, Addressable a t) =>
--   CExp -> ℙ ((PΣ a, (ProcCh a, t)), s) ->
--   Identity (ℙ ((PΣ a, (ProcCh a, t)), s))
-- rnsAnalysis c = reachableStep (\((p, g), s) -> collectListT $ runStateT (runStateT (mnext p) g) s) (((c, ρ0), (Nothing, τ0)), bot)


-- runRNSAnalysis :: (Addressable a t, StoreLike a s (D a), Show a, Ord s, Ord t) =>
--                CExp -> ℙ ((PΣ a, (ProcCh a, t)), s)
-- runRNSAnalysis c = runIdentity $ findFP (rnsAnalysis c)

initialGuts :: Addressable a t => (ProcCh a, t)
initialGuts = (Nothing, τ0) 

newtype RNSFP a = RNSFP { unRNSFP :: a } deriving (Lattice)

instance (Ord s, Ord a, Ord t, Addressable a t, Lattice s) =>
         AddStepToFP (ReallyNonSharedAnalysis s (ProcCh a, t)) (PΣ a)
         (RNSFP (ℙ ((PΣ a, (ProcCh a, t)), s))) where
  applyStep step (RNSFP fp) =
    RNSFP $ Foldable.foldr
      (\ ((p,g),s) -> Set.union $ Set.fromList $ runIdentity $
                      collectListT (runStateT (runStateT (step p) g) s))
      bot fp
  inject p = RNSFP $ Set.singleton $ ((p, initialGuts), bot)
