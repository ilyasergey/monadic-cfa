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

-- ReallyNonSharedAnalysis s g a =
--   StateT g (StateT s (ListT Identity)) a
--   g -> StateT s (ListT Identity) (a, g)
--   g -> s -> ListT Identity ((a, g), s)
--   g -> s -> Identity [((a, g), s)]    (more or less :))
--   g -> s -> [((a, g), s)]

instance (Addressable a t, StoreLike a s (D a)) 
  => Analysis (ReallyNonSharedAnalysis s (ProcCh a, t)) a
              where
     fun ρ (Lam l) = return $ Clo(l, ρ)
     fun ρ (Ref v) = lift $ getsNDSet $ (flip fetch $ ρ!v) 
        
     arg ρ (Lam l) = return $ Clo(l, ρ)   
     arg ρ (Ref v) = lift $ getsNDSet $ flip fetch (ρ!v) 
     
     a $= d = lift $ modify $ \ σ -> bind σ a (Set.singleton d)

     alloc v = gets (valloc v . snd)
     
     tick proc ps = modify $ \(_, t) -> (Just proc, advance proc ps t)

-- Garbage Collection
instance (Lattice s, Eq a, StoreLike a s (D a), Ord a) =>
         GarbageCollector (ReallyNonSharedAnalysis s g) (PΣ a) where
  gc ps = do
    σ <- lift get
    let rs = Set.map (\(v, a) -> a) (reachable ps σ)
    lift $ modify $ \ σ -> filterStore σ (\a -> Set.member a rs)
    return ()

initialGuts :: Addressable a t => (ProcCh a, t)
initialGuts = (Nothing, τ0) 

class HasInitial g where
  initial :: g

instance Addressable a t => HasInitial (ProcCh a, t) where
  initial = initialGuts

  
newtype RNSFP a g s = RNSFP { unRNSFP :: ℙ ((PΣ a, g), s) } deriving (Lattice)

instance (Ord s, Ord a, Ord g, HasInitial g, Lattice s, StoreLike a s (D a)) =>
         AddStepToFP (ReallyNonSharedAnalysis s g) (PΣ a)
         (RNSFP a g s) where
  applyStep step (RNSFP fp) =
    RNSFP $ joinWith 
      (\ ((p,g),s) -> Set.fromList $ runIdentity $
                      collectListT (runStateT (runStateT (do {x <- step p; gc x; return x}) g) s))
      fp
  inject p = RNSFP $ Set.singleton $ ((p, initial), bot)
