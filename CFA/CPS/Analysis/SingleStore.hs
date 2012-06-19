{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.SingleStore where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Foldable as Foldable
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

import Util

type SharedAnalysis s g = StateT g (SharedStateListT s Identity)
-- SharedAnalysis s g a =
--   StateT g (SharedStateListT s Identity) a
--   g -> SharedStateListT s Identity (a,g)
--   g -> s -> Identity [((a,g),s)]    (more or less)
--   g -> s -> [((a,g),s)]

instance (Addressable a t, StoreLike a s (D a), Lattice s, Show a, Show s) =>
         Analysis (SharedAnalysis s (ProcCh a, t)) a where
     fun ρ (Lam l) = return $ Clo(l, ρ)
     fun ρ (Ref v) = lift $ getsNDSet $ flip fetch (ρ!v) 
        
     arg ρ (Lam l) = return $ Clo(l, ρ)   
     arg ρ (Ref v) = lift $ getsNDSet $ flip fetch (ρ!v) 
     
     a $= d = lift $ modify $ \ σ -> bind σ a (Set.singleton d)

     alloc v = gets (valloc v . snd)
     
     tick proc ps k = do modify $ \(_, t) -> (Just proc, advance proc ps t)
                         k

instance (Ord a, StoreLike a s (D a)) 
  => GarbageCollector (SharedAnalysis s g) (PΣ a) where
  gc m = mapStateT mergeSharedState $ do
    ps <- m
    σ <- lift get
    let rs = Set.map (\(v, a) -> a) (reachable ps σ)
    lift $ modify $ \ σ -> filterStore σ (\a -> Set.member a rs)
    return ps
    
initialGuts :: Addressable a t => (ProcCh a, t)
initialGuts = (Nothing, τ0) 

instance (Ord t, Ord a, Lattice s, Addressable a t, StoreLike a s (D a)) =>
         AddStepToFP (SharedAnalysis s (ProcCh a, t)) (PΣ a) (ℙ (PΣ a, (ProcCh a, t)), s) where
  applyStep step (states, s) = 
    Foldable.foldr (\(p, g) -> (⊔) $ mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s) bot states
  inject a = (Set.singleton (a, initialGuts), bot)
                               
