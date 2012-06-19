{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.NonShared where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Foldable as Foldable hiding (concat) 
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

type NonSharedAnalysis s g =
  StateT g (SharedStateListT s (ListT Identity))
-- NonSharedAnalysis s g a =
-- StateT g (SharedStateListT s (ListT Identity)) a
-- g -> SharedStateListT s (ListT Identity) (a, g)    (more or less)
-- g -> s -> ListT Identity [((a, g),s)]              (more or less)
-- g -> s -> Identity [[((a, g),s)]]
-- g -> s -> [[((a, g),s)]]

instance (Addressable a t, StoreLike a s (D a)) 
  => Analysis (NonSharedAnalysis s (ProcCh a, t)) a
              where
     fun ρ (Lam l) = return $ Clo(l, ρ)
     fun ρ (Ref v) = lift $ getsM $ lift . pureNDSet . (flip fetch $ ρ!v)
        
     arg ρ (Lam l) = return $ Clo(l, ρ)   
     arg ρ (Ref v) = lift $ getsNDSet $ flip fetch (ρ!v) 
     
     a $= d = lift $ modify $ \ σ -> bind σ a (Set.singleton d)

     alloc v = gets $ valloc v . snd
     
     tick proc ps k = do modify $ \(_, t) -> (Just proc, advance proc ps t)
                         k

-- Garbage Collection
instance (Lattice s, Eq a, StoreLike a s (D a), Ord a) =>
         GarbageCollector (NonSharedAnalysis s (ProcCh a, t)) (PΣ a) where
  gc m = mapStateT mergeSharedState $ do
    ps <- m
    σ <- lift get
    let rs = Set.map (\(v, a) -> a) (reachable ps σ)
    lift $ modify $ \ σ -> filterStore σ (\a -> Set.member a rs)
    return ps
         

initialGuts :: Addressable a t => (ProcCh a, t)
initialGuts = (Nothing, τ0) 


instance (Ord s, Ord a, Ord t, Addressable a t, Lattice s, StoreLike a s (D a)) =>
         AddStepToFP (NonSharedAnalysis s (ProcCh a, t)) (PΣ a)
         (ℙ ((PΣ a, (ProcCh a, t)), s)) where
  applyStep step fp =
    joinWith (\((p,g),s) -> Set.fromList $ concat $ runIdentity $ 
                            collectListT (collectSSListT (runStateT (gc $ step p) g) s))
             fp
  inject p = Set.singleton $ ((p, initialGuts), bot)
