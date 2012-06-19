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
-- NonSharedAnalysis s0 s g a =
--   SharedStateListT s (StateT g (SharedStateListT s0 Identity)) 
--   s -> StateT g (SharedStateListT s0 Identity) (s, [a])
--   s -> g -> s0 -> (s0, [(g, (s, [a]))])

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
         


-- instance (Lattice s, Ord a, Ord g, Ord s) => 
--          FPCalc (NonSharedAnalysis (Set (PΣ a, s, g)) s g) (PΣ a) where
--   hasSeen p =
--     do g <- lift $ lift ask
--        s <- get
--        lift $ gets $ Set.member (p, s, g)
--   markSeen p = 
--     do g <- lift $ lift ask
--        s <- get
--        lift $ modify $ Set.insert (p, s, g)


-- analysis :: 
--   (Ord s, Ord a, Ord t, StoreLike a s (D a), Show a, Addressable a t) =>
--   CExp -> ℙ ((PΣ a, (ProcCh a, t)), s) ->
--   Identity (ℙ ((PΣ a, (ProcCh a, t)), s))
-- analysis c =
--   reachableStep (\((p, g), s) ->
--                   liftM concat $ collectListT $ collectSSListT (runStateT (mnext p) g) s)
--     (((c, ρ0), (Nothing, τ0)), bot)


-- runAnalysis :: (Addressable a t, StoreLike a s (D a), Show a, Ord s, Ord t) =>
--                CExp -> ℙ ((PΣ a, (ProcCh a, t)), s)
-- runAnalysis c = runIdentity $ findFP (analysis c)

initialGuts :: Addressable a t => (ProcCh a, t)
initialGuts = (Nothing, τ0) 


instance (Ord s, Ord a, Ord t, Addressable a t, Lattice s, StoreLike a s (D a)) =>
         AddStepToFP (NonSharedAnalysis s (ProcCh a, t)) (PΣ a)
         (Set ((PΣ a, (ProcCh a, t)), s)) where
  applyStep step fp =
    Foldable.foldr
      (\((p,g),s) -> Set.union $ Set.fromList $ concat $ runIdentity $
                     collectListT (collectSSListT (runStateT (gc $ step p) g) s))
      bot fp
  inject p = Set.singleton $ ((p, initialGuts), bot)
