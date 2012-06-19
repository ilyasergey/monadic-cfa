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
--import CFA.CPS.Analysis.SingleStore.SingleStoreGC

import Util

type SharedAnalysis s g = StateT g (SharedStateListT s Identity)
-- type SharedAnalysis s0 s g = ReaderT g (SharedStateListT (s0, s) Identity))
-- type SharedAnalysis s0 s g = g -> s -> s0 -> (s0, s, [(a]))

-- SharedAnalysis s0 s g a =
--                        SharedStateListT s (State (g, s0)) a
--                        s -> (g, s0) -> ((s, [a]), (g, s0))

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

--     exit = mzero

instance (Ord a, StoreLike a s (D a)) 
  => GarbageCollector (SharedAnalysis s g) (PΣ a) where
  gc m = mapStateT mergeSharedState $ do
    ps <- m
    σ <- lift get
    let rs = Set.map (\(v, a) -> a) (reachable ps σ)
    lift $ modify $ \ σ -> filterStore σ (\a -> Set.member a rs)
    return ps
    
-- instance (Ord g, Ord a, Lattice s, Show a) =>
--          FPCalc (SharedAnalysis (Set (PΣ a, g), s) s g) (PΣ a) where
--   hasSeen p = do
--     s <- gets fst
--     (s0, sOld) <- gets snd
--     g <- lift ask
--     let seen = Set.member (p,g) s0 && s ⊑ sOld
--     return seen
--   markSeen p = do
--     g <- lift ask
--     s <- gets fst
--     modify $ mapSnd $
--       \(seenStates, prevStore) -> (Set.insert (p, g) seenStates, s ⊔ prevStore)


-- analysis :: 
--   (Ord s, Ord a, Ord t, StoreLike a s (D a), Show a, Addressable a t, Show s) =>
--   CExp -> ℙ (PΣ a, (ProcCh a, t)) ->
--   State s (ℙ (PΣ a, (ProcCh a, t)))
-- analysis c =
--   reachableStep (\(p, g) ->
--                   collectSSListTST (runStateT (mnext p) g)) ((c, ρ0), (Nothing, τ0))


-- runAnalysis :: (Addressable a t, StoreLike a s (D a), Show a, Ord s, Ord t, Show s) =>
--                CExp -> (ℙ (PΣ a, (ProcCh a, t)), s)
-- runAnalysis c = runIdentity $ findFP (\(vs, s) -> runStateT (analysis c vs) s)

initialGuts :: Addressable a t => (ProcCh a, t)
initialGuts = (Nothing, τ0) 

instance (Ord t, Ord a, Lattice s, Addressable a t, StoreLike a s (D a)) =>
         AddStepToFP (SharedAnalysis s (ProcCh a, t)) (PΣ a) (ℙ (PΣ a, (ProcCh a, t)), s) where
  applyStep step (states, s) = 
    Foldable.foldr (\(p, g) -> (⊔) $ mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s) bot states
  inject a = (Set.singleton (a, initialGuts), bot)
                               
