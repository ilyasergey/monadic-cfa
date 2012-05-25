{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module CFA.CPS.Analysis.Runner where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Traversable
import Data.Foldable as Foldable
import Control.Monad.Trans
import Control.Monad.State
import Control.Applicative

import CFA.CPS
import CFA.Lattice
import CFA.CPS.Analysis
import CFA.CPS.Analysis.SingleStore
import CFA.CPS.Analysis.Concrete
import CFA.CFAMonads
import CFA.Store

import Debug.Trace

----------------------------------------------------------------------
 -- Running the analysis
----------------------------------------------------------------------

newtype StoreAnd o a s d = SAO (o, s) deriving (Lattice)

instance (Lattice o, Ord a, StoreLike a s d) => StoreLike a (StoreAnd o a s d) d where
  σ0 = SAO (bot, σ0)
  bind (SAO (o, s)) a d = SAO (o, bind s a d)
  replace (SAO (o, s)) a d = SAO (o, replace s a d)
  fetch (SAO (_,s)) a = fetch s a
  filterStore (SAO (o,s)) crit = SAO (o, filterStore s crit)
  
getSAO :: StoreAnd o a s d -> o
getSAO (SAO (o,s)) = o

mapSAO :: (o -> o_) -> StoreAnd o a s d -> StoreAnd o_ a s d 
mapSAO f (SAO (o,s)) = SAO (f o, s)

newtype FixedPointAnal a s g b = FPA { runFPA :: SingleStoreAnalysis (StoreAnd (Set (PΣ a, g)) a s (D a)) g b }
  deriving (Monad)

-- type SingleStoreAnalysis s g a = StateT g (SharedStateT s [] a)
--                                = g -> (SharedStateT s [] (a, g))
--                                = g -> s -> (s, [(a, g)])

-- SharedStateT seenStates (SingleStoreAnalysis s g) a =
--           seenStates -> g -> s -> (s, seenStates, [( a, g)])

instance (Lattice s, Ord a, Addressable a t, Ord t,
          StoreLike a s (D a)) =>
         Analysis (FixedPointAnal a s (ProcCh a, t)) a where
  fun ρ f = FPA $ fun ρ f
  arg ρ f = FPA $ arg ρ f
  a $= d = FPA $ a $= d
  alloc v = FPA $ alloc v
  tick a = FPA $ tick a

class Monad m => FPCalc m a | m -> a where
  hasSeen :: a -> m Bool
  markSeen :: a -> m ()

ifNotSeen :: FPCalc m s => s -> m () -> m ()
ifNotSeen s go = do seen <- hasSeen s
                    when (not seen) $ do
                    markSeen s
                    go

explore :: forall m a. (Show a, Ord a, Analysis m a,
                        GarbageCollector m (PΣ a), FPCalc m (PΣ a)) =>
           CExp -> m ()
explore c = loop (c , ρ0) 0
  where loop :: PΣ a -> Int -> m ()
        loop c step =
          trace ("loop [step " ++ show step ++ "]:\n" ++ show c ++ "\n") $
          -- for consistency with old code: tick off new state only
          --tickOffAndCont c $ 
          do nc <- mnext c
             ifNotSeen nc $ loop nc (step + 1)

type FPSConcrete = StateT (Set (PΣ CAddr, ΣC)) Concrete

instance Analysis (StateT s Concrete) CAddr where
  fun ρ f = lift $ fun ρ f
  arg ρ f = lift $ arg ρ f
  a $= d = lift $ a $= d
  alloc v = lift $ alloc v
  tick a = lift $ tick a

instance GarbageCollector (StateT s Concrete) (PΣ CAddr) where
  gc a = lift $ gc a

instance FPCalc FPSConcrete (PΣ CAddr) where
  hasSeen s = do store <- lift get
                 gets (Set.member (s, store))
  markSeen s = do store <- lift get
                  modify (Set.insert (s, store))


instance (Ord g, Ord a, Lattice s) => FPCalc (FixedPointAnal a s g) (PΣ a) where
  hasSeen s = FPA $ do 
    g <- getGuts
    getsShared (Set.member (s, g) . getSAO)
  markSeen s = FPA $ do
    g <- getGuts
    modifyShared $ mapSAO $ Set.insert (s, g)

instance (Ord a, StoreLike a s (D a), Ord g) =>
         GarbageCollector (FixedPointAnal a s g) (PΣ a) where
  gc a = FPA $ gc a

exploreConcrete :: CExp -> Set (PΣ CAddr, ΣC)
exploreConcrete p = evalState (execStateT (explore p) (Set.empty :: Set (PΣ CAddr, ΣC))) initialΣC
