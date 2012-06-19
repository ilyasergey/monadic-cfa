{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module CFA.CPS.Analysis.Runner where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Traversable
import Data.Foldable as Foldable
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.State
import Control.Applicative

import CFA.CPS
import CFA.Lattice
import CFA.CPS.Analysis
import CFA.CFAMonads
import CFA.Store

import Util

import Debug.Trace

----------------------------------------------------------------------
 -- Running the analysis
----------------------------------------------------------------------

-- newtype StoreAnd o a s d = SAO (o, s) deriving (Lattice)

-- instance (Lattice o, Ord a, StoreLike a s d) => StoreLike a (StoreAnd o a s d) d where
--   σ0 = SAO (bot, σ0)
--   bind (SAO (o, s)) a d = SAO (o, bind s a d)
--   replace (SAO (o, s)) a d = SAO (o, replace s a d)
--   fetch (SAO (_,s)) a = fetch s a
--   filterStore (SAO (o,s)) crit = SAO (o, filterStore s crit)
  
-- getSAO :: StoreAnd o a s d -> o
-- getSAO (SAO (o,s)) = o

-- mapSAO :: (o -> o_) -> StoreAnd o a s d -> StoreAnd o_ a s d 
-- mapSAO f (SAO (o,s)) = SAO (f o, s)

class Monad m => FPCalc m s | m -> s where
  hasSeen :: s -> m Bool
  markSeen :: s -> m ()

ifNotSeen :: FPCalc m s => s -> m () -> m ()
ifNotSeen s go = do seen <- hasSeen s
                    when (not seen) $ do
                    markSeen s
                    go

addToFP :: (FPCalc m s, MonadPlus m) => s -> m s -> m s
addToFP s cont = do seen <- hasSeen s
                    if seen then return s
                      else return s `mplus` (markSeen s >> cont)

-- ifNotSeen :: s -> ReaderT (Set s) m () -> ReaderT (Set s) m ()
-- ifNotSeen s go = do seen <- asks (Set.member s)
--                     when seen $ 
--                     local (Set.insert s) go

explore :: forall m a. (Show a, Analysis m a,
                        GarbageCollector m (PΣ a), FPCalc m (PΣ a)) =>
           CExp -> m ()
explore c = loop (c , ρ0) 0
  where loop :: PΣ a -> Int -> m ()
        loop c step =
          trace ("loop [step " ++ show step ++ "]:\n" ++ show c ++ "\n") $
          -- for consistency with old code: tick off new state only
          -- ifNotSeen c $ 
          do nc <- mnext c
             --trace ("explore nc: " ++ show nc) $ do
             ifNotSeen nc $ loop nc (step + 1)

findFP :: forall a m. (Monad m, Lattice a) => (a -> m a) -> m a
findFP f = loop bot
  where loop :: a -> m a
        loop c = do c' <- f c
                    if c' ⊑ c
                    then return c
                    else loop c' 

reachableStep :: (Monad m, Ord a, Foldable t) => (a -> m (t a)) -> a -> ℙ a -> m (ℙ a)
reachableStep mnext init =
  Foldable.foldr
    (liftM2 (flip $ Foldable.foldr Set.insert) . mnext)
    (return $ Set.singleton init)

class AddStepToFP m a fp | m -> a, m -> fp, fp -> m where
  applyStep :: (a -> m a) -> fp -> fp
  inject :: a -> fp

data Phantom1 (m :: * -> *) where
  Booh :: Phantom1 m

exploreFP :: forall m a fp .
             (Lattice fp, AddStepToFP m (PΣ a) fp, GarbageCollector m (PΣ a),
              Analysis m a, Show a) =>
             CExp -> fp
exploreFP c = runIdentity $ findFP (Identity . loop) 
  where loop :: fp -> fp
        loop acc = inject (c, ρ0) ⊔ applyStep mnext acc
