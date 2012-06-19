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

-- class Monad m => FPCalc m s | m -> s where
--   hasSeen :: s -> m Bool
--   markSeen :: s -> m ()

-- ifNotSeen :: FPCalc m s => s -> m () -> m ()
-- ifNotSeen s go = do seen <- hasSeen s
--                     when (not seen) $ do
--                     markSeen s
--                     go

-- addToFP :: (FPCalc m s, MonadPlus m) => s -> m s -> m s
-- addToFP s cont = do seen <- hasSeen s
--                     if seen then return s
--                       else return s `mplus` (markSeen s >> cont)

-- ifNotSeen :: s -> ReaderT (Set s) m () -> ReaderT (Set s) m ()
-- ifNotSeen s go = do seen <- asks (Set.member s)
--                     when seen $ 
--                     local (Set.insert s) go

-- explore :: forall m a. (Show a, Analysis m a,
--                         GarbageCollector m (PΣ a), FPCalc m (PΣ a)) =>
--            CExp -> m ()
-- explore c = loop (c , ρ0) 0
--   where loop :: PΣ a -> Int -> m ()
--         loop c step =
--           trace ("loop [step " ++ show step ++ "]:\n" ++ show c ++ "\n") $
--           -- for consistency with old code: tick off new state only
--           -- ifNotSeen c $ 
--           do nc <- mnext c
--              --trace ("explore nc: " ++ show nc) $ do
--              ifNotSeen nc $ loop nc (step + 1)

-- reachableStep :: (Monad m, Ord a, Foldable t) => (a -> m (t a)) -> a -> ℙ a -> m (ℙ a)
-- reachableStep mnext init =
--   Foldable.foldr
--     (liftM2 (flip $ Foldable.foldr Set.insert) . mnext)
--     (return $ Set.singleton init)

findFP :: forall a m. (Lattice a) => (a -> a) -> a
findFP f = loop bot
  where loop :: a -> a
        loop c = let c' = f c in if c' ⊑ c then c else loop c' 

class AddStepToFP m a fp | m -> a, m -> fp, fp -> m where
  applyStep :: (a -> m a) -> fp -> fp
  inject :: a -> fp

exploreFP :: forall m a fp .
             (Lattice fp, AddStepToFP m (PΣ a) fp, GarbageCollector m (PΣ a),
              Analysis m a, Show a) =>
             CExp -> fp
exploreFP c = findFP loop
  where loop :: fp -> fp
        loop acc = inject (c, ρ0) ⊔ applyStep mnext acc
