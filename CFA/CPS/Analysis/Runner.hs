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

class Monad m => FPCalc m a | m -> a where
  hasSeen :: a -> m Bool
  markSeen :: a -> m ()

ifNotSeen :: FPCalc m s => s -> m () -> m ()
ifNotSeen s go = do seen <- hasSeen s
                    when (not seen) $ do
                    markSeen s
                    go

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
          --tickOffAndCont c $ 
          do nc <- mnext c
             flip (maybe (return ())) nc $ \nc -> 
               ifNotSeen nc $ loop nc (step + 1)

