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
import CFA.CPS.Analysis.ReallyNonShared

import Util

type SharedAnalysis s g = StateT g (SharedStateListT s Identity)
-- SharedAnalysis s g a =
--   StateT g (SharedStateListT s Identity) a
--   g -> SharedStateListT s Identity (a,g)
--   g -> s -> Identity [((a,g),s)]    (more or less)
--   g -> s -> [((a,g),s)]

alpha :: (Lattice s, Ord a, Ord g) =>
        ℙ ((PΣ a, g), s) -> (ℙ (PΣ a, g), s)
alpha = joinWith (\((p, g), s) -> (Set.singleton (p,g), s))

gamma :: (Ord a, Ord g, Ord s) =>
        (ℙ (PΣ a, g), s) -> ℙ ((PΣ a, g), s)
gamma (states, s) = Set.map (\(p, g) -> ((p,g), s)) states

instance (Ord g, Ord a, Lattice s, StoreLike a s (D a), Ord s, HasInitial g) =>
         AddStepToFP (ReallyNonSharedAnalysis s g)  (PΣ a) (ℙ (PΣ a, g), s) where
  applyStep step = alpha . unRNSFP . applyStep step . RNSFP . gamma 

  inject a = (Set.singleton (a, initial), bot)
                               
