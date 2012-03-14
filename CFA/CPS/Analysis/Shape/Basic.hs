{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CFA.CPS.Analysis.Shape.Basic where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.Store

import CFA.CFAMonads
import CFA.CPS.Analysis

instance (Ord a, StoreLike a s d) => AlkaliLike a (s, ℙ a) d where
  addUniqueAddr  a = undefined
  deAnodizeStore σ = undefined
  deAnodizeEnv σ ρ = undefined
  deAnodizeD  σ d = undefined
  reset      σ = undefined
