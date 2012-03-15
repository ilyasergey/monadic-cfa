{-# LANGUAGE TypeSynonymInstances #-}

module CFA.AFJ.Examples where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Store
import CFA.AFJ
import CFA.AFJ.Analysis
import CFA.AFJ.Analysis.Runner

----------------------------------------------------------------------
-- abstract interpreter with a per-state store
----------------------------------------------------------------------

import CFA.AFJ.Analysis.NonShared

----------------------------------------------------------------------
-- example program
----------------------------------------------------------------------

----------------------------------------------------------------------

instance Truncatable Time where
  trunc ls = take 1 ls

type AbstractGuts = (Time, Store Addr)

abstractResult :: [Stmt] -> ClassTable -> ((), Set (State Addr, AbstractGuts))
abstractResult = explore 
