{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CESK.Analysis.Runner where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Lattice
import CFA.CESK
import CFA.CESK.Analysis

import Debug.Trace

----------------------------------------------------------------------
 -- Running the analysis
----------------------------------------------------------------------

-- Abstract state-space exploration algorithm
-- TODO: remove step counting and trace output 
loop :: (Analysis m a s g, Ord a, Ord g, Show a, Show g, Lattice s) =>
        [(State a, g)] -> (s, Set (State a, g)) -> Int -> (s, Set (State a, g))

loop worklist v@(shared, oldStates) step = 
  -- trace output
  trace ("Worklist [step " ++ show step ++ "]:\n" ++ show worklist ++ "\n") $
  let newStoreStates = List.map (\(state, config) -> 
                                    stepAnalysis shared config state)
                                    worklist 
      -- compute a new shared component and new states
      (shared', states') = foldl (\(s, bg) -> \(s', bg') -> (s ⊔ s', bg ++ bg'))
                                 (shared, []) newStoreStates
      newWorkList = List.filter (\elem -> not (Set.member elem oldStates)) states'
   in if List.null newWorkList
      then v
      else let newVisited = (shared', oldStates ⊔ (Set.fromList newWorkList))
            in loop newWorkList newVisited (step + 1)

 -- compute an approximation
explore :: (Analysis m a s g, Ord a, Ord g, Show a, Show g, Lattice s) => 
        Exp -> (s, Set (State a, g))

explore program = 
  let (state0, σ0, g0) = inject program
   in loop [(state0, g0)] (σ0, Set.empty) 0 
