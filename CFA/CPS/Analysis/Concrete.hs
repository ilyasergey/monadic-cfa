{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.Concrete where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis

data CAddr = CBind Var Int
  deriving (Eq, Ord, Show)

instance Analysis (Concrete) 
                  CAddr 
                  ()
                  (Store CAddr, Int) 
                  where
  fun ρ (Lam l) = Concrete (\ (σ,t) -> 
    let proc = Clo(l, ρ)
     in (proc,(σ,t)))
  fun ρ (Ref v) = Concrete (\ (σ,t) -> 
    let [proc] = Set.toList $ σ!(ρ!v)
     in (proc,(σ,t)))

  arg ρ (Lam l) = Concrete (\ (σ,t) ->
    let proc = Clo(l, ρ) 
     in (Set.singleton proc, (σ, t)))
  arg ρ (Ref v) = Concrete (\ (σ,t) -> 
    let procs = σ!(ρ!v)
     in (procs, (σ, t)))

  a $= d = Concrete (\ (σ,t) -> ((), (σ ⨆ [a ==> d],t)) )

  alloc v = Concrete (\ (σ,t) -> (CBind v t, (σ, t)))

  tick (call, ρ) = Concrete (\ (σ,n) -> ((), (σ, n+1)))

  stepAnalysis _ config state = ((), [cf (mnext state) config])

  inject call = ((call, Map.empty), (), (bot, 0))

-- Add Garbage Collection
instance GarbageCollector (Concrete () (Store CAddr, Int)) (PΣ CAddr)

