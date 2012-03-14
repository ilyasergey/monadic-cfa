{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.NonShared where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis

instance (Addressable a t, StoreLike a s (D a)) 
   => Analysis (GenericAnalysis)
               a                -- address type
               ()               -- no shared result
               (ProcCh a, s, t) -- Generic Analysis' guts
               where
  fun ρ (Lam l) = GCFA (\ (_,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (proc, (Just proc,σ,t)) ])
  fun ρ (Ref v) = GCFA (\ (_,σ,t) -> 
    let procs = fetch σ (ρ!v)
     in [ (proc, (Just proc,σ,t)) | proc <- Set.toList procs ]) 

  arg ρ (Lam l) = GCFA (\ (ch,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (Set.singleton proc, (ch, σ, t)) ])
  arg ρ (Ref v) = GCFA (\ (ch,σ,t) -> 
    let procs = fetch σ (ρ!v)
     in [ (procs, (ch, σ, t)) ])

  a $= d = GCFA (\ (ch,σ,t) -> [((),(ch,bind σ a d,t))] )

  alloc v = GCFA (\ (ch,σ,t) -> [(valloc v t, (ch, σ, t))])

  tick ps = GCFA (\ (Just proc, σ, t) ->
     [((), (Just proc, σ, advance proc ps t))])

  stepAnalysis _ config state = ((), gf (mnext state) config)

  inject call = ((call, Map.empty), (), (Nothing, σ0, τ0))

-- Garbage Collection
instance GarbageCollector (GenericAnalysis () (ProcCh a, s, t)) a
