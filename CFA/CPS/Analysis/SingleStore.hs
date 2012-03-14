{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.SingleStore where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis
import CFA.CPS.Analysis.SingleStore.SingleStoreGC

instance (Addressable a t, StoreLike a s (D a), GarbageCollector ((SingleStoreAnalysis a) s g) a) 
   => Analysis (SingleStoreAnalysis a) 
               a                     -- address type
               s                     -- shared store
               (ProcCh a, t)         -- SingleStore Analysis' guts
               where
  fun ρ (Lam l) = SSFA (\σ -> \(_,t) ->
    let proc = Clo(l, ρ) 
     in (σ, [(proc, (Just proc,t)) ]))
  fun ρ (Ref v) = SSFA (\σ -> \(_,t) -> 
    let procs = fetch σ (ρ!v)
     in (σ, [ (proc, (Just proc,t)) | proc <- Set.toList procs ])) 

  arg ρ (Lam l) = SSFA (\σ -> \(ch, t) -> 
    let proc = Clo(l, ρ) 
     in (σ, [ (Set.singleton proc, (ch, t)) ]))
  arg ρ (Ref v) = SSFA (\σ -> \(ch, t) -> 
    let procs = fetch σ (ρ!v)
     in (σ, [ (procs, (ch,t)) ]))

  a $= d = SSFA (\σ -> \(ch, t) -> 
    let σ' = bind σ a d
    in (σ', [((), (ch, t))] ))

  alloc v = SSFA (\σ -> \(ch, t) -> (σ, [(valloc v t, (ch, t))]))

  tick ps = SSFA (\σ -> \ (Just proc, t) ->
     (σ, ([((), (Just proc, advance proc ps t))])))

  stepAnalysis store config state = runWithStore (mnext state >>= gc) store config

  inject call = ((call, Map.empty), σ0, (Nothing, τ0))