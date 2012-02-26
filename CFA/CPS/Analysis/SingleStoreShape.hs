{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.SingleStoreShape where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.CFAMonads
import CFA.CPS.Analysis
import CFA.CPS.Analysis.SingleStore.SingleStoreGC

-- Shape analysis
instance (Addressable a t, StoreLike a s, AlkaliLike a s) 
   => Analysis (SingleStoreAnalysis a) 
               a              
               s
               (ProcCh a, t)  
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
  arg ρ (Ref v) = SSFA (\σ -> \( ch, t) -> 
    let procs = fetch σ (ρ!v)
     in (σ, [ (procs, (ch,t)) ]))

  a $= d = SSFA (\σ -> \(ch, t) -> 
    let σ' = deAnodizeStore σ 
        σ'' = bind σ' a (deAnodizeD σ d)
    in (σ'', [((), (ch, t))] ))

  alloc v = SSFA (\σ -> \(ch, t) -> 
    let addr = valloc v t
        σ' = addUniqueAddr addr
     in (σ', [(addr, (ch, t))]))

  updateEnv ρ bs = SSFA (\σ -> \( ch, t) -> 
    let ρ' = deAnodizeEnv σ ρ
     in (σ, [ (ρ' // bs, (ch,t)) ]))

  tick ps = SSFA (\σ -> \ (Just proc, t) ->
     (σ, ([((), (Just proc, advance proc ps t))])))

  stepAnalysis store config state = runWithStore (mnext state >>= gc) (reset store) config

  inject call = ((call, Map.empty), σ0, (Nothing, τ0))
