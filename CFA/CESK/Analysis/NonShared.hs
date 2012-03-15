{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module CFA.CESK.Analysis.NonShared where

import Data.Map as Map
import Data.Set as Set

import CFA.Lattice
import CFA.CFAMonads
import CFA.Store

import CFA.CESK
import CFA.CESK.Analysis

----------------------------------------------------------------------  
-- ABSTRACT INTERPRETATION
----------------------------------------------------------------------  

type D a = ℙ (Storable a)

instance (StoreLike Addr s (D Addr), Truncatable Time) 
   => Analysis (GenericAnalysis)
               Addr                        -- address type
               ()                          -- no shared result
               (Time, State Addr, s)       -- Generic Analysis' guts
               where
  tick ctx@(Ref (_, _), ρ, a) = GCFA (\(t, s, σ) -> [((), (t, ctx, σ))])
  tick ctx@(App (_, _, l), ρ, a) = GCFA (\(t, s, σ) -> [((), (TLab l (contour t), ctx, σ))])
  tick ctx@(v, ρ, a) = GCFA (\(TLab l ctr, s, σ) -> 
                       [case κ of 
                           Ar _ -> ((), (TLab l ctr, ctx, σ))
                           Fn _ -> ((), (trunc $ TMt (l : ctr), ctx, σ)) 
                        | Cont κ <- Set.toList $ fetch σ a])

  getVar ρ x   = GCFA (\(t, s, σ) -> 
                  let clos = fetch σ (ρ ! x)
                   in [(clo, (t, s, σ)) | Val clo <- Set.toList clos])

  putVar ρ x b c = GCFA (\(t, s, σ) -> do
                  let d  = (Set.singleton (Val c))
                      σ' = bind σ b d
                      ρ' = ρ // [(x, b)]
                  return (ρ', (t, s, σ')))

  loadCont a   = GCFA (\(t, s, σ) -> 
                  let ks = fetch σ a
                   in [(κ, (t, s, σ)) | Cont κ <- Set.toList ks])

  storeCont b κ  = GCFA (\(t, s, σ) -> do
                  let d  = (Set.singleton (Cont κ))
                      σ' = bind σ b d
                  return ((), (t, s, σ')))

  alloc _       = GCFA (\(t, s, σ) -> do
                  [(a, (t, s, σ)) | a <- allocKCFA t s σ])

  stepAnalysis _ config state = ((), gf (mstep state) config)

  inject call = let initState = (call, Map.empty, Call "mt" [])
                 in (initState, (), (TMt [], initState, σ0))



-- abstract allocator function
-- nondeterministic because of stored continuations
allocKCFA :: StoreLike Addr s (D Addr) => Time -> State Addr -> s -> [Addr]
allocKCFA t (App (e0, _, _), _ ,_) σ = [Call (lab e0) (contour t)]
allocKCFA t (Lam _, _, a) σ = 
      [case κ of
            Ar (e, _, _)      -> Call (lab e) (contour t)
            Fn ((x, _), _, _) -> Bind x (contour t) 
       | Cont κ <- Set.toList $ fetch σ  a]

instance GarbageCollector (GenericAnalysis () (Time, State Addr, s)) (State Addr)

type Store a = a :-> (D a)

instance StoreLike Addr (Store Addr) (D Addr) where
 σ0 = Map.empty  
 bind σ a d = σ ⨆ [a ==> d]
 fetch σ a = σ CFA.Lattice.!! a  
 replace σ a d = σ ⨆ [a ==> d]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ

