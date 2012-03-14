{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module CFA.CESK.Analysis.Abstract where

import Data.Map as Map
import Data.Set as Set

import CFA.Lattice
import CFA.Store

import CFA.CESK
import CFA.CESK.Analysis



{---------------- ABSTRACT INTERPRETATION ----------------}

data KCFA a = KCFA { kf :: !((Time, State Addr, AStore) -> [(a, Time, State Addr, AStore)]) }

--TODO is it possible to abstract over the list structure?
type D1 = (ℙ D)

type AStore = Addr :-> D1

k = 1

instance Monad KCFA where
   return a = KCFA (\(t, s, σ) -> [(a, t, s, σ)]) 
   (>>=) (KCFA f) g = KCFA (\ (t, s, σ) ->
     let chs = f(t, s, σ)
      in concatMap (\ (a, t', s', σ') -> (kf $ g(a))(t', s', σ')) chs)

instance Analysis KCFA Addr where
  tick ctx@(Ref (_, _), ρ, a) = KCFA (\(t, s, σ) -> [((), t, ctx, σ)])
  tick ctx@(App (_, _, l), ρ, a) = KCFA (\(t, s, σ) -> [((), TLab l (contour t), ctx, σ)])
  tick ctx@(v, ρ, a) = KCFA (\(TLab l ctr, s, σ) -> 
                       [case κ of 
                           Ar _ -> ((), TLab l ctr, ctx, σ)
                           Fn _ -> ((), TMt (take k (l : ctr)), ctx, σ) 
                        | Cont κ <- Set.toList (σ ! a)])

  getVar ρ x   = KCFA (\(t, s, σ) -> 
                  let clos = σ ! (ρ ! x)
                   in [(clo, t, s, σ) | Val clo <- Set.toList clos])

  putVar ρ x c = KCFA (\(t, s, σ) -> do
                  b <- allocKCFA t s σ
                  let d  = (Set.singleton (Val c))
                      σ' = σ ⊎ [b ==> d]
                      ρ' = ρ // [(x, b)]
                  return (ρ', t, s, σ'))

  loadCont a   = KCFA (\(t, s, σ) -> 
                  let ks = σ ! a
                   in [(κ, t, s, σ) | Cont κ <- Set.toList ks])

  storeCont κ  = KCFA (\(t, s, σ) -> do
                  b <- allocKCFA t s σ
                  let d  = (Set.singleton (Cont κ))
                      σ' = σ ⊎ [b ==> d]
                  return (b, t, s, σ'))

-- abstract allocator function
-- similar to the concrete allocator
-- nondeterministic because of stored continuations
allocKCFA :: Time -> State Addr -> AStore -> [Addr]
allocKCFA t (App (e0, _, _), _ ,_) σ = [Call (lab e0) (contour t)]
allocKCFA t (Lam _, _, a) σ = 
      [case κ of
            Ar (e, _, _)      -> Call (lab e) (contour t)
            Fn ((x, _), _, _) -> Bind x (contour t) 
       | Cont κ <- Set.toList (σ ! a)]

