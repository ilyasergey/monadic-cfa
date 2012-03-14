{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}

module CFA.CESK.Analysis.Concrete where  

import Data.Map as Map
import Data.Set as Set

import CFA.Lattice
import CFA.Store
import CFA.CFAMonads

import CFA.CESK
import CFA.CESK.Analysis

----------------------------------------------------------------------  
-- TIME-STAMPED ADDRESSES (FIXED)
----------------------------------------------------------------------  

data Addr = Bind Var [Lab]
          | Call Lab [Lab]
  deriving (Eq, Ord, Show)

data Time = TLab Lab [Lab]
          | TMt [Lab]
  deriving (Eq, Ord, Show)

contour :: Time -> [Lab]
contour (TLab _ c) = c
contour (TMt c) = c

instance Address Addr

----------------------------------------------------------------------  
-- CONCRETE INTERPRETATION
----------------------------------------------------------------------  

data D = Val (Clo Addr)
       | Cont (Kont Addr)
  deriving (Eq, Ord)

type Store = Addr :-> D

instance Analysis Concrete 
                  Addr 
                  () 
                  (Time, State Addr, Store) where
  tick ctx@(Ref (_, _), ρ, a) = Concrete (\(t, s, σ) -> ((), (t, ctx, σ)))
  tick ctx@(App (_, _, l), ρ, a) = Concrete (\(t, s, σ) -> ((), (TLab l (contour t), ctx, σ)))
  tick ctx@(v, ρ, a) = Concrete (\(TLab l ctr, s, σ) -> 
                       let (Cont κ) = σ ! a
                        in case κ of 
                           Ar _ -> ((), (TLab l ctr, ctx, σ))
                           Fn _ -> ((), (TMt (l:ctr), ctx, σ)))

  getVar ρ x = Concrete (\(t, s, σ) -> 
                 let (Val clo) = σ ! (ρ ! x)
                  in (clo, (t, s, σ)))

  putVar ρ x c = Concrete (\(t, s, σ) -> 
                 let b  = alloc t s σ
                     σ' = σ // [(b, Val c)]
                  in (ρ // [(x, b)], (t, s, σ')))

  loadCont a  = Concrete (\(t, s, σ) -> 
                 let (Cont κ) = σ ! a
                  in (κ, (t, s, σ)))

  storeCont κ = Concrete (\(t, s, σ) -> 
                 let b  = alloc t s σ
                     σ' = σ // [(b, Cont κ)]
                  in (b, (t, s, σ')))
  

-- Concrete allocator function
-- Turns the last captured time moment into the address
alloc :: Time -> State Addr -> Store -> Addr
alloc t (App (e0, _, _), _ ,_) σ = Call (lab e0) (contour t)
alloc t (Lam _, _, a) σ = 
      case σ ! a of
        Cont (Ar (e, _, _))      -> Call (lab e) (contour t)
        Cont (Fn ((x, _), _, _)) -> Bind x (contour t)


instance GarbageCollector (Concrete () (Time, State Addr, Store)) (State Addr)