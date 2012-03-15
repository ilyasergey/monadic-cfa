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
-- CONCRETE INTERPRETATION
----------------------------------------------------------------------  

type Store a = a :-> (Storable a)

instance Analysis Concrete 
                  Addr 
                  () 
                  (Time, State Addr, Store Addr) where
  tick ctx@(Ref (_, _), ρ, a) = Concrete (\(t, s, σ) -> ((), (t, ctx, σ)))
  tick ctx@(App (_, _, l), ρ, a) = Concrete (\(t, s, σ) -> ((), (TLab l (contour t), ctx, σ)))
  tick ctx@(v, ρ, a) = Concrete (\(t, s, σ) -> 
                        case t of 
                          TLab l ctr -> (let (Cont κ) = σ ! a
                                         in case κ of 
                                            Mt   -> ((), (TMt (l:ctr), ctx, σ))
                                            Ar _ -> ((), (TLab l ctr, ctx, σ))
                                            Fn _ -> ((), (TMt (l:ctr), ctx, σ)))
                          _          -> ((), (t, s, σ)))

  getVar ρ x = Concrete (\(t, s, σ) -> 
                 let (Val clo) = σ ! (ρ ! x)
                  in (clo, (t, s, σ)))

  putVar ρ x b c = Concrete (\(t, s, σ) -> 
                 let σ' = σ // [(b, Val c)]
                  in (ρ // [(x, b)], (t, s, σ')))

  loadCont a  = Concrete (\(t, s, σ) -> 
                 let (Cont κ) = σ ! a
                  in (κ, (t, s, σ)))

  storeCont b κ = Concrete (\(t, s, σ) -> 
                 let σ' = σ // [(b, Cont κ)]
                  in ((), (t, s, σ')))

  alloc _     = Concrete (\(t, s, σ) -> do
                  (allocC t s σ, (t, s, σ)))

  stepAnalysis _ config state = ((), [cf (mstep state) config])

  inject call = let initState = (call, Map.empty, Call "mt" [])
                    a0 = Call "mt" []
                 in (initState, (), (TMt [], initState, Map.empty // [(a0, Cont Mt)]))
  

-- Concrete allocator function
-- Turns the last captured time moment into the address
allocC :: Time -> State Addr -> Store Addr -> Addr
allocC t (App (e0, _, _), _ ,_) σ = Call (lab e0) (contour t)
allocC t (Lam _, _, a) σ = 
      case σ ! a of
        Cont (Ar (e, _, _))      -> Call (lab e) (contour t)
        Cont (Fn ((x, _), _, _)) -> Bind x (contour t)


instance GarbageCollector (Concrete () (Time, State Addr, Store Addr)) (State Addr)