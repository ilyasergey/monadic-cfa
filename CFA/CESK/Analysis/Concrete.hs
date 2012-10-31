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
import Data.List as List
import Data.Traversable
import Control.Monad.State
import Control.Monad.ListT
import Control.Monad.Identity
import Control.Monad.Reader

import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.Runner

import CFA.CESK
import CFA.CESK.Analysis

----------------------------------------------------------------------  
-- CONCRETE INTERPRETATION
----------------------------------------------------------------------  

type Store a = a :-> (Storable a)

instance LambdaCESKInterface (StorePassingSemantics (Store Addr) (Time, PState Addr)) Addr where

  tick ctx@(Ref (_, _), ρ, a) = modify $ \(t, _) -> (t, ctx)
  tick ctx@(App (_, _, l), ρ, a) = modify $ \(t, _) -> (TLab l (contour t), ctx)
  tick ctx@(v, ρ, a) = do (t, s) <- get
                          σ      <- lift get
                          case t of 
                            TLab l ctr -> 
                                 let (Cont κ) = σ ! a
                                  in case κ of 
                                       Mt   -> put (TMt (l:ctr), ctx)
                                       Ar _ -> put (TLab l ctr, ctx)
                                       Fn _ -> put (TMt (l:ctr), ctx)
                            _          -> return ()

  getVar ρ x = lift $ getsNDSet (\σ -> let (Val clo) = σ ! (ρ ! x)
                                       in Set.singleton(clo))

  putVar ρ x b c = (lift $ modify $ \σ -> σ // [(b, Val c)]) >> 
                   (return $ ρ // [(x, b)])
                  
  loadCont a  = lift $ getsNDSet (\σ -> 
                 let (Cont κ) = σ ! a
                  in Set.singleton κ)

  storeCont b κ = lift $ modify $ \σ -> σ // [(b, Cont κ)]

  alloc _       =  do (t, s) <- get
                      σ      <- lift get
                      return $ allocC t s σ 

-- Concrete allocator function
-- Turns the last captured time moment into the address
allocC :: Time -> PState Addr -> Store Addr -> Addr
allocC t (App (e0, _, _), _ ,_) σ = Call (lab e0) (contour t)
allocC t (Lam _, _, a) σ = 
      case σ ! a of
        Cont (Ar (e, _, _))      -> Call (lab e) (contour t)
        Cont (Fn ((x, _), _, _)) -> Bind x (contour t)


instance AddStepToFP (StorePassingSemantics (Store Addr) (Time, PState Addr)) 
                     (PState Addr)
                     (Set (PState Addr, Time, Store Addr)) where
  applyStep step =
    joinWith 
      (\(p, t, σ) -> Set.fromList $ List.map (\((a, (b, c)), d) -> (a, b, d)) $
                            runIdentity $
                            collectListT (runStateT (runStateT (step p) (t, p)) σ))
  inject p = Set.singleton $ (p, initial, Map.empty)