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
import Data.List as List

import Control.Monad.State
import Control.Monad.ListT
import Control.Monad.Identity

import CFA.Lattice
import CFA.CFAMonads
import CFA.Runner
import CFA.Store

import CFA.CESK
import CFA.CESK.Analysis

----------------------------------------------------------------------  
-- ABSTRACT INTERPRETATION
----------------------------------------------------------------------  

type D a = ℙ (Storable a)
type NDStore a = a :-> (D a)

instance (StoreLike Addr s (D Addr), Truncatable Time) => 
         LambdaCESKInterface (StorePassingSemantics s (Time, PState Addr)) Addr where

  tick ctx@(Ref (_, _), ρ, a) 
    = modify $ \(t, _) -> (t, ctx)    
  tick ctx@(App (_, _, l), ρ, a) 
    = modify $ \(t, _) -> (TLab l (contour t), ctx)
  tick ctx@(v, ρ, a) 
    = do (t, s) <- get
         σ      <- lift get
         case t of 
          TLab l ctr -> 
           let ts = [case κ of 
                      Mt   -> (TMt (l:ctr), ctx)
                      Ar _ -> (TLab l ctr, ctx)
                      Fn _ -> (TMt (l:ctr), ctx)
                      | Cont κ <- Set.toList $ fetch σ a]
           in mapM put ts >> return ()            
          _          -> return ()

  getVar ρ x 
    = lift $ getsNDSet $ (\σ -> Set.map (\(Val c) -> c) $ 
                                fetch σ (ρ ! x))

  putVar ρ x b c 
     = (lift $ modify $ \σ -> bind σ b $ Set.singleton $ Val c) >> 
       (return $ ρ // [(x, b)])

  loadCont a  
     = lift $ getsNDSet (\σ -> Set.map (\(Cont κ) -> κ) $ 
                                                fetch σ a)

  storeCont b κ 
     = lift $ modify $ \σ -> bind σ b $ Set.singleton (Cont κ)

  alloc _       =  do (t, s) <- get
                      σ      <- lift get
                      pureND $ allocKCFA t s σ 

-- abstract allocator function
-- nondeterministic because of stored continuations
allocKCFA ::  StoreLike Addr s (D Addr) => 
              Time -> PState Addr -> s -> [Addr]
allocKCFA t (App (e0, _, _), _ ,_) σ 
  = [Call (lab e0) (contour t)]
allocKCFA t (Lam _, _, a) σ = 
      [case κ of
            Ar (e, _, _)      -> Call (lab e) (contour t)
            Fn ((x, _), _, _) -> Bind x (contour t) 
       | Cont κ <- Set.toList $ fetch σ  a]

instance StoreLike Addr (NDStore Addr) (D Addr) where
 σ0 = Map.empty  
 bind σ a d = σ ⨆ [a ==> d]
 fetch σ a = σ CFA.Lattice.!! a  
 replace σ a d = σ ⨆ [a ==> d]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ


---------------------------------------------------------------
-- Runner                                                    --
---------------------------------------------------------------
instance (Ord s, StoreLike Addr s (D Addr), Truncatable Time) => 
         AddStepToFP (StorePassingSemantics s (Time, PState Addr))
                     (PState Addr)
                     (Set (PState Addr, Time, s)) where
  applyStep step =
    joinWith 
      (\(p, t, σ) -> Set.fromList $ List.map (\((a, (b, c)), d) -> (a, b, d)) $
                            runIdentity $
                            collectListT (runStateT (runStateT (step p) (t, p)) σ))
  inject p = Set.singleton $ (p, initial, σ0)