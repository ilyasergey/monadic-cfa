{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

module CFA.AFJ.Analysis.NonShared where

import Data.Map as Map
import Data.Set as Set
import Data.List as L
import Control.Monad.State
import Control.Monad.ListT
import Control.Monad.Identity

import CFA.Lattice
import CFA.Runner
import CFA.CFAMonads
import CFA.Store

import CFA.AFJ
import CFA.AFJ.Analysis

----------------------------------------------------------------------  
-- ABSTRACT INTERPRETATION
----------------------------------------------------------------------  
type D a = ℙ (Storable a)

instance (StoreLike Addr s (D Addr), Truncatable Time) => 
         AFJCESKInterface (StorePassingSemantics s Time) Addr where

  tick ctx@(stmts, _, _) = modify $ 
                           \t -> trunc ((lab (head stmts)):t)

  getObj β v =  lift $ getsNDSet $ 
                \σ -> Set.map (\(Val d) -> d) $ fetch σ (β!v)

  putObj β v d =  lift $ modify $ 
                  \σ -> bind σ  (β!v) (Set.singleton (Val d))

  getCont pk =  lift $ getsNDSet $ 
                \σ -> Set.map (\(Cont κ) -> κ) $ fetch σ pk

  putCont m κ 
    = do t <- get
         let b = alloc_k t m 
         lift $ modify $ \σ ->  bind σ b $ 
                                Set.singleton (Cont κ)
         return b

  initBEnv β vs'' vs''' 
    = do t <- get 
         let pairs'   =  L.map (\v -> (v, alloc t v)) vs''
             pairs''  =  L.map (\v -> (v, alloc t v)) vs'''
         return $ β // pairs' // pairs''

  getMethod table (cn, _) m = return $ method table cn m

  getConstr table cn  = do t <- get
                           σ <- lift get
                           -- updates a store and returns an environment of all class fields
                           return $ createConstr table cn σ t

createConstr table cn σ t ds =
  do σ' <- lift get 
     let fs = allFields table cn -- compute all fields
         as = L.map (alloc t) fs    -- appropriate addresses for fields
         fBindings = zip fs as    -- bindings [field |-> addr]
         -- mapping from all class fields to provided arguments
         fMappings = Map.empty // classFieldMappings table cn ds 
         -- heap is updated according to the mappings
         pairs = [(ai, Set.singleton (Val $ fMappings ! fi)) 
                 | (fi, ai) <- fBindings] 
         σ'' = L.foldl (\store (ai, di) -> bind store ai di) σ' pairs
         -- new environment is created
         β' = Map.empty // fBindings
     lift $ modify (\_ -> σ'')
     return β' 



----------------------------------------------------------------------------
-- Store machinery
----------------------------------------------------------------------------

alloc :: (Truncatable Time) => Time -> Var -> Addr
alloc t v = AVar v $ trunc t

alloc_k :: (Truncatable Time) => Time -> MethodName -> Addr
alloc_k t m = ACall m $ trunc t

type Store a = a :-> (D a)

instance StoreLike Addr (Store Addr) (D Addr) where
 σ0 = Map.empty  
 bind σ a d = σ ⨆ [a ==> d]
 fetch σ a = σ CFA.Lattice.!! a  
 replace σ a d = σ ⨆ [a ==> d]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ

----------------------------------------------------------------------------
-- Runner machinery
----------------------------------------------------------------------------

instance (Ord s, StoreLike Addr s (D Addr), Truncatable Time) => 
         AddStepToFP (StorePassingSemantics s Time)
                     (PState Addr)
                     (Set (PState Addr, Time, s)) where
  applyStep step =
    joinWith 
      (\(p, t, σ) -> Set.fromList $ L.map (\((a, b), c) -> (a, b, c)) $
                            runIdentity $
                            collectListT (runStateT (runStateT (step p) t) σ))
  inject p = Set.singleton $ (p, initial, σ0)

----------------------------------------------------------------------------
-- Utility function to inject variables and stamtement to state          --
----------------------------------------------------------------------------
injectToState :: [Var] -> [Stmt] -> PState Addr
injectToState vars stmts = let t0 = [] 
                               as = L.map (alloc t0) vars
                               varBinds = L.zip vars as
                               a0 = ACall "main" []
                            in (stmts, Map.empty // varBinds, a0)
