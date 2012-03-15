{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

module CFA.AFJ.Analysis.AbstractNonShared where

import Data.Map as Map
import Data.Set as Set
import Data.List as L

import CFA.Lattice
import CFA.CFAMonads
import CFA.Store

import CFA.AFJ
import CFA.AFJ.Analysis

----------------------------------------------------------------------  
-- ABSTRACT INTERPRETATION
----------------------------------------------------------------------  
type D a = ℙ (Storable a)

instance (StoreLike Addr s (D Addr), Truncatable Time) 
   => Analysis (GenericAnalysis)
               Addr                        -- address type
               ()                          -- no shared result
               (Time, s)                   -- Generic Analysis' guts
               where
  tick ctx@(stmts, _, _) = GCFA (\(t, σ) -> [((), (trunc ((lab (head stmts)):t), σ))])
  
  getObj β v = GCFA (\(t, σ) -> 
               [(d, (t, σ)) | Val d <- Set.toList $ fetch σ (β!v)])

  putObj β v d = GCFA (\(t, σ) -> 
                 let σ' = bind σ  (β!v) (Set.singleton (Val d))
                  in [((), (t, σ'))])

  getCont pk = GCFA (\(t, σ) -> 
               [(κ, (t, σ)) | Cont κ <- Set.toList $ fetch σ pk])

  putCont m κ = GCFA (\(t, σ) -> 
                let b = alloc_k t m 
                    σ' = bind σ b $ Set.singleton (Cont κ)
                 in [(b, (t, σ'))])

  initBEnv β vs'' vs''' = GCFA (\(t, σ) -> 
                           let pairs' = L.map (\v -> (v, alloc t v)) vs''
                               pairs'' = L.map (\v -> (v, alloc t v)) vs'''
                               β' = β // pairs' // pairs'' in
                           [(β', (t, σ))])

  getConstr cn  = GCFA (\(t, σ) ->  
             -- updates a store and returns an environment of all class fields
             let ructor = (\ds -> GCFA(\(t', σ') -> 
                   let fs = allFields ?table cn -- compute all fields
                       as = L.map (alloc t) fs    -- appropriate addresses for fields
                       fBindings = zip fs as    -- bindings [field |-> addr]
                       -- mapping from all class fields to provided arguments
                       fMappings = Map.empty // classFieldMappings ?table cn ds 
                       -- heap is updated according to the mappings
                       pairs = [(ai, Set.singleton (Val $ fMappings ! fi)) | (fi, ai) <- fBindings] 
                       σ'' = foldl (\store (ai, di) -> bind store ai di) σ' pairs
                       -- new environment is create
                       β' = Map.empty // fBindings
                    in [(β', (t', σ''))]))
             in [(ructor, (t, σ))])

  getMethod (cn, _) m = GCFA (\(t, σ) -> [(method ?table cn m, (t, σ))])

alloc :: Time -> Var -> Addr
alloc t v = AVar v $ trunc t

alloc_k :: Time -> MethodName -> Addr
alloc_k t m = ACall m $ trunc t

instance Truncatable [Lab] where
  trunc ls = take 1 ls