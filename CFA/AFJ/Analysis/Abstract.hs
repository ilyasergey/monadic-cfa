{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

module CFA.AFJ.Analysis.Abstract where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Lattice
import CFA.Store

import CFA.AFJ
import CFA.AFJ.Analysis

{----------------- TIME-STAMPED ADDRESSES ------------------}

data Addr = AVar Var [Lab]
          | ACall MethodName [Lab]
  deriving (Eq, Ord, Show)

type Time = [Lab]

instance Address Addr


{---------------- CONCRETE INTERPRETATION ----------------}

data D = Val (Obj Addr)
       | Cont (Kont Addr)
  deriving (Eq, Ord)

-- TODO: implement the concrete interpreter

{---------------- ABSTRACT INTERPRETATION ----------------}

-- Used EXACTLY the same monad as for KCFA in Lambda

data KCFA a = KCFA { kf :: !((Time, AStore) -> [(a, Time, AStore)]) }

--TODO is it possible to abstract over the list structure?
type D1 = (ℙ D)

type AStore = Addr :-> D1

k = 1

instance Monad KCFA where
   return a = KCFA (\(t, σ) -> [(a, t, σ)]) 
   (>>=) (KCFA f) g = KCFA (\ (t, σ) ->
     let chs = f(t, σ)
      in concatMap (\ (a, t', σ') -> (kf $ g(a))(t', σ')) chs)

instance JavaSemanticInterface KCFA Addr where
  tick ctx@(stmts, _, _) = KCFA (\(t, σ) -> [((), take k ((lab (head stmts)):t), σ)])
  
  getObj β v = KCFA (\(t, σ) -> 
               [(d, t, σ) | Val d <- Set.toList $ σ!(β!v)])

  putObj β v d = KCFA (\(t, σ) -> 
                 [((), t, σ ⊎ [(β!v) ==> (Set.singleton (Val d))])])

  getCont pk = KCFA (\(t, σ) -> 
               [(κ, t, σ) | Cont κ <- Set.toList $ σ ! pk])

  putCont m κ = KCFA (\(t, σ) -> 
                let b = alloc_k t m in
                [(b, t, σ ⊎ [b ==> (Set.singleton (Cont κ))])])

  initBEnv β vs'' vs''' = KCFA (\(t, σ) -> 
                           let pairs' = map (\v -> (v, alloc t v)) vs''
                               pairs'' = map (\v -> (v, alloc t v)) vs''' in
                           let β' = β // pairs' // pairs'' in
                           [(β', t, σ)])

  getC cn  = KCFA (\(t, σ) ->  
             -- updates a store and returns an environment of all class fields
             let ructor = (\ds -> KCFA(\(t', σ') -> 
                   let fs = allFields ?table cn -- compute all fields
                       as = map (alloc t) fs    -- appropriate addresses for fields
                       fBindings = zip fs as    -- bindings [field |-> addr]
                       -- mapping from all class fields to provided arguments
                       fMappings = Map.empty // classFieldMappings ?table cn ds 
                       -- heap is updated according to the mappings
                       σ'' = σ' ⊎ [ai ==> (Set.singleton (Val $ fMappings ! fi)) | (fi, ai) <- fBindings]
                       -- new environment is create
                       β' = Map.empty // fBindings
                    in [(β', t', σ'')]))
             in [(ructor, t, σ)])

  getM (cn, _) m = KCFA (\(t, σ) -> [(method ?table cn m, t, σ)])

alloc :: Time -> Var -> Addr
alloc t v = AVar v (take k t)

alloc_k :: Time -> MethodName -> Addr
alloc_k t m = ACall m (take k t)
