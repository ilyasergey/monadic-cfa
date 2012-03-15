{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

module CFA.AFJ.Analysis where

import Data.Map as Map
import Data.Set as Set
import Data.List as L

import CFA.Lattice
import CFA.Store

import CFA.AFJ

----------------------------------------------------------------------  
-- State-Space
----------------------------------------------------------------------  

-- a - for addresses
type BEnv a = Var :-> a
type Kont a = (Var, [Stmt], BEnv a, a)
type State a = ([Stmt], BEnv a, a)
type Obj a = (ClassName, BEnv a)

class (Eq a, Ord a) => Address a

data Storable a = Val (Obj a)
       | Cont (Kont a)
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------  
-- k-CFA addresses
----------------------------------------------------------------------  

data Addr = AVar Var [Lab]
          | ACall MethodName [Lab]
  deriving (Eq, Ord, Show)

type Time = [Lab]

instance Address Addr

---------------------------------------------------------------------  
-- Abstract analysis interface.
----------------------------------------------------------------------  

-- Hint: Add new primitives as they appear in the semantics
class Monad (m s g) => Analysis m a s g | g -> m, m -> s, g -> a where
  tick           :: State a -> m s g ()
  getObj         :: BEnv a -> Var -> m s g (Obj a)
  putObj         :: BEnv a -> Var -> Obj a -> m s g ()
  getCont        :: a -> m s g (Kont a)
  putCont        :: MethodName -> (Kont a) -> m s g a
  getConstr      :: ClassTable -> ClassName -> m s g ([Obj a] -> m s g (BEnv a))
  getMethod      :: ClassTable -> Obj a -> MethodName -> m s g Method
  initBEnv       :: BEnv a -> [Var] -> [Var] -> m s g (BEnv a)

  stepAnalysis   :: ClassTable -> s -> g -> State a -> (s, [(State a, g)])
  inject         :: [Stmt] -> (State a, s, g)

mstep :: (Analysis m a s g) => ClassTable -> State a -> m s g (State a)
mstep table ctx@((Asgn v v' l):succ, β, pk) = do
      tick ctx
      d <- getObj β v'
      putObj β v d
      return $! (succ, β, pk) 
mstep table ctx@((Ret v l):[], β, pk) = do
      tick ctx
      (v', s, β', pk') <- getCont pk
      d <- getObj β v
      putObj β' v' d
      return $! (s, β', pk')
mstep table ctx@((Lkp v v' f l):succ, β, pk) = do
      tick ctx
      (c, β') <- getObj β v'
      d <- getObj β' f
      putObj β v d
      return $! (succ, β, pk)
mstep table ctx@((Cast v cn v' l):succ, β, pk) = do
      tick ctx
      d <- getObj β v'
      putObj β v d
      return $! (succ, β, pk) 
mstep table ctx@((New v cn vs l):succ, β, pk) = do
      tick ctx
      ructor <- getConstr table cn
      ds <- sequence [getObj β vi | vi <- vs]    
      β' <- ructor ds
      let d' = (cn, β')
      putObj β v d'
      return $! (succ, β, pk)     
mstep table ctx@((MCall v v0 mthd vs l):succ, β, pk) = do
      tick ctx      
      d0 <- getObj β v0
      (cn, _ , params, locals, body) <- getMethod table d0 mthd
      ds <- sequence [getObj β vi | vi <- vs]    
      let κ = (v, succ, β, pk)
      pk' <- putCont mthd κ
      let vs'' = L.map snd params
      let vs''' = L.map snd locals
      let β' = Map.empty // ["this" ==> (β ! v0)]
      β'' <- initBEnv β' vs'' vs'''
      sequence [putObj β'' vi di | vi <- vs'' | di <- ds]
      return $! (body, β'', pk')     
      
