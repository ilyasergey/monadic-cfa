{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

module CFA.AFJ.Analysis where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Lattice
import CFA.Store

import CFA.AFJ

{---------------- STATE-SPACE ----------------}                 

-- a - for addresses

type BEnv a = Var :-> a
type Kont a = (Var, [Stmt], BEnv a, a)
type State a = ([Stmt], BEnv a, a)
type Obj a = (ClassName, BEnv a)

class (Eq a, Ord a) => Address a

{----------------- MONADIC SEMANTICS ------------------}

-- Hint: Add new primitives as they appear in the semantics
class (Address a, Monad m) => JavaSemanticInterface m a where
  tick           :: State a -> m ()
  getObj         :: BEnv a -> Var -> m (Obj a)
  putObj         :: BEnv a -> Var -> Obj a -> m ()
  getCont        :: a -> m (Kont a)
  putCont        :: MethodName -> (Kont a) -> m a
  getC           :: (?table :: ClassTable) => ClassName -> m ([Obj a] -> m (BEnv a))
  getM           :: (?table :: ClassTable) => Obj a -> MethodName -> m Method
  initBEnv       :: BEnv a -> [Var] -> [Var] -> m (BEnv a)

 
mstep :: (JavaSemanticInterface m a, ?table :: ClassTable) => State a -> m (State a)
mstep ctx@((Asgn v v' l):succ, β, pk) = do
      tick ctx
      d <- getObj β v'
      putObj β v d
      return $! (succ, β, pk) 
mstep ctx@((Ret v l):[], β, pk) = do
      tick ctx
      (v', s, β', pk') <- getCont pk
      d <- getObj β v
      putObj β' v' d
      return $! (s, β', pk')
mstep ctx@((Lkp v v' f l):succ, β, pk) = do
      tick ctx
      (c, β') <- getObj β v'
      d <- getObj β' f
      putObj β v d
      return $! (succ, β, pk)
mstep ctx@((Cast v cn v' l):succ, β, pk) = do
      tick ctx
      d <- getObj β v'
      putObj β v d
      return $! (succ, β, pk) 
mstep ctx@((New v cn vs l):succ, β, pk) = do
      tick ctx
      ructor <- getC cn
      ds <- sequence [getObj β vi | vi <- vs]    
      β' <- ructor ds
      let d' = (cn, β')
      putObj β v d'
      return $! (succ, β, pk)     
mstep ctx@((MCall v v0 m vs l):succ, β, pk) = do
      tick ctx      
      d0 <- getObj β v0
      (cn, _ , params, locals, body) <- getM d0 m
      ds <- sequence [getObj β vi | vi <- vs]    
      let κ = (v, succ, β, pk)
      pk' <- putCont m κ
      let vs'' = map snd params
      let vs''' = map snd locals
      let β' = Map.empty // ["this" ==> (β ! v0)]
      β'' <- initBEnv β' vs'' vs'''
      sequence [putObj β'' vi di | vi <- vs'' | di <- ds]
      return $! (body, β'', pk')     
      
