{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CFA.CESK.Analysis where

-- Imports.
import Data.Map as Map
import Data.Set as Set

import CFA.Lattice
import CFA.Store

import CFA.CESK

----------------------------------------------------------------------  
-- Abstract analysis interface.
----------------------------------------------------------------------  
class Monad (m s g) => Analysis m a s g | g -> m, m -> s, g -> a where 
  tick      :: State a -> m s g ()
  getVar    :: Env a -> Var -> m s g (Clo a)
  putVar    :: Env a -> Var -> a -> Clo a -> m s g (Env a)
  loadCont  :: a -> m s g (Kont a)
  storeCont :: a -> Kont a -> m s g ()
  alloc     :: () -> m s g a


-- A small-step monadic semantics for CESK* machine
-- in Store- and Time- passing style

-- The underlying monad implemens a `time-state-store-passing style'
-- in order to disguise `alloc' calls, which use both time and state
-- (at least, in the abstract case)

----------------------------------------------------------------------  
-- Generic transition
----------------------------------------------------------------------  
mstep :: (Analysis m a s g) => State a -> m s g (State a)
mstep ctx@(Ref (x, l), ρ, a) = do
  tick ctx
  Clo (v, ρ', l) <- getVar ρ x
  return $! (Lam (v, l), ρ', a)
mstep ctx@(App (e0, e1, l), ρ, a) = do
  tick ctx
  b <- alloc ()
  storeCont b (Ar (e1, ρ, a))
  return (e0, ρ, b)
mstep ctx@(Lam (v, l), ρ, a) = do
  tick ctx
  κ <- loadCont a
  case κ of
    Ar (e, ρ, a) -> do
      b <- alloc ()
      storeCont b κ
      return (e, ρ, b)
    Fn ((x, e), ρ', c) -> do
      b <- alloc ()
      ρ'' <- putVar ρ' x b (Clo (v, ρ, l))
      return (e, ρ'', c)

----------------------------------------------------------------------
 -- Utility
----------------------------------------------------------------------

class Truncatable t where
  trunc :: t -> t