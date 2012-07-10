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
import CFA.CESK
import CFA.Runner

----------------------------------------------------------------------  
-- Abstract analysis interface.
----------------------------------------------------------------------  
class Monad m => Analysis m a | m -> a where 
  tick      :: PState a -> m ()
  getVar    :: Env a -> Var -> m (Clo a)
  putVar    :: Env a -> Var -> a -> Clo a -> m (Env a)
  loadCont  :: a -> m (Kont a)
  storeCont :: a -> Kont a -> m ()
  alloc     :: () -> m a

-- A small-step monadic semantics for CESK* machine
-- in Store- and Time- passing style

----------------------------------------------------------------------  
-- Generic transition
----------------------------------------------------------------------  
mstep :: (Analysis m a) => PState a -> m (PState a)
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
 -- Running the analysis
----------------------------------------------------------------------

runAnalysis :: (Lattice fp , AddStepToFP m (PState a) fp, 
                HasInitial a, Analysis m a) =>
               Exp -> fp
runAnalysis e = exploreFP mstep (e, Map.empty, initial)
