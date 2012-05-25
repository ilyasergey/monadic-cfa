{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.NonShared where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Traversable
import Control.Monad.State
import Control.Monad.List
import Control.Monad.Identity

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis

type GenericAnalysis g = StateT g (ListT Identity)

first  (a, b, c) = a
second (a, b, c) = b
third  (a, b, c) = c

alterFirst  a' = modify $ \(a, b, c) -> (a', b, c)
alterSecond b' = modify $ \(a, b, c) -> (a, b', c)
alterThird  c' = modify $ \(a, b, c) -> (a, b, c')

-- instance (Addressable a t, StoreLike a s (D a), 
--           MonadState (s, ProcCh a, t) m, MonadPlus m) 
--   => Analysis m a

instance (Addressable a t, StoreLike a s (D a)) 
  => Analysis (GenericAnalysis (s, ProcCh a, t)) a
              where
     fun ρ (Lam l) = let proc = Clo(l, ρ)
                      in do alterSecond $ Just proc
                            return $ proc

     fun ρ (Ref v) = do σ <- gets first 
                        procs <- gets $ Set.toList . (flip fetch $ ρ!v) . first
                        proc <- msum $ List.map return procs
                        alterSecond $ Just proc
                        return proc
        
     arg ρ (Lam l) = return $ Set.singleton $ Clo(l, ρ)   
     arg ρ (Ref v) = gets $ (flip fetch (ρ!v)) . first
     
     a $= d = do σ <- gets first
                 alterFirst $ bind σ a d

     alloc v = do t <- gets third 
                  return (valloc v t)   
     
     tick ps = do Just proc <- gets second
                  t <- gets third
                  alterThird $ advance proc ps t

  -- stepAnalysis _ config state = ((), gf (mnext state) config)

  -- inject call = ((call, Map.empty), (), (Nothing, σ0, τ0))

-- Garbage Collection
instance GarbageCollector (GenericAnalysis (ProcCh a, s, t)) (PΣ a)
