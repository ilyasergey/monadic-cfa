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

alterFirst  f = modify $ \(a, b, c) -> (f a, b, c)
alterSecond f = modify $ \(a, b, c) -> (a, f b, c)
alterThird  f = modify $ \(a, b, c) -> (a, b, f c)

setSecond :: MonadState (s1,s2,s3) m => s2 -> m ()
setSecond = alterSecond . const

-- instance (Addressable a t, StoreLike a s (D a), 
--           MonadState (s, ProcCh a, t) m, MonadPlus m) 
--   => Analysis m a

getsND :: (MonadPlus m, MonadState s m) => (s -> [a]) -> m a
getsND f = do results <- gets f
              msum $ List.map return results

instance (Addressable a t, StoreLike a s (D a)) 
  => Analysis (GenericAnalysis (s, ProcCh a, t)) a
              where
     fun ρ (Lam l) = do let proc = Clo(l, ρ)
                        setSecond $ Just proc
                        return proc

     fun ρ (Ref v) = do σ <- gets first 
                        proc <- getsND $ Set.toList . (flip fetch $ ρ!v) . first
                        setSecond $ Just proc
                        return proc
        
     arg ρ (Lam l) = return $ Set.singleton $ Clo(l, ρ)   
     arg ρ (Ref v) = gets $ flip fetch (ρ!v) . first
     
     a $= d = alterFirst $ \ σ -> bind σ a d

     alloc v = gets (valloc v . third)
     
     tick ps = do Just proc <- gets second
                  alterThird $ advance proc ps

  -- stepAnalysis _ config state = ((), gf (mnext state) config)

  -- inject call = ((call, Map.empty), (), (Nothing, σ0, τ0))

-- Garbage Collection
instance GarbageCollector (GenericAnalysis (ProcCh a, s, t)) (PΣ a)
