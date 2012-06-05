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

module CFA.CPS.Analysis.ReallyNonShared where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Traversable
import Control.Monad.State
import Control.Monad.List
import Control.Monad.Identity
import Control.Monad.Reader

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis
import CFA.CPS.Analysis.Runner

import Util

type GenericAnalysis s0 s g = ReaderT g (StateT s (SharedStateListT s0 Identity))
-- GenericAnalysis s0 s g a =
--   SharedStateListT s (StateT g (SharedStateListT s0 Identity)) 
--   s -> StateT g (SharedStateListT s0 Identity) (s, [a])
--   s -> g -> s0 -> (s0, [(g, (s, [a]))])

-- instance (Addressable a t, StoreLike a s (D a), 
--           MonadState (s, ProcCh a, t) m, MonadPlus m) 
--   => Analysis m a
instance (Addressable a t, StoreLike a s (D a), Lattice s0) 
  => Analysis (GenericAnalysis s0 s (ProcCh a, t)) a
              where
     fun ρ (Lam l) = return $ Clo(l, ρ)
     fun ρ (Ref v) = getsNDSet $ (flip fetch $ ρ!v) 
        
     arg ρ (Lam l) = return $ Clo(l, ρ)   
     arg ρ (Ref v) = getsNDSet $ flip fetch (ρ!v) 
     
     a $= d = modify $ \ σ -> bind σ a (Set.singleton d)

     alloc v = asks (valloc v . snd)
     
     tick proc ps = local $ \(_, t) -> (Just proc, advance proc ps t)

-- Garbage Collection
instance (Lattice s0, Lattice s) =>
         GarbageCollector (GenericAnalysis s0 s (ProcCh a, t)) (PΣ a)

instance (Lattice s, Ord a, Ord g, Ord s) => 
         FPCalc (GenericAnalysis (Set (PΣ a, s, g)) s g) (PΣ a) where
  hasSeen p =
    do s <- get
       g <- ask
       lift $ lift $ gets $ Set.member (p, s, g)
  markSeen p = 
    do s <- get
       g <- ask
       lift $ lift $ modify $ Set.insert (p, s, g)

