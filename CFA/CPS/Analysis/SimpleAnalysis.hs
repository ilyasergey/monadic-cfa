{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.SimpleAnalysis where

import Data.Maybe
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Foldable as Foldable
import Data.Traversable
import Control.Monad.State
import Control.Monad.ListT
import Control.Monad.Identity
import Control.Monad.Reader

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis
import CFA.Runner

import Util

----------------------------------------------------------------------
-- integer time-stamped concrete interpreter
----------------------------------------------------------------------


instance Analysis (StorePassingSemantics (Store Integer) Integer) Integer
              where
     fun ρ (Lam l) = return $ Clo(l, ρ)
     fun ρ (Ref v) = lift $ getsNDSet $ \σ -> σ!(ρ!v) 
        
     arg ρ (Lam l) = return $ Clo(l, ρ)   
     arg ρ (Ref v) = lift $ getsNDSet $ \σ -> σ!(ρ!v)
     
     a $= d = lift $ modify $ \σ -> Map.insert a (Set.singleton d) σ
     alloc v = gets id     
     tick proc ps = modify $ \t -> t + 1

instance HasInitial Integer where
  initial = 0

instance (Ord a, StoreLike a s (D a))
         => GarbageCollector (StorePassingSemantics s t) (PΣ a) where
  gc ps = do
    σ <- lift get
    let rs = Set.map (\(v, a) -> a) (reachable ps σ)
    lift $ modify $ \ σ -> filterStore σ (\a -> Set.member a rs)
    return ()


instance (Ord s, Ord a, Ord g, HasInitial g, Lattice s) =>
         AddStepToFP (StorePassingSemantics s g) a
         (ℙ ((a, g), s)) where
  applyStep step fp =
    joinWith 
      (\((p,t),s) -> Set.fromList $ runIdentity $
                     collectListT (runStateT (runStateT (step p) t) s))
      fp
  inject p = Set.singleton $ ((p, initial), bot)

idx  = Lam (["x"] :=> Call (Ref "x") [])
idy  = Lam (["y"] :=> Exit)
comb = Lam (["f", "g"] :=> Call (Ref "f") [Ref "g"])
ex   = Call comb [idx, idy]

result e = runAnalysis e :: ℙ ((PΣ Integer, Integer), Store Integer)