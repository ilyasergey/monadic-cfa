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
import CFA.CPS.Analysis.Runner

import Util

type TwoLevelAnalysis s g = StateT g (StateT s (ListT Identity))

-- TwoLevelAnalysis s g a =
--   StateT g (StateT s (ListT Identity)) a
--   g -> StateT s (ListT Identity) (a, g)
--   g -> s -> ListT Identity ((a, g), s)
--   g -> s -> Identity [((a, g), s)]    (more or less :))
--   g -> s -> [((a, g), s)]

instance Analysis (TwoLevelAnalysis (Store Integer) Integer) Integer
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

class HasInitial g where
  initial :: g

instance (Ord s, Ord a, Ord g, HasInitial g, Lattice s) =>
         AddStepToFP (TwoLevelAnalysis s g) (PΣ a)
         (ℙ ((PΣ a, g), s)) where
  applyStep step fp =
    joinWith 
      (\((p,t),s) -> Set.fromList $ runIdentity $
                     collectListT (runStateT (runStateT (step p) t) s))
      fp
  inject p = Set.singleton $ ((p, initial), bot)

runAnalysis :: CExp -> Set ((PΣ Integer, Integer), Store Integer)
runAnalysis e = exploreFP e

idx  = Lam (["x"] :=> Call (Ref "x") [])
idy  = Lam (["y"] :=> Exit)
comb = Lam (["f", "g"] :=> Call (Ref "f") [Ref "g"])
ex   = Call comb [idx, idy]
