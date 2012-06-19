{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- TODO: get rid of this
-- {-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.Concrete where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Foldable as Foldable
import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative

import Util

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis
import CFA.CPS.Analysis.Runner

data CAddr = CBind Var Int
  deriving (Eq, Ord, Show)

type DStore a = a :-> (Val a)

type ΣC = (DStore CAddr, Int)


alterStore = mapFst
increaseTime = mapSnd (+1)

-- is a monad
type Concrete = State ΣC 

readA :: CAddr -> Concrete (Val CAddr)
readA a = gets $ (! a) . fst 

getTime :: Concrete Int
getTime = gets snd

instance Analysis Concrete CAddr where
  fun ρ (Lam l) = return $ Clo (l, ρ)
  fun ρ (Ref v) = readA (ρ!v)

  arg ρ (Lam l) = let proc = Clo(l, ρ) in return proc
  arg ρ (Ref v) = readA (ρ!v)

  a $= d = modify $ alterStore $ Map.insert a d 

  alloc v = CBind v <$> getTime

  tick _ _ go = modify increaseTime >> go

initialΣC :: ΣC
initialΣC = (Map.empty, 0)

injectConcrete :: CExp -> (PΣ CAddr, ΣC)
injectConcrete call = ((call, ρ0), initialΣC)


-- Add Garbage Collection
instance GarbageCollector Concrete (PΣ CAddr)

instance AddStepToFP Concrete (PΣ CAddr) (ℙ (PΣ CAddr, ΣC)) where
  applyStep step states = Set.map (uncurry $ runState . step) states
  inject s = Set.singleton (s, initialΣC)
  

exploreConcrete :: CExp -> ℙ (PΣ CAddr, ΣC)
exploreConcrete = exploreFP

