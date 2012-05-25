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
import Control.Monad.State
import Control.Applicative

import Util

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis

data CAddr = CBind Var Int
  deriving (Eq, Ord, Show)

type ΣC = (Store CAddr, Int)

alterStore = mapFst
increaseTime = mapSnd (+1)

type Concrete = State ΣC

readA :: CAddr -> Concrete (D CAddr)
readA a = gets $ (! a) . fst 

getTime :: Concrete Int
getTime = gets snd

instance Analysis Concrete CAddr where
  fun ρ (Lam l) = return $ Clo (l, ρ)
  fun ρ (Ref v) = do [proc] <- liftM Set.toList $ readA (ρ!v)
                     return proc
  arg ρ (Lam l) = let proc = Clo(l, ρ) in return $ Set.singleton proc
  arg ρ (Ref v) = readA (ρ!v)

  a $= d = modify $ alterStore $ \ σ -> σ ⨆ [a ==> d]

  alloc v = CBind v <$> getTime

  tick _ = modify increaseTime

stepConcrete :: ΣC -> PΣ CAddr -> (PΣ CAddr, ΣC)
stepConcrete config state = runState (mnext state) config

initialΣC :: ΣC
initialΣC = (bot, 0)

injectConcrete :: CExp -> (PΣ CAddr, ΣC)
injectConcrete call = ((call, ρ0), initialΣC)


-- Add Garbage Collection
instance GarbageCollector Concrete (PΣ CAddr)

