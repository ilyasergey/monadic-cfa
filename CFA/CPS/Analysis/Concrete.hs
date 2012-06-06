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
type FPSConcrete = StateT (Set (PΣ CAddr, ΣC)) Concrete

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

stepConcrete :: ΣC -> PΣ CAddr -> (Maybe (PΣ CAddr), ΣC)
stepConcrete config state = runState (mnext state) config

initialΣC :: ΣC
initialΣC = (Map.empty, 0)

injectConcrete :: CExp -> (PΣ CAddr, ΣC)
injectConcrete call = ((call, ρ0), initialΣC)


-- Add Garbage Collection
instance GarbageCollector Concrete (PΣ CAddr)

instance GarbageCollector (StateT s Concrete) (PΣ CAddr) where
  gc a = lift $ gc a


instance FPCalc FPSConcrete (PΣ CAddr) where
  hasSeen p = do store <- lift get
                 gets (Set.member (p, store))
  markSeen p = do store <- lift get
                  modify (Set.insert (p, store))


instance Analysis (StateT s Concrete) CAddr where
  fun ρ f = lift $ fun ρ f
  arg ρ f = lift $ arg ρ f
  a $= d = lift $ a $= d
  alloc v = lift $ alloc v
  tick proc ps go = StateT $ \s -> tick proc ps $ runStateT go s



exploreConcrete :: CExp -> Set (PΣ CAddr, ΣC)
exploreConcrete p = evalState (execStateT (explore p) (Set.empty :: Set (PΣ CAddr, ΣC))) initialΣC

