{-# LANGUAGE TypeOperators #-}

module CFA.CPS where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Lattice

-- Syntax.
type Var = String

data Lambda = [Var] :=> CExp
  deriving (Ord, Eq, Show)

data AExp = Ref Var
          | Lam Lambda
  deriving (Ord, Eq, Show)

data CExp = Call AExp [AExp]
          | Exit
  deriving (Ord, Eq, Show)

-- State-space
type PΣ a = (CExp, Env a)
type Env a = Var :-> a
type D a = ℙ (Val a)
data Val a = Clo (Lambda, Env a)
  deriving (Eq, Ord, Show)

ρ0 = Map.empty 

 -- Generic store.
type Store a = a :-> (D a)
