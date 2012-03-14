{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module CFA.CESK where

-- Imports.
import Data.Map as Map
import Data.Set as Set

import CFA.Lattice
import CFA.Store

{---------------- SYNTAX AND STATE-SPACE ----------------}

-- `a' stands for the nature of addresses
-- it is also a leaf of the state-space

type Var = String
type Lab = String
type Env a = Var :-> a
type Lambda = (Var, Exp)
type State a = (Exp, Env a, a)

data Exp = Ref (Var, Lab)
         | App (Exp, Exp, Lab)
         | Lam (Lambda, Lab)
  deriving (Eq, Ord, Show)

data Clo a = Clo (Lambda, Env a, Lab)
  deriving (Eq, Ord)

data Kont a = Mt
            | Ar (Exp, Env a, a)
            | Fn (Lambda, Env a, a)
  deriving (Eq, Ord)

class (Eq a, Ord a) => Address a

-- retrieve a label
lab :: Exp -> Lab
lab (Ref (_, l)) = l
lab (App (_, _, l)) = l
lab (Lam (_, l)) = l
