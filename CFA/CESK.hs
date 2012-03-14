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
  deriving (Eq, Ord, Show)

data Kont a = Mt
            | Ar (Exp, Env a, a)
            | Fn (Lambda, Env a, a)
  deriving (Eq, Ord, Show)

data Storable a  = Val (Clo a)
                 | Cont (Kont a)
  deriving (Eq, Ord, Show)



-- retrieve a label
lab :: Exp -> Lab
lab (Ref (_, l)) = l
lab (App (_, _, l)) = l
lab (Lam (_, l)) = l

----------------------------------------------------------------------  
-- TIME-STAMPED ADDRESSES (FIXED)
----------------------------------------------------------------------  
data Time = TLab Lab [Lab]
          | TMt [Lab]
  deriving (Eq, Ord, Show)

class (Eq a, Ord a) => Address a

data Addr = Bind Var [Lab]
          | Call Lab [Lab]
  deriving (Eq, Ord, Show)

instance Address Addr

contour :: Time -> [Lab]
contour (TLab _ c) = c
contour (TMt c) = c

