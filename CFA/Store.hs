{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CFA.Store where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Lattice

-- Store uniquely defines the type of its addresses
class (Eq a, Lattice s, Lattice d) => StoreLike a s d | s->a, s->d where
  σ0 :: s
  bind :: s -> a -> d -> s
  replace :: s -> a -> d -> s
  fetch :: s -> a -> d
  filterStore :: s -> (a -> Bool) -> s 

----------------------------------------------------------------------
 -- Abstract Garbage Collection
----------------------------------------------------------------------

-- Abstract garbage collector
class Monad m => GarbageCollector m a where
  gc :: a -> m a
  -- default implementation
  gc = return

----------------------------------------------------------------------
 -- Abstract Counting
----------------------------------------------------------------------

-- Abstract natural number
data AbsNat = AZero | AOne | AMany
     deriving (Ord, Eq, Show)

instance Lattice AbsNat where
 bot = AZero
 top = AMany
 n ⊑ m = (n == bot) || (m == top) || (n == m)
 n ⊔ m = if (n ⊑ m) then m else n
 n ⊓ m = if (n ⊑ m) then n else m

-- Abstract addition
(⊕) :: AbsNat -> AbsNat -> AbsNat
AZero ⊕ n = n
n ⊕ AZero = n
n ⊕ m = AMany

class ACounter a s where
  count :: s -> a -> AbsNat

-- Counting store
type StoreWithCount a d = a :-> (d, AbsNat)

instance (Ord a, Lattice d) => ACounter a (StoreWithCount a d) where
 -- fetching with default bottom
 count σ a = snd $ σ CFA.Lattice.!! a         

-- counter is nullified when filtered
-- and incremented when `bind' is called
instance (Ord a, Lattice d) => StoreLike a (StoreWithCount a d) d where
 σ0 = Map.empty  
 bind σ a d = σ `update_add` [a ==> (d, AOne)]
 fetch σ a = fst $ σ CFA.Lattice.!! a  
 replace σ a d = σ ⨆ [a ==> (d, AZero)]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ

update_add :: (Ord k, Lattice v) => (k :-> (v, AbsNat)) -> [(k, (v, AbsNat))] -> (k :-> (v, AbsNat))
update_add f [] = f
update_add f ((k,v):tl) = Map.insertWith (\(x1, y1) -> \(x2, y2) -> (x1 ⊔ x2, y1 ⊕ y2)) k v (update_add f tl)

