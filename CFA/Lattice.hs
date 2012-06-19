{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CFA.Lattice where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Monoid

 -- Abbreviations.
type k :-> v = Map.Map k v
type ℙ a = Set.Set a

(==>) :: a -> b -> (a,b)
(==>) x y = (x,y)

(//) :: Ord k => (k :-> v) -> [(k,v)] -> (k :-> v)
(//) f [] = f
(//) f ((x,y):tl) = Map.insert x y (f // tl)

(⊎) :: (Ord k, Lattice v) => (k :-> v) -> [(k,v)] -> (k :-> v)
f ⊎ [] = f
f ⊎ ((k,v):tl) = Map.insertWith (⊔) k v (f ⊎ tl)


 -- Partial order theory.
class Lattice a where
 bot :: a
 top :: a
 (⊑) :: a -> a -> Bool
 (⊔) :: a -> a -> a
 (⊓) :: a -> a -> a

-- unit is a trivial lattice
instance Lattice () where
 bot = ()
 top = ()
 x ⊔ y = top
 x ⊓ y = bot
 x ⊑ y = True

instance (Lattice a, Lattice b) => Lattice (a, b) where
 bot = (bot, bot)
 top = (top, top)
 (a1, b1) ⊔ (a2, b2) = (a1 ⊔ a2, b1 ⊔ b2)
 (a1, b1) ⊓ (a2, b2) = (a1 ⊓ a2, b1 ⊓ b2)
 (a1, b1) ⊑ (a2, b2) = (a1 ⊑ a2) && (b1 ⊑ b2)

instance (Ord s, Eq s) => Lattice (ℙ s) where
 bot = Set.empty
 top = error "no representation of universal set"
 x ⊔ y = x `Set.union` y
 x ⊓ y = x `Set.intersection` y
 x ⊑ y = x `Set.isSubsetOf` y

instance (Ord k, Lattice v) => Lattice (k :-> v) where
 bot = Map.empty
 top = error "no representation of top map"
 f ⊑ g = Map.isSubmapOfBy (⊑) f g
 f ⊔ g = Map.unionWith (⊔) f g
 f ⊓ g = Map.intersectionWith (⊓) f g

(⨆) :: (Ord k, Lattice v) => (k :-> v) -> [(k,v)] -> (k :-> v)
f ⨆ [] = f
f ⨆ ((k,v):tl) = Map.insertWith (⊔) k v (f ⨆ tl)

(!!) :: (Ord k, Lattice v) => (k :-> v) -> k -> v
f !! k = Map.findWithDefault bot k f

-- a lattice is a monoid in two ways...
newtype JoinMonoid a = JoinMonoid { withJoinMonoid :: a } deriving (Show, Eq, Lattice)

instance Lattice a => Monoid (JoinMonoid a) where
  mempty = bot
  mappend = (⊔)

newtype MeetMonoid a = MeetMonoid { withMeetMonoid :: a } deriving (Show, Eq, Lattice)

instance Lattice a => Monoid (MeetMonoid a) where
  mempty = top
  mappend = (⊓)

ljoin :: Lattice a => [a] -> a
ljoin l = withJoinMonoid $ mconcat $ List.map JoinMonoid l
