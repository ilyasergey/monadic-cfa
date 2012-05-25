{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CFA.CFAMonads where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad as Monad
import Control.Monad.State
import Control.Applicative
import Data.Monoid
import Data.Traversable

import Util

import CFA.Lattice

----------------------------------------------------------------------  
 -- Concrete Semantics
----------------------------------------------------------------------

-- domi: moved to concrete.hs
-- newtype Concrete g b = Concrete { cf :: State g b } deriving (Monad)

----------------------------------------------------------------------
 -- Generic analysis with no shared component
----------------------------------------------------------------------
  
-- GenericAnalysis :: * -> * -> *
-- parametrized by guts and passed result
-- data GenericAnalysis s g b = GCFA {
--   gf :: g -> [(b, g)]
-- }

-- -- Curry GenericAnalysis for the fixed guts
-- instance Monad (GenericAnalysis s g) where
--   (>>=) (GCFA f) g = GCFA (\ guts ->
--     concatMap (\ (a, guts') -> (gf $ g(a)) guts') (f guts))

--   return a = GCFA (\ guts -> [(a,guts)])

newtype SharedStateT s m a = SharedStateT { runSharedStateT :: s -> (s, m a) }

-- note: the Lattice constraint would more naturally be a Monoid constraint, but
-- it's easier to work with lattices everywhere.. Note: we use the join monoid over 
-- the lattice.
instance (Monad m, Traversable m, Lattice s) => Monad (SharedStateT s m) where
  return v = SharedStateT $ \s -> (s, return v)
  m >>= (f :: a -> SharedStateT s m b) = SharedStateT $ \s ->
    let -- (s', m') :: (s, m a)
        (s', m') = runSharedStateT m s
        ress :: m (JoinMonoid s, m b)
        ress = liftM (\a -> mapFst JoinMonoid $ runSharedStateT (f a) s') m'
    in mapFst ((s' ⊔) . withJoinMonoid) $ mapSnd Monad.join $ sequenceA ress

instance (Lattice s, Traversable m, Monad m) => MonadState s (SharedStateT s m) where
  get = SharedStateT $ \s -> (s, return s)
  put s = SharedStateT $ \_ -> (s, return ())


liftSharedState :: m a -> SharedStateT s m a
liftSharedState m = SharedStateT $ \s -> (s, m)
----------------------------------------------------------------------
 -- Single store-threading analysis.
----------------------------------------------------------------------
 
data SingleStoreAnalysis s g b = SSFA { runWithStore :: s -> g -> (s, [(b, g)]) }

-- TODO redefine store-like logic
instance Lattice s => Monad (SingleStoreAnalysis s g) where
  (>>=) (SSFA f) g = SSFA (\st -> \guts -> 
     let (st', pairs) = f st guts -- make an f-step
         -- get new results via g :: [(st, [(b, g)])]
         newResults = List.map (\(a, guts') -> runWithStore (g a) st' guts') pairs
         -- merge stores and concatenate the results :: (st, [(b, g)])
         -- requires a lattice structure of a store
      in foldl (\(s, bg) -> \(s', bg') -> (s ⊔ s', bg ++ bg'))
               (st', []) newResults)

  return a = SSFA (\s -> \guts -> (s, [(a, guts)]))

instance Lattice s => Functor (SingleStoreAnalysis s g) where
  fmap = liftM

getShared :: SingleStoreAnalysis s g s
getShared = SSFA $ \s g -> (s, [(s,g)])

getsShared :: Lattice s => (s -> v) -> SingleStoreAnalysis s g v
getsShared f = liftM f getShared

getGuts :: SingleStoreAnalysis s g g
getGuts = SSFA $ \s g -> (s, [(g,g)])

getsGuts :: Lattice s => (g -> v) -> SingleStoreAnalysis s g v
getsGuts f = f <$> getGuts

modifyShared :: (s -> s) -> SingleStoreAnalysis s g ()
modifyShared f = SSFA $ \s g -> (f s, [((), g)])

modifyGuts :: (g -> g) -> SingleStoreAnalysis s g ()
modifyGuts f = SSFA $ \s g -> (s, [((), f g)])

