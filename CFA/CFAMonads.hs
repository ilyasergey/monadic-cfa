{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CFA.CFAMonads where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad as Monad
import Control.Monad.State
import Control.Monad.ListT as ListT
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Applicative
import Data.Monoid
import Data.Foldable as Foldable hiding (msum)
import Data.Traversable as Trav
import Data.List.Class as ListC

import Util

import CFA.Lattice

mapListItem :: Monad m => (forall v. n v -> m v) -> ListItem (ListT n) v -> ListItem (ListT m) v
mapListItem f Nil = Nil
mapListItem f (Cons v vs) = Cons v (mapListT f vs)

mapListT :: Monad m => (forall v. n v -> m v) -> ListT n v -> ListT m v
mapListT f m = ListT $ liftM (mapListItem f) $ f $ runListT m

----------------------------------------------------------------------
-- SharedStateListT : a reusable component to implement analyses...
----------------------------------------------------------------------
swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

-- state merging
mergeState :: Lattice s => [(a, s)] -> ([a], s)
mergeState = mapSnd withJoinMonoid . swap . sequenceA . List.map swap . List.map (mapSnd JoinMonoid)

duplicateState :: ([a], s) -> [(a,s)]
duplicateState (vs, s) = List.map (flip (,) s) vs

mergeAndDupState :: Lattice s => [(a, s)] -> [(a, s)]
mergeAndDupState = duplicateState . mergeState

-- newtype SharedStateT s n m a = SharedStateT { runSharedStateT :: s -> n (s, m a) }
-- newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }
-- Note: we are using "ListT done right" from the Control.Monad.ListT package.
newtype SharedStateListT s n a =
  SSListT { runSSListT :: StateT s (ListT n) a }
  deriving (Monad, MonadState s, MonadPlus)

instance MonadTrans (SharedStateListT s) where
  lift m = SSListT $ lift $ lift m

listToListT :: Monad n => n [a] -> ListT n a
listToListT = (>>= ListC.fromList) . lift

collectListT :: Monad n => ListT n a -> n [a]
collectListT = ListC.toList

collectSSListT :: Monad n => SharedStateListT s n a -> s -> n [(a,s)]
collectSSListT = (collectListT.) . runStateT . runSSListT

collectSSListTS :: (Lattice s, Monad n) => SharedStateListT s n a -> s -> n ([a],s)
collectSSListTS = (liftM mergeState.) . collectSSListT

collectSSListTST :: (Lattice s, Monad n) => SharedStateListT s n a -> StateT s n [a]
collectSSListTST = StateT . collectSSListTS

makeSSListT :: Monad n => (s -> n [(a,s)]) -> SharedStateListT s n a
makeSSListT f = SSListT $ StateT $ listToListT . f

makeSSListTS :: (Monad n) => (s -> n ([a],s)) -> SharedStateListT s n a
makeSSListTS f = SSListT $ StateT $ listToListT . liftM duplicateState . f

-- ask for losing precision 
mergeSharedState :: forall s n a . (Monad n, Lattice s) =>
                    SharedStateListT s n a -> SharedStateListT s n a 
mergeSharedState (SSListT (StateT f)) = SSListT $ StateT $ listToListT . liftM mergeAndDupState . ListC.toList . f

mapSharedState :: (Monad m, Monad n, Lattice s) => (forall v. n v -> m v) ->
                  SharedStateListT s n a -> SharedStateListT s m a 
mapSharedState f m = SSListT $ mapStateT (mapListT f) (runSSListT m)

-- SharedStateListT s n a = s -> n (s, [a])
--     abstracts
--   StateT s (ListT n) a
--    s -> n [(s, a)]
-- alternative:
--   ListT (StateT s n) a = s -> n ([a], s)
--   bad idea, because each non-deterministic branch gets the modified store from the
--   previous ND branch, instead of them all getting the same store and merging stores
--   afterwards. This causes lost precision, because non-first branches get bigger
--   stores. Also not a good idea because this is then order-dependent, and not actually
--   a Monad.

toNonShared :: Monad n => SharedStateListT s n a -> StateT s (ListT n) a
toNonShared = runSSListT

toShared :: (Monad n, Lattice s) => StateT s (ListT n) a -> SharedStateListT s n a
toShared = SSListT 

runSSListT0 :: (Monad n, Lattice s) => SharedStateListT s n a -> n ([a], s)
runSSListT0 m = liftM mergeState $ collectSSListT m bot

-- type MyAnalysis a = StateT g (SharedStateListT s Identity a)
--                   = g -> (SharedStateListT s Identity (g, a)
--                   = g -> (s -> (s, [(g, a)]))


askSSLT :: (Lattice s, MonadReader env m) => SharedStateListT s m env
askSSLT = do env <- lift ask
             return env

localSSLT :: (Lattice s, MonadReader env m) => (env -> env) -> SharedStateListT s m v -> SharedStateListT s m v
localSSLT f m = mapSharedState (local f) m

-- instance (Lattice s, MonadReader env m) =>
--          MonadReader env (SharedStateListT s m) where
--   ask = askSSLT
--   local = localSSLT

pureND :: MonadPlus m => [a] -> m a
pureND = msum . List.map return

pureNDSet :: MonadPlus m => Set a -> m a
pureNDSet = pureND . Set.toList

getsND :: (MonadPlus m, MonadState s m) => (s -> [a]) -> m a
getsND f = gets f >>= pureND

getsNDSet :: (MonadPlus m, MonadState s m) => 
             (s -> Set a) -> m a
getsNDSet f = getsND (Set.toList . f)

getsM :: (MonadState s m, Monad m) => (s -> m a) -> m a
getsM f = get >>= f

asksM :: (MonadReader s (t m), Monad m, MonadTrans t) => (s -> m a) -> t m a
asksM f = asks f >>= lift

commaM :: Monad m => m a -> m b -> m (a,b)
commaM = liftM2 (,)

liftTup :: Monad t => (t a, b) -> t (a,b)
liftTup (ma,b) = liftM (flip (,) b) ma

joinWith :: (Foldable t, Lattice a) => (b -> a) -> t b -> a
joinWith f = Foldable.foldr ((⊔) . f) bot
