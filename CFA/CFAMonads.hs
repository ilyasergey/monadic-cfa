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
import Control.Monad.List
import Control.Monad.Reader
import Control.Applicative
import Data.Monoid
import Data.Traversable as Trav

import Util

import CFA.Lattice

----------------------------------------------------------------------
 -- Generic analysis with no shared component
----------------------------------------------------------------------
  
-- newtype SharedStateT s n m a = SharedStateT { runSharedStateT :: s -> n (s, m a) }
-- newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }
newtype SharedStateListT s n a = SSListT { runSSListT :: s -> n (s, [a]) }
-- SharedStateListT s n a
--  s -> n (s, [a])


-- newtype ReaderT s n a = ReaderT { runEnvT :: s -> n a }

-- SharedStateListT s (ReaderT s' n) a = ReaderT s' (SharedStateListT s n) a
-- s -> ReaderT s' n (s, [a])          = s' -> SharedStateListT s n a
-- s -> s' -> n (s, [a])            = s' -> s -> n (s, [a])


-- SharedStateListT s n a = s -> n (s, [a])
--     abstracts
--   StateT s (ListT n) a
--    s -> n [(s, a)]
--   StateT s (ListT n) a = s -> n [(a, s)]
-- alternative:
--   ListT (StateT s n) a = s -> n ([a], s)
--   bad idea, because each non-deterministic branch gets the modified store from the
--   previous ND branch, instead of them all getting the same store and merging stores
--   afterwards. This causes lost precision, because non-first branches get bigger
--   stores. Also not a good idea because this is then order-dependent, and not actually
--   a Monad.
toNonShared :: Monad n => SharedStateListT s n a -> StateT s (ListT n) a
toNonShared m = StateT $ \ s -> ListT $ do
  (s', lv) <- runSSListT m s
  return $ List.map (flip (,) s') lv

toShared :: (Monad n, Lattice s) => StateT s (ListT n) a -> SharedStateListT s n a
toShared m = SSListT $ \ s -> do
  lsv <- runListT (runStateT m s)
  return (foldr (⊔) bot $ List.map snd lsv, List.map fst lsv)


runSSListT0 :: Lattice s => SharedStateListT s n a -> n (s, [a])
runSSListT0 m = runSSListT m bot

-- type MyAnalysis a = StateT g (SharedStateListT s Identity a)
--                   = g -> (SharedStateListT s Identity (g, a)
--                   = g -> (s -> (s, [(g, a)]))

-- note: the Lattice constraint would more naturally be a Monoid constraint, but
-- it's easier to work with lattices everywhere.. Note: we use the join monoid over 
-- the lattice.
instance (Monad n, Lattice s) => Monad (SharedStateListT s n) where
  return v = SSListT $ \s -> return (s, return v)
  m >>= (f :: a -> SharedStateListT s n b) = SSListT $ \s ->
    do  -- (s', m') :: (s, [a])
        (s', m') <- runSSListT m s
          
        -- ress :: [(JoinMonoid s, [b])]
        ress <- Trav.sequence $ liftM (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
        return $ mapFst ((s' ⊔) . withJoinMonoid) $ (mapSnd Monad.join $ sequenceA ress)

instance (Lattice s, Monad n) => MonadState s (SharedStateListT s n) where
  get = SSListT $ \s -> return (s, return s)
  put s = SSListT $ \_ -> return (s, return ())

-- instance (Lattice s, MonadReader env m) =>
--          MonadReader env (SharedStateListT s m) where
--   ask = SSListT $ \s -> do env <- ask
--                            return (s, [env])
--   local f m = SSListT $ \s -> local f (runSSListT m s)

askSSLT :: (Lattice s, MonadReader env m) => SharedStateListT s m env
askSSLT = SSListT $ \s -> do env <- ask
                             return (s, [env])
localSSLT :: (Lattice s, MonadReader env m) => (env -> env) -> SharedStateListT s m v -> SharedStateListT s m v
localSSLT f m = SSListT $ \s -> local f (runSSListT m s)

instance (Lattice s, Monad n) => MonadPlus (SharedStateListT s n) where
  mzero = SSListT $ \s -> return (s, [])
  mplus a b = SSListT $ \s -> do (sa, resa) <- runSSListT a s
                                 (sb, resb) <- runSSListT b s
                                 return (sa ⊔ sb, resa ++ resb)

pureND :: MonadPlus m => [a] -> m a
pureND = msum . List.map return

pureNDSet :: MonadPlus m => Set a -> m a
pureNDSet = pureND . Set.toList

instance MonadTrans (SharedStateListT s) where
  lift n = SSListT $ \s -> liftM ((,) s . return) n

getsND :: (MonadPlus m, MonadState s m) => (s -> [a]) -> m a
getsND f = gets f >>= pureND

getsNDSet :: (MonadPlus m, MonadState s m) => (s -> Set a) -> m a
getsNDSet f = getsND (Set.toList . f)

getsM :: (MonadState s (t m), Monad m, MonadTrans t) => (s -> m a) -> t m a
getsM f = gets f >>= lift

asksM :: (MonadReader s (t m), Monad m, MonadTrans t) => (s -> m a) -> t m a
asksM f = asks f >>= lift

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

