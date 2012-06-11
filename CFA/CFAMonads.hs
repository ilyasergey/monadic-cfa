{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
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
import Control.Monad.ListT
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Applicative
import Data.Monoid
import Data.Foldable hiding (msum)
import Data.Traversable as Trav

import Util

import CFA.Lattice

-- axiom:
--   action on singletons:
--     parallel [m] === liftM (:[]) m
--
--   "thread independence"?
--   distributivity: parallel lsa >> parallel lsb === parallel (zipWith (>>) lsa lsb)
--   more general?: parallel lsa >>= (parallel . map f) === parallel (map (>>= f) lsa)
--           in do-notation: do { xs <- parallel lsa ; parallel (map f xs) } 
--                         = parallel $ map (\ la -> do { x <- la ; f x }) lsa
--
--   purity: parallel (map return ls) === return ls

-- purity consequence:
--   parallel . List.map (liftM f) == liftM (List.map f) . parallel 
class Monad m => MonadParallel m where
  parallel :: [m a] -> m [a]

instance MonadParallel [] where
  parallel = Monad.sequence

instance (MonadParallel n, Lattice s) =>
         MonadParallel (SharedStateListT s n) where
  parallel ls = SSListT $ \s ->
    let ls' = parallel [ runSSListT x s | x <- ls ]
    in liftM (mapFst withJoinMonoid .
               sequenceA . List.map (mapFst JoinMonoid)) ls'

instance MonadParallel Identity where
  parallel = Monad.sequence

-- alternative to mapM
pmapM :: MonadParallel m => (a -> m b) -> [a] -> m [b]
pmapM f = parallel . List.map f

----------------------------------------------------------------------
 -- Generic analysis with no shared component
----------------------------------------------------------------------

-- from HaskellWiki: "ListT done right"                  
-- data MList' m a = MNil | a `MCons` MList m a
-- type MList m a  = m (MList' m a)
-- -- This can be directly used as a monad transformer
--newtype ListT m a = ListT { runListT :: MList m a }
  
-- newtype SharedStateT s n m a = SharedStateT { runSharedStateT :: s -> n (s, m a) }
-- newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }
newtype SharedStateListT s n a = SSListT { runSSListT :: s -> n (s, [a]) }

-- SharedStateListT s n a = s -> n (s, [a])
--     abstracts?
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
-- toNonShared :: Monad n => SharedStateListT s n a -> StateT s (ListT n) a
-- toNonShared m = StateT $ \ s -> ListT $ do
--   (s', lv) <- runSSListT m s
--   return $ List.map (flip (,) s') lv

-- toShared :: (Monad n, Lattice s) => StateT s (ListT n) a -> SharedStateListT s n a
-- toShared m = SSListT $ \ s -> do
--   lsv <- runListT (runStateT m s)
--   return (List.foldr (⊔) bot $ List.map snd lsv, List.map fst lsv)


runSSListT0 :: Lattice s => SharedStateListT s n a -> n (s, [a])
runSSListT0 m = runSSListT m bot

-- type MyAnalysis a = StateT g (SharedStateListT s Identity a)
--                   = g -> (SharedStateListT s Identity (g, a)
--                   = g -> (s -> (s, [(g, a)]))

-- note: the Lattice constraint would more naturally be a Monoid constraint, but
-- it's easier to work with lattices everywhere.. Note: we use the join monoid over 
-- the lattice.
instance (MonadParallel n, Lattice s) => Monad (SharedStateListT s n) where
  return v = SSListT $ \s -> return (s, return v)
  m >>= (f :: a -> SharedStateListT s n b) = SSListT $ \s ->
    do  -- (s', m') :: (s, [a])
        (s', m') <- runSSListT m s
          
        -- ress :: [(JoinMonoid s, [b])]
        ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
        return $ mapFst ({-(s' ⊔) .-} withJoinMonoid) $ (mapSnd Monad.join $ sequenceA ress)

-- monad laws:
-- 1: left identity: return a >>= f  ===   f a
--        return a >>= f 
--              (def of >>=)
--      = SSListT $ \s -> do (s', m') <- runSSListT (return a) s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--              (def of return)
--      = SSListT $ \s -> do (s', m') <- return (s, [a])
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--              (Monad axiom "left identity" in n) 
--      = SSListT $ \s -> do ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s) [a]
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--              (List.map on singletons)
--      = SSListT $ \s -> do ress <- parallel [liftM (mapFst JoinMonoid) $ runSSListT (f a) s]
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--              (MonadParallel axiom "action on singletons")
--      = SSListT $ \s -> do ress <- liftM (:[]) $ liftM (mapFst JoinMonoid) $ runSSListT (f a) s
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--              (def of liftM)
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd Monad.join . sequenceA) $ liftM (:[]) $ liftM (mapFst JoinMonoid) $ runSSListT (f a) s
--              (obvious?)
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd Monad.join . (\x -> sequenceA [x]) . mapFst JoinMonoid) $ runSSListT (f a) s
--              (def of sequenceA for lists)
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd Monad.join . (\x -> (:) <$> x <*> pure []) . mapFst JoinMonoid) $ runSSListT (f a) s
--              (applicative functor interchange, homomorphism etc.) 
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd Monad.join . (\x -> (:[]) <$> x) . mapFst JoinMonoid) $ runSSListT (f a) s
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd Monad.join . ((:[]) <$>) . mapFst JoinMonoid) $ runSSListT (f a) s
--              (def of fmap for (,) s)
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd Monad.join . mapSnd (:[]) . mapFst JoinMonoid) $ runSSListT (f a) s
--              (property of mapSnd)
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd (Monad.join . (:[])) . mapFst JoinMonoid) $ runSSListT (f a) s
--              (def of monad join for lists)
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapSnd id . mapFst JoinMonoid) $ runSSListT (f a) s
--              (property of mapSnd)
--      = SSListT $ \s -> liftM (mapFst withJoinMonoid . mapFst JoinMonoid) $ runSSListT (f a) s
--              (property of mapFst)
--      = SSListT $ \s -> liftM (mapFst (withJoinMonoid . JoinMonoid)) $ runSSListT (f a) s
--              (def of withJoinMonoid)
--      = SSListT $ \s -> liftM (mapFst id) $ runSSListT (f a) s
--              (property of mapFst)
--      = SSListT $ \s -> liftM id $ runSSListT (f a) s
--              (Functor law)
--      = SSListT $ \s -> runSSListT (f a) s
--              (eta-eq)
--      = SSListT $ runSSListT (f a) 
--              (newtype property)
--      = f a
--
--
-- 2: right identity: m >>= return  ===   m
--        m >>= return
--             (def of >>=)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (return a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (def of return in SSListT)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ return (s', [a])) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (Applicative functor laws: def of fmap, homomorphism)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> return $ mapFst JoinMonoid $ (s', [a])) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (def of mapFst)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> return (JoinMonoid s', [a])) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (property of List.map)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map return $ List.map (\a -> (JoinMonoid s', [a])) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (purity of MonadParallel)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- return $ List.map (\a -> (JoinMonoid s', [a])) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (right identity of Monad n)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA $ List.map (\a -> (JoinMonoid s', [a])) m'
--             (TODO: why?)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ (JoinMonoid s', List.map (:[]) m')
--             (def of mapSnd)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           return $ mapFst withJoinMonoid $ (JoinMonoid s', mapSnd Monad.join $ List.map (:[]) m')
--             (def of mapFst)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           return $ (withJoinMonoid $ JoinMonoid s', Monad.join $ List.map (:[]) m')
--             (def of withJoinMonoid)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           return $ (s', Monad.join $ List.map (:[]) m')
--             (Monad.join for lists on singletons)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           return (s', m')
--             (right identity)
--      = SSListT $ \s -> runSSListT m s
--             (eta-eq)
--      = SSListT $ runSSListT m
--             (newtype con+decon)
--      = m
--
-- 3: associativity: (m >>= f) >>= g  ===  m >>= (\x -> f x >>= g)
--        (m >>= f) >>= g
--             (def of >>=)
--      = SSListT $ \s -> do (s', m') <- runSSListT (m >>= f) s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (def of >>=)
--      = SSListT $ \s -> do (s', m') <- runSSListT (SSListT $ \s -> do 
--                               (s', m') <- runSSListT m s
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
--                               return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                             ) s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (newtype con-decon)
--      = SSListT $ \s -> do (s', m') <- (\s -> do 
--                               (s', m') <- runSSListT m s
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
--                               return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                             ) s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (beta-eq)
--      = SSListT $ \s -> do (s', m') <- do 
--                               (s', m') <- runSSListT m s
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
--                               return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (|Monad| n associativity)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a) s') m'
--                           (s', m') <- return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--             (purity consequence, List.map properties, liftM property)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> runSSListT (f a) s') m'
--                           (s', m') <- return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA $ List.map (mapFst JoinMonoid) ress
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress


--  ???

--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> runSSListT (f a) s') m'
--                           ress <- parallel $ List.map (liftM (mapSnd Monad.join . sequenceA . List.map (mapFst JoinMonoid)) . 
--                                     parallel . (\(s', m') -> List.map (\a -> runSSListT (g a) s') m')) ress
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (property of liftM)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> runSSListT (f a) s') m'
--                           ress <- parallel $ List.map (liftM (mapSnd Monad.join . sequenceA . List.map (mapFst JoinMonoid))) $ 
--                                     List.map (\(s', m') -> parallel $ List.map (\a -> runSSListT (g a) s') m') ress
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (property of liftM)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> runSSListT (f a) s') m'
--                           ress <- parallel $ List.map (liftM (mapSnd Monad.join . sequenceA) . liftM (List.map (mapFst JoinMonoid))) $ 
--                                     List.map (\(s', m') -> parallel $ List.map (\a -> runSSListT (g a) s') m') ress
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (property of List.map)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> runSSListT (f a) s') m'
--                           ress <- parallel $ List.map (\(s', m') ->
--                               liftM (mapSnd Monad.join . sequenceA) $ liftM (List.map (mapFst JoinMonoid)) $ parallel $ List.map (\a -> runSSListT (g a) s') m'
--                             ) ress
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (MonadParallel purity consequence)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> runSSListT (f a) s') m'
--                           ress <- parallel $ List.map (\(s', m') ->
--                               liftM (mapSnd Monad.join . sequenceA) $ parallel $ List.map (liftM (mapFst JoinMonoid)) $ List.map (\a -> runSSListT (g a) s') m'
--                             ) ress
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (property of List.map)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> runSSListT (f a) s') m'
--                           ress <- parallel $ List.map (\(s', m') ->
--                               liftM (mapSnd Monad.join . sequenceA) $ parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                             ) ress
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (distributivity)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (>>= (\(s', m') ->
--                               liftM (mapSnd Monad.join . sequenceA) $ parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                             )) $ List.map (\a -> runSSListT (f a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (do notation)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\ma -> do 
--                               (s', m') <- ma
--                               liftM (mapSnd Monad.join . sequenceA) $ parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                             ) $ List.map (\a -> runSSListT (f a) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (property of List.map)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> do 
--                               (s', m') <- runSSListT (f a) s'
--                               liftM (mapSnd Monad.join . sequenceA) $ parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                             ) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (def of liftM)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> do 
--                               (s', m') <- runSSListT (f a) s'
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                               return $ mapSnd Monad.join $ sequenceA ress
--                             ) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (property of mapFst, newtype con-decon, mapFst-id)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> do 
--                               (s', m') <- runSSListT (f a) s'
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                               return $ mapFst JoinMonoid $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                             ) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (right identity of Monad n)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> do 
--                               (s', m') <- runSSListT (f a) s'
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                               r <- mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                               return $ mapFst JoinMonoid r
--                             ) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--              (def of liftM, Monad n associativity)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ do 
--                               (s', m') <- runSSListT (f a) s'
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                               return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                             ) m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--              (beta-eq)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ (\s -> do 
--                               (s', m') <- runSSListT (f a) s
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                               return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                             ) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (newtype con-decon)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (SSListT $ \s -> do 
--                               (s', m') <- runSSListT (f a) s
--                               ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (g a) s') m'
--                               return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--                             ) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (def of >>=)
--      = SSListT $ \s -> do (s', m') <- runSSListT m s
--                           ress <- parallel $ List.map (\a -> liftM (mapFst JoinMonoid) $ runSSListT (f a >>= g) s') m'
--                           return $ mapFst withJoinMonoid $ mapSnd Monad.join $ sequenceA ress
--            (def of >>=)
--      = m >>= (\x -> f x >>= g)



instance (Lattice s, MonadParallel n) => MonadState s (SharedStateListT s n) where
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

instance (Lattice s, MonadParallel n) => MonadPlus (SharedStateListT s n) where
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

getsM :: (MonadState s m, Monad m) => (s -> m a) -> m a
getsM f = get >>= f

asksM :: (MonadReader s (t m), Monad m, MonadTrans t) => (s -> m a) -> t m a
asksM f = asks f >>= lift

-- ----------------------------------------------------------------------
--  -- Single store-threading analysis.
-- ----------------------------------------------------------------------
 
-- data SingleStoreAnalysis s g b = SSFA { runWithStore :: s -> g -> (s, [(b, g)]) }

-- -- TODO redefine store-like logic
-- instance Lattice s => Monad (SingleStoreAnalysis s g) where
--   (>>=) (SSFA f) g = SSFA (\st -> \guts -> 
--      let (st', pairs) = f st guts -- make an f-step
--          -- get new results via g :: [(st, [(b, g)])]
--          newResults = List.map (\(a, guts') -> runWithStore (g a) st' guts') pairs
--          -- merge stores and concatenate the results :: (st, [(b, g)])
--          -- requires a lattice structure of a store
--       in foldl (\(s, bg) -> \(s', bg') -> (s ⊔ s', bg ++ bg'))
--                (st', []) newResults)

--   return a = SSFA (\s -> \guts -> (s, [(a, guts)]))

-- instance Lattice s => Functor (SingleStoreAnalysis s g) where
--   fmap = liftM

-- getShared :: SingleStoreAnalysis s g s
-- getShared = SSFA $ \s g -> (s, [(s,g)])

-- getsShared :: Lattice s => (s -> v) -> SingleStoreAnalysis s g v
-- getsShared f = liftM f getShared

-- getGuts :: SingleStoreAnalysis s g g
-- getGuts = SSFA $ \s g -> (s, [(g,g)])

-- getsGuts :: Lattice s => (g -> v) -> SingleStoreAnalysis s g v
-- getsGuts f = f <$> getGuts

-- modifyShared :: (s -> s) -> SingleStoreAnalysis s g ()
-- modifyShared f = SSFA $ \s g -> (f s, [((), g)])

-- modifyGuts :: (g -> g) -> SingleStoreAnalysis s g ()
-- modifyGuts f = SSFA $ \s g -> (s, [((), f g)])

