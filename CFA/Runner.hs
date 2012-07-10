{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module CFA.Runner where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Traversable
import Data.Foldable as Foldable
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.State
import Control.Applicative

import CFA.Lattice
import CFA.CFAMonads

class HasInitial a where
  initial :: a

findFP :: forall a m. (Lattice a) => (a -> a) -> a
findFP f = loop bot
  where loop :: a -> a
        loop c = let c' = f c in if c' ⊑ c then c else loop c' 

class AddStepToFP m a fp | m -> a, fp -> m where
  applyStep :: (a -> m a) -> fp -> fp
  inject :: a -> fp

exploreFP :: forall m a fp.
             (Lattice fp, AddStepToFP m a fp) =>
             (a -> m a) -> a -> fp
exploreFP step s = findFP loop
  where loop :: fp -> fp
        loop acc = inject s ⊔ applyStep step acc
