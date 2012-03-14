{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CFA.CFAMonads where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Lattice

----------------------------------------------------------------------  
 -- Concrete Semantics
----------------------------------------------------------------------

data Concrete s g b = Concrete { cf :: g -> (b, g) }

instance Monad (Concrete s g) where
  (>>=) (Concrete f) g = Concrete (\guts ->
    let (b, guts') = f guts
     in (cf $ g(b)) guts')
  
  return b = Concrete (\guts -> (b, guts))

----------------------------------------------------------------------
 -- Generic analysis with no shared component
----------------------------------------------------------------------
  
-- GenericAnalysis :: * -> * -> *
-- parametrized by guts and passed result
data GenericAnalysis s g b = GCFA {
  gf :: g -> [(b, g)]
}

-- Curry GenericAnalysis for the fixed guts
instance Monad (GenericAnalysis s g) where
  (>>=) (GCFA f) g = GCFA (\ guts ->
    concatMap (\ (a, guts') -> (gf $ g(a)) guts') (f guts))

  return a = GCFA (\ guts -> [(a,guts)])

----------------------------------------------------------------------
 -- Single store-threading analysis.
----------------------------------------------------------------------
 
data SingleStoreAnalysis a s g b = SSFA { runWithStore :: s -> g -> (s, [(b, g)]) }

-- TODO redefine store-like logic
instance Lattice s => Monad (SingleStoreAnalysis a s g) where
  (>>=) (SSFA f) g = SSFA (\st -> \guts -> 
     let (st', pairs) = f st guts -- make an f-step
         -- get new results via g :: [(st, [(b, g)])]
         newResults = List.map (\(a, guts') -> (runWithStore $ g(a)) st' guts') pairs
         -- merge stores and concatenate the results :: (st, [(b, g)])
         -- requires a lattice structure of a store
      in foldl (\(s, bg) -> \(s', bg') -> (s ⊔ s', bg ++ bg'))
               (st', []) newResults)

  return a = SSFA (\s -> \guts -> (s, [(a, guts)]))


