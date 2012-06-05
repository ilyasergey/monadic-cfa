{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis.SingleStore.SingleStoreGC where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CFAMonads
import CFA.CPS.Analysis

instance (Ord a, StoreLike a s (D a)) 
  => GarbageCollector (SharedAnalysis s0 s g) (PΣ a) where
  gc ps = SSFA (\σ -> \g -> 
        let rs = Set.map (\(v, a) -> a) (reachable ps σ)
            σ' = filterStore σ (\a -> not (Set.member a rs))
         in (σ', [((), g)]))
