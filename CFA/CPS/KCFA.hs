{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module CFA.CPS.KCFA where

import Data.Map as Map

import CFA.CPS
import CFA.Lattice
import CFA.CPS.Analysis


class KCFA a where
  getK :: a -> Int

data KTime = KCalls [CExp] 
  deriving (Eq, Ord, Show)

data KAddr = KBind Var KTime
  deriving (Eq, Ord, Show)

instance (KCFA KTime) => Addressable KAddr KTime where
 τ0 = KCalls []
 valloc v t = KBind v t
 advance proc (call, ρ) t@(KCalls calls) = 
  KCalls $ take (getK t) (call : calls) 

-- Simple store
instance StoreLike KAddr (Store KAddr) where
 σ0 = Map.empty  

 bind σ a d = σ ⨆ [a ==> d]
 fetch σ a = σ CFA.Lattice.!! a  
 replace σ a d = σ ⨆ [a ==> d]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ
