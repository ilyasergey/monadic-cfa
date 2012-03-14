{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module CFA.CESK.Examples where

-- Imports.
import Data.Map as Map
import Data.Set as Set

import CFA.Lattice
import CFA.Store

import CFA.CESK
import CFA.CESK.Analysis


-- -- provide the initial state
-- -- State = (Exp, Env, Addr)
-- state0 = (Lam (("x", Ref ("x", "l2")), "l1"), Map.empty, Call "l3" [])

-- -- define the denotational semantics of the first step
-- -- literally, mstep - is a denotational semantics, induced by the 
-- -- abstract machine over time and store
-- transition = mstep state0 :: KCFA (State Addr)

-- -- run analysis with the suplied time and store
-- result = kf transition (TMt [], undefined, Map.empty)