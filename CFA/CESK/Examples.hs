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
import CFA.CFAMonads

import CFA.CESK
import CFA.CESK.Analysis
import CFA.CESK.Analysis.Concrete


-- provide the initial state
-- State = (Exp, Env, Addr)

lam1 = Lam (("x", Ref ("x", "l2")), "l1")
arg1 = Lam (("y", Ref ("y", "l6")), "l5")
app = App (lam1, arg1, "l7")

state0 = (app, Map.empty, Call "l3" [])

-- define the denotational semantics of the first step
-- literally, mstep - is a denotational semantics, induced by the 
-- abstract machine over time and store
transition :: Concrete () (Time, State Addr, Store Addr) (State Addr)
transition = mstep state0 >>= mstep

-- run analysis with the suplied time and store
result = cf transition (TMt [], undefined, Map.empty)