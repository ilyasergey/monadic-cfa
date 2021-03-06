module CFA.CESK.Examples where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Store
import CFA.Runner

import CFA.CESK
import CFA.CESK.Analysis

----------------------------------------------------------------------
-- abstract interpreter with a per-state store
----------------------------------------------------------------------

import CFA.CESK.Analysis.Concrete

----------------------------------------------------------------------
-- example program
----------------------------------------------------------------------

-- ((λ (f g) (f g)) (λ (x) x) (λ (y) Exit))
idx  = Lam (("x", Ref ("x", "l1")), "l2")
idy  = Lam (("y", Ref ("y", "l3")), "l4")

comb = Lam (("f", Lam (("g", App (Ref ("f", "l8"), Ref ("g", "l9"), "l7")), "l6")), "l5")
ex   = App (App (comb, idx, "l11"), idy, "l10")

----------------------------------------------------------------------

concreteResult :: Exp -> Set (PState Addr, Time, Store Addr)
concreteResult = runAnalysis
