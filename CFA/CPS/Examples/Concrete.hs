module CFA.CPS.Examples where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.CPS.Analysis
import CFA.CPS.Analysis.Runner

----------------------------------------------------------------------
-- concrete interpreter
----------------------------------------------------------------------

import CFA.CPS.Analysis.Concrete

----------------------------------------------------------------------
-- example program
----------------------------------------------------------------------

-- ((λ (f g) (f g)) (λ (x) x) (λ (y) Exit))
idx  = Lam (["x"] :=> Call (Ref "x") [])
idy  = Lam (["y"] :=> Exit)
comb = Lam (["f", "g"] :=> Call (Ref "f") [Ref "g"])
ex   = Call comb [idx, idy]

ucombx = Lam (["x"] :=> Call (Ref "x") [Ref "x"])
ucomby = Lam (["y"] :=> Call (Ref "y") [Ref "y"])
omega = Call ucombx [ucomby]

----------------------------------------------------------------------

type ConcreteGuts = (Store CAddr, Int)

concreteResult :: CExp -> ((), Set (PΣ CAddr, ConcreteGuts))
concreteResult = explore
