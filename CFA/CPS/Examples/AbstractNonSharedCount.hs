module CFA.CPS.Examples where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice
import CFA.Store
import CFA.CPS.Analysis
import CFA.Runner

----------------------------------------------------------------------
-- abstract interpreter with a per-state store and counting
----------------------------------------------------------------------

import CFA.CPS.KCFA
import CFA.CPS.Analysis.NonShared
import CFA.CPS.Analysis.ReallyNonShared

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

instance KCFA KTime where
  getK = const 1

type AbstractGuts = (ProcCh KAddr, KTime)

abstractResultC :: CExp -> Set ((PΣ KAddr, AbstractGuts), StoreWithCount KAddr (D KAddr)) 
abstractResultC e = exploreFP mnext (e, ρ0)
