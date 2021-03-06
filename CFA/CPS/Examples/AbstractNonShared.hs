module CFA.CPS.Examples where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.CFAMonads
import CFA.Lattice
import CFA.CPS.Analysis
import CFA.Runner
import Control.Monad.State
import Control.Monad.List
import Control.Monad.Identity
import Control.Monad.Reader

----------------------------------------------------------------------
-- abstract interpreter with a per-state store
----------------------------------------------------------------------

import CFA.Store
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
  getK = const 2

type AbstractGuts = (ProcCh KAddr, KTime)

reallyNonSharedResultC_ :: CExp -> Set ((PΣ KAddr, AbstractGuts), Store KAddr)
reallyNonSharedResultC_ e = unRNSFP $ exploreFP mnext (e, ρ0)

nonSharedResultC :: CExp -> Set ((PΣ KAddr, AbstractGuts), Store KAddr)
nonSharedResultC e = exploreFP mnext (e, ρ0)
