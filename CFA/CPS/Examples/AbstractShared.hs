module CFA.CPS.Examples where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

import CFA.CPS
import CFA.CFAMonads
import CFA.Lattice
import CFA.Store
import CFA.CPS.Analysis
import CFA.CPS.Analysis.Runner
import CFA.CPS.Analysis.SingleStore

----------------------------------------------------------------------
-- abstract interpreter with a single-threaded store
----------------------------------------------------------------------

import CFA.CPS.KCFA
import CFA.CPS.Analysis.SingleStore

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


type AbstractGutsSS = (ProcCh KAddr, KTime)

-- abstractResultSSC :: CExp -> (Set (PΣ KAddr, AbstractGutsSS), Store KAddr)
-- abstractResultSSC e = snd $ snd go 
--   where go :: ([()], (Store KAddr, (Set (PΣ KAddr, AbstractGutsSS), Store KAddr)))
--         go = runIdentity $ runSSListT0 $ runReaderT (explore e) initialGutsSS

abstractResultSSC :: CExp -> (Set (PΣ KAddr, AbstractGutsSS), Store KAddr)
abstractResultSSC e = exploreFP e
