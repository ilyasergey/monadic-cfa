module CFA.Analysis.Proof where

import Data.Set as Set
import Data.Foldable as Foldable

import CFA.Lattice
import CFA.CPS
import CFA.CPS.Analysis

import CFA.CPS.Analysis.SingleStore
import CFA.CPS.Analysis.ReallyNonShared

-- conjecture:
--  if g :: b -> c
--     f :: a -> Set b
--  then
--    joinWith g . joinWith f
--      ===
--    joinWith (joinWith g . f)
-- proof:
--   ?

-- conjecture 2:
--   f ⊑ g    then   joinWith f ⊑ joinWith g

-- conjecture 3:
-- joinWith f . map g == joinWith (f . g)

-- proof:
--   joinWith g . joinWith f

-- conjecture 4:
-- joinWith (\x -> (f x, g x)) == (\xs -> joinWith f xs, joinWith g xs)

alpha :: (Lattice s, Ord a, Ord t) =>
        ℙ ((PΣ a, (ProcCh a, t)), s) -> (ℙ (PΣ a, (ProcCh a, t)), s)
alpha = joinWith (\((p, g), s) -> (Set.singleton (p,g), s))

-- lemma 0:
--  alpha a `union` alpha b == alpha (a `union` b)
-- lemma 1:
--   foldr ((⊔) . f) bot
--        ⊑  
--   foldr ((⊔) . g) bot        
--      if f ⊑ g

-- lemma 2:
--    foldr ((⊔) . f) bot . foldr (Set.union . g) Set.empty 
--      

-- to prove: alpha . applyStepToFP mnext ⊑ applyStepToFP mnext . alpha
-- joinWith (\((p, g), s) -> (Set.singleton (p,g), s)) .
--     joinWith (\ ((p,g),s) -> Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s))
   where g == (\((p, g), s) -> (Set.singleton (p,g), s))
         f == (\ ((p,g),s) -> Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s))
       joinWith (joinWith g . f) ===
       joinWith (joinWith (\((p, g), s) -> (Set.singleton (p,g), s)) . (\ ((p,g),s) -> Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s))) ===
       joinWith ((\((p,g),s) -> joinWith (\((p, g), s) -> (Set.singleton (p,g), s)) $ Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s))) 
       joinWith ((\((p,g),s) -> (joinWith (\((p, g), s) -> (Set.singleton (p,g))) $ Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s),
                                 joinWith (\((p, g), s) -> s) $ Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s)))) 

       joinWith (\((p,g),s) -> let newStates = Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s)
                               in (Set.map (\((p, g), s) -> (p,g)) newStates,
                                   joinWith (\((p, g), s) -> s) newStates)) 

       joinWith (\((p,g),s) -> let newStates = Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s)
                               in (joinWith (\((p, g), s) -> Set.singleton (p,g)) newStates,
                                   joinWith (\((p, g), s) -> s) newStates)) 

       \states -> joinWith (\((p,g),s) -> let newStates = Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s)
                                           in joinWith (\((p, g), s) -> (Set.singleton (p,g), s)) newStates) states

       \states -> joinWith (\((p,g),s) -> joinWith (\((p', g'),s') -> (Set.singleton (p',g'), s')) (Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s))) states

       \states -> joinWith (\((p,g),s) -> alpha (Set.fromList $ runIdentity $ collectListT (runStateT (runStateT (gc $ step p) g) s))) states

-- \states -> joinWith (\((p,g),_) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) (joinWith (\((p,g),s) -> s) states)) states

-- (\states -> joinWith (let s' = joinWith (\((p,g),s) -> s) states
--                       in \(p,g) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s' . (\((p, g), s) -> (p,g))) states)

-- (\states -> let s' = joinWith (\((p,g),s) -> s) states
--              in joinWith (\(p,g) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s' . (\((p, g), s) -> (p,g))) states)

-- (\states -> let states' = map (\((p, g), s) -> (p,g)) states
--                 s = joinWith (\((p,g),s) -> s) states
--             in joinWith (\(p,g) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s) states')
-- (\states -> (let (states', s) = (map (\((p, g), s) -> (p,g)) states, joinWith (\((p,g),s) -> s) states)) in joinWith (\(p,g) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s) states')
-- (\states -> (\(states', s) -> joinWith (\(p,g) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s) states') $ (map (\((p, g), s) -> (p,g)) states, joinWith (\((p,g),s) -> s) states))
-- (\(states, s) -> joinWith (\(p,g) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s) states) . (\states -> (map (\((p, g), s) -> (p,g)) states, joinWith (\((p,g),s) -> s) states))
-- (\(states, s) -> joinWith (\(p,g) -> mapFst Set.fromList $ runIdentity $ collectSSListTS (runStateT (gc $ step p) g) s) states) . (joinWith (\((p, g), s) -> (Set.singleton (p,g), s)))

