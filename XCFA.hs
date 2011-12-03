{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

 -- Imports.
import CPS
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.Fix

 -- Abbreviations.
type k :-> v = Map.Map k v
type ℙ a = Set.Set a

(==>) :: a -> b -> (a,b)
(==>) x y = (x,y)

(//) :: Ord k => (k :-> v) -> [(k,v)] -> (k :-> v)
(//) f [] = f
(//) f ((x,y):tl) = Map.insert x y (f // tl)


 -- Partial order theory.
class Lattice a where
 bot :: a
 top :: a
 (⊑) :: a -> a -> Bool
 (⊔) :: a -> a -> a
 (⊓) :: a -> a -> a


instance (Ord s, Eq s) => Lattice (ℙ s) where
 bot = Set.empty
 top = error "no representation of universal set"
 x ⊔ y = x `Set.union` y
 x ⊓ y = x `Set.intersection` y
 x ⊑ y = x `Set.isSubsetOf` y

instance (Ord k, Lattice v) => Lattice (k :-> v) where
 bot = Map.empty
 top = error "no representation of top map"
 f ⊑ g = Map.isSubmapOfBy (⊑) f g
 f ⊔ g = Map.unionWith (⊔) f g
 f ⊓ g = Map.intersectionWith (⊓) f g

(⨆) :: (Ord k, Lattice v) => (k :-> v) -> [(k,v)] -> (k :-> v)
f ⨆ [] = f
f ⨆ ((k,v):tl) = Map.insertWith (⊔) k v (f ⨆ tl)

(!!) :: (Ord k, Lattice v) => (k :-> v) -> k -> v
f !! k = Map.findWithDefault bot k f



 -- State-space.
type PΣ a = (CExp, Env a)
type Env a = Var :-> a
type D a = ℙ (Val a)
data Val a = Clo (Lambda, Env a)
  deriving (Eq,Ord)

ρ0 = Map.empty 

 -- Generic store.
type Store a = a :-> (D a)

 -- Abstract analysis interface.
 -- Type parameter "g" is for guts and is passed along
 -- Address is a part of the Semantic interface
 -- Not of the analysis!!!
 -- So `a' parameter should not be in the analysis
class Monad (m g) => Analysis a g m where
  fun :: (Env a) -> AExp -> m g (Val a)
  arg :: (Env a) -> AExp -> m g (D a)

  ($=) :: a -> (D a) -> m g ()
 
  alloc :: Var -> m g a
  tick :: (PΣ a) -> m g ()

  stepAnalysis :: g -> PΣ a -> [(PΣ a, g)]

 -- Generic analysis.
type ProcCh a = Maybe (Val a) -- Nondeterministic choice.

class Storable a s where
  σ0 :: s
  bind :: s -> a -> (D a)-> s
  replace :: s -> a -> (D a) -> s
  fetch :: s -> a -> (D a)

class (Ord a, Eq a) => Addressable a t where
  t0 :: t

  valloc :: Var -> t -> a 
  advance :: Val a -> PΣ a -> t -> t 
  
-- GenericAnalysis :: * -> * -> * -> *
data GenericAnalysis g b = GCFA {
  gf :: g -> [(b, g)]
}

-- Curry GenericAnalysis for the given guts
instance Monad (GenericAnalysis g) where
  (>>=) (GCFA f) g = GCFA (\ guts ->
    concatMap (\ (a, guts') -> (gf $ g(a)) guts') (f guts))
  return a = GCFA (\ guts -> [(a,guts)])

-- Instance of the analysis for some particular guts
instance (Addressable a t, Storable a s) 
   => Analysis a 
               (ProcCh a, s, t) -- Generic Analysis' guts
      (GenericAnalysis) where
  fun ρ (Lam l) = GCFA (\ (_,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (proc, (Just proc,σ,t)) ])
  fun ρ (Ref v) = GCFA (\ (_,σ,t) -> 
    let procs = fetch σ (ρ!v)
     in [ (proc, (Just proc,σ,t)) | proc <- Set.toList procs ]) 

  arg ρ (Lam l) = GCFA (\ (ch,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (Set.singleton proc, (ch, σ, t)) ])
  arg ρ (Ref v) = GCFA (\ (ch,σ,t) -> 
    let procs = fetch σ (ρ!v)
     in [ (procs, (ch, σ, t)) ])

  a $= d = GCFA (\ (ch,σ,t) -> [((),(ch,bind σ a d,t))] )

  alloc v = GCFA (\ (ch,σ,t) -> [(valloc v t, (ch, σ, t))])

  tick ps = GCFA (\ (Just proc, σ, t) ->
     [((), (Just proc, σ, advance proc ps t))])

  stepAnalysis config state = gf (mnext state) $ config

 -- Generic transition
mnext :: Analysis a g m => (PΣ a) -> m g (PΣ a)
mnext ps@(Call f aes, ρ) = do  
  proc@(Clo (vs :=> call', ρ')) <- fun ρ f
  tick ps
  as <- mapM alloc vs
  ds <- mapM (arg ρ) aes 
  let ρ'' = ρ' // [ v ==> a | v <- vs | a <- as ]
  sequence [ a $= d | a <- as | d <- ds ]
  return $! (call', ρ'')


 -- Example: Concrete Semantics

-- Need to pass an unused type parameter `g' for "guts"
-- Problem: no dependency between "a" and "g" is captured
data Concrete g b = Concrete { 
    cf :: g -> (b, g)}

data CAddr = CBind Var Int
  deriving (Eq, Ord)

instance Monad (Concrete g) where
  (>>=) (Concrete f) g = Concrete (\guts ->
    let (b, guts') = f guts
     in (cf $ g(b)) guts')
  return b = Concrete (\guts -> (b, guts))

instance Analysis CAddr 
                  (Store CAddr, Int) 
         (Concrete) where
  fun ρ (Lam l) = Concrete (\ (σ,t) -> 
    let proc = Clo(l, ρ)
     in (proc,(σ,t)))
  fun ρ (Ref v) = Concrete (\ (σ,t) -> 
    let [proc] = Set.toList $ σ!(ρ!v)
     in (proc,(σ,t)))

  arg ρ (Lam l) = Concrete (\ (σ,t) ->
    let proc = Clo(l, ρ) 
     in (Set.singleton proc, (σ, t)))
  arg ρ (Ref v) = Concrete (\ (σ,t) -> 
    let procs = σ!(ρ!v)
     in (procs, (σ, t)))

  a $= d = Concrete (\ (σ,t) -> ((), (σ ⨆ [a ==> d],t)) )

  alloc v = Concrete (\ (σ,t) -> (CBind v t, (σ, t)))

  tick (call, ρ) = Concrete (\ (σ,n) -> ((), (σ, n+1)))

  stepAnalysis config state = [cf (mnext state) config]

 -- Example: KCFA from GenericAnalysis

k = 1

data KAddr = KBind Var KTime
  deriving (Eq,Ord)

data KTime = KCalls [CExp] 
  deriving (Eq,Ord)


instance Addressable KAddr KTime where
 t0 = KCalls []

 valloc v t = KBind v t
 advance proc (call, ρ) (KCalls calls) = 
  KCalls $ take k (call : calls) 

instance Storable KAddr (Store KAddr) where
 σ0 = Map.empty  

 bind σ a d = σ ⨆ [a ==> d]
 fetch σ a = σ Main.!! a  
 replace σ a d = σ ⨆ [a ==> d]

-- running the analysis

-- TODO
-- define `stepAnalysis' function as `runState'

-- initial parameters for the analysis 
-- (reminiscent to the initial state)

-- Some particular case (bottom for the iteration)
-- see http://hackage.haskell.org/packages/archive/base/latest/doc/html/Control-Monad-Fix.html#t:MonadFix

--initConfigGF :: (ProcCh KAddr, Store KAddr, KTime)
initConfigGF state = undefined 
--(state, Just (undefined :: Val KAddr), Map.empty, KCalls [])       

--stepAnalysis :: Analysis a g (Concrete a) => g -> PΣ a -> (PΣ a, g)
--stepAnalysis config state = cf (mnext state) config

-- Insight: analysis shouldn't depen on the semanticsc  
instance MonadFix (GenericAnalysis g) where
  mfix trans = 
     let state0 = undefined -- how to obtain it ?!!
     in (return state0) -- iteration zero: return initial state
        >>= trans 
        >>= trans 
        >>= trans -- and so on...

-----------------------------

 -- Abstract state-space exploration algorithm
-- explore :: 
--   (Ord t, Ord s, Analysis a m, Addressable a t, Storable a s) 
--   => PΣ a -> Set.Set (PΣ a, ProcCh a, s, t)
-- explore state0 =
--  let 
--   -- fixpoint iteration
--   iterate :: [(PΣ a, ProcCh a, s, t)] -> 
--              Set.Set (PΣ a, ProcCh a, s, t) -> 
--              Set.Set (PΣ a, ProcCh a, s, t) 
--   iterate worklist visited = 
--     let newStates = worklist >>= (\(state, ch, s, t) -> 
--                                    stepAnalysis (ch, s, t) state)
--         -- new states
--         newWorkList = List.filter (\elem -> Set.member elem visited) newStates 
--         in if List.null newWorkList
--            then visited -- fixpoint reached
--            else let newVisited = visited ⊔ (Set.fromList newWorkList)
--                 in iterate newWorkList newVisited

--  in iterate [(initConfigGF state0)] Set.empty


{-

1. Perhaps, introduce pre- and post-transition procedurec for fixpoint
computation management.

-}