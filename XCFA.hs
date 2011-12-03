{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Main where

 -- Imports.
import CPS
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.Fix

import Debug.Trace

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
  deriving (Eq, Ord, Show)

ρ0 = Map.empty 

 -- Generic store.
type Store a = a :-> (D a)

 -- Abstract analysis interface.
 -- Type parameter "g" is for guts and is passed along
 -- Address is a part of the Semantic interface, but not of the analysis!!!
 -- So `a' parameter should not be in the analysis, only `g' for guts

 -- Do we really need functional dependencies between variables?
 -- 1. Indeed, guts define the underlying monad
 -- 2. Guts define addresses? - Yes, indeed
 -- !! No more dependencies is needed

 -- TODO: Explain to Matt and Jan the necessity of dependency
 -- variables, and why is it natural
 
class Monad (m g) => Analysis a g m | g->m, g->a where
  fun :: (Env a) -> AExp -> m g (Val a)
  arg :: (Env a) -> AExp -> m g (D a)

  ($=) :: a -> (D a) -> m g ()
 
  alloc :: Var -> m g a
  tick :: (PΣ a) -> m g ()

  stepAnalysis :: g -> PΣ a -> [(PΣ a, g)]
  inject :: CExp -> (PΣ a, g)

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
mnext ps@(Exit, ρ) = return $! ps

----------------------------------------------------------------------  
 -- Example: Concrete Semantics
----------------------------------------------------------------------

data Concrete g b = Concrete { 
    cf :: g -> (b, g)}

data CAddr = CBind Var Int
  deriving (Eq, Ord, Show)

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

  inject call = ((call, Map.empty), (bot, 0))               

----------------------------------------------------------------------
 -- Generic analysis.
----------------------------------------------------------------------

type ProcCh a = Maybe (Val a) -- Nondeterministic choice.

-- FunctionalDependencies again:
-- time defines addresses 
class (Ord a, Eq a) => Addressable a t | t->a where
  τ0 :: t
  valloc :: Var -> t -> a 
  advance :: Val a -> PΣ a -> t -> t 

-- and again:
-- Store uniquely defines the type of its addresses
class Storable a s | s->a where
  σ0 :: s
  bind :: s -> a -> (D a)-> s
  replace :: s -> a -> (D a) -> s
  fetch :: s -> a -> (D a)
  
-- GenericAnalysis :: * -> * -> *
-- parametrized by guts and passed result
data GenericAnalysis g b = GCFA {
  gf :: g -> [(b, g)]
}

-- Curry GenericAnalysis for the fixed guts
instance Monad (GenericAnalysis g) where
  (>>=) (GCFA f) g = GCFA (\ guts ->
    concatMap (\ (a, guts') -> (gf $ g(a)) guts') (f guts))
  return a = GCFA (\ guts -> [(a,guts)])

-- Instance of the analysis for some particular guts
instance (Addressable a t, Storable a s) 
   => Analysis a                -- address type
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

  inject call = ((call, Map.empty), (Nothing, σ0, τ0))

----------------------------------------------------------------------
 -- Example: KCFA from GenericAnalysis
----------------------------------------------------------------------

k = 1

data KAddr = KBind Var KTime
  deriving (Eq, Ord, Show)

data KTime = KCalls [CExp] 
  deriving (Eq, Ord, Show)


instance Addressable KAddr KTime where
 τ0 = KCalls []
 valloc v t = KBind v t
 advance proc (call, ρ) (KCalls calls) = 
  KCalls $ take k (call : calls) 

instance Storable KAddr (Store KAddr) where
 σ0 = Map.empty  

 bind σ a d = σ ⨆ [a ==> d]
 fetch σ a = σ Main.!! a  
 replace σ a d = σ ⨆ [a ==> d]

----------------------------------------------------------------------
 -- running the analysis
----------------------------------------------------------------------

 -- Abstract state-space exploration algorithm
 -- TODO: remove step counting and trace output 
loop :: (Analysis a g m, Ord a, Ord g, Show a, Show g) =>
        [(PΣ a, g)] -> Set (PΣ a, g) -> Int -> Set (PΣ a, g)
loop worklist visited step = 
  -- trace output
  trace ("Worklist [step " ++ show step ++ "]:\n" ++ show worklist ++ "\n") $
  let newStates = worklist >>= (\(state, config) -> 
                                 stepAnalysis config state)
      newWorkList = List.filter (\elem -> not (Set.member elem visited)) newStates 
   in if List.null newWorkList
      then visited
      else let newVisited = visited ⊔ (Set.fromList newWorkList)
            in loop newWorkList newVisited (step + 1)

-- compute an approximation
explore :: (Analysis a g m, Ord a, Ord g, Show a, Show g) => CExp -> Set (PΣ a, g)
explore program = loop [inject program] Set.empty 0

----------------------------------------------------------------------
-- example program
----------------------------------------------------------------------

-- ((λ (f g) (f g)) (λ (x) x) (λ (y) Exit))
idx  = Lam (["x"] :=> Call (Ref "x") [])
idy  = Lam (["y"] :=> Exit)
comb = Lam (["f", "g"] :=> Call (Ref "f") [Ref "g"])
ex   = Call comb [idx, idy]

-- concrete analysis is chosen by the type specification
concreteResult = explore ex :: Set (PΣ CAddr, (Store CAddr, Int))

-- TODO: Implement initial config
abstractResult = explore ex :: Set (PΣ KAddr, (ProcCh KAddr, Store KAddr, KTime))

{-----------------------------------------------------------
More ideas: 

1. Perhaps, introduce pre- and post-transition procedurec for fixpoint
computation management.

-----------------------------------------------------------}