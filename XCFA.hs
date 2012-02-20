{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module Main where

 -- Imports.
import CPS
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.Fix

 -- debug
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

-- unit is a trivial lattice
instance Lattice () where
 bot = ()
 top = ()
 x ⊔ y = top
 x ⊓ y = bot
 x ⊑ y = True

instance (Lattice a, Lattice b) => Lattice (a, b) where
 bot = (bot, bot)
 top = (top, top)
 (a1, b1) ⊔ (a2, b2) = (a1 ⊔ a2, b1 ⊔ b2)
 (a1, b1) ⊓ (a2, b2) = (a1 ⊓ a2, b1 ⊓ b2)
 (a1, b1) ⊑ (a2, b2) = (a1 ⊑ a2) && (b1 ⊑ b2)

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
 -- 2. Guts define the shared component
 -- !! No more dependencies is needed

class Monad (m s g) => Analysis m a s g | g->m, m->s, g->a where
  fun :: (Env a) -> AExp -> m s g (Val a)
  arg :: (Env a) -> AExp -> m s g (D a)

  ($=) :: a -> (D a) -> m s g ()
 
  alloc :: Var -> m s g a
  tick :: (PΣ a) -> m s g ()

  stepAnalysis :: s -> g -> PΣ a -> (s, [(PΣ a, g)])
  inject :: CExp -> (PΣ a, s, g)

-- Abstract garbage collector
class Monad m => GarbageCollector m a where
  gc :: (PΣ a) -> m (PΣ a)
  -- default implementation
  gc = return

-- Generic transition
mnext :: Analysis m a s g => (PΣ a) -> m s g (PΣ a)
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

data Concrete s g b = Concrete { 
    cf :: g -> (b, g)
}

data CAddr = CBind Var Int
  deriving (Eq, Ord, Show)

instance Monad (Concrete s g) where
  (>>=) (Concrete f) g = Concrete (\guts ->
    let (b, guts') = f guts
     in (cf $ g(b)) guts')
  return b = Concrete (\guts -> (b, guts))

instance Analysis (Concrete) 
                  CAddr 
                  ()
                  (Store CAddr, Int) 
                  where
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

  stepAnalysis _ config state = ((), [cf (mnext state >>= gc) config])

  inject call = ((call, Map.empty), (), (bot, 0))

-- Add Garbage Collection
instance GarbageCollector (Concrete () (Store CAddr, Int)) CAddr

----------------------------------------------------------------------
 -- Addresses, Stores and Choices
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
class Lattice s => StoreLike a s | s->a where
  σ0 :: s
  bind :: s -> a -> (D a)-> s
  replace :: s -> a -> (D a) -> s
  fetch :: s -> a -> (D a)
  filterStore :: s -> (a -> Bool) -> s 

----------------------------------------------------------------------
 -- Generic analysis with no shared component
----------------------------------------------------------------------
  
-- GenericAnalysis :: * -> * -> *
-- parametrized by guts and passed result
data GenericAnalysis s g b = GCFA {
  gf :: g -> [(b, g)]
}

-- Curry GenericAnalysis for the fixed guts
instance Monad (GenericAnalysis s g) where
  (>>=) (GCFA f) g = GCFA (\ guts ->
    concatMap (\ (a, guts') -> (gf $ g(a)) guts') (f guts))
  return a = GCFA (\ guts -> [(a,guts)])

instance (Addressable a t, StoreLike a s) 
   => Analysis (GenericAnalysis)
               a                -- address type
               ()               -- no shared result
               (ProcCh a, s, t) -- Generic Analysis' guts
               where
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

  stepAnalysis _ config state = ((), gf (mnext state >>= gc) config)

  inject call = ((call, Map.empty), (), (Nothing, σ0, τ0))

-- Garbage Collection
instance GarbageCollector (GenericAnalysis () (ProcCh a, s, t)) a
  
----------------------------------------------------------------------
 -- Single store-threading analysis.
----------------------------------------------------------------------
  
data StoreLike a s => SingleStoreAnalysis a s g b = SSFA {
  runWithStore :: s -> g -> (s, [(b, g)])
}

-- TODO redefine store-like logic
instance StoreLike a s => Monad (SingleStoreAnalysis a s g) where
  (>>=) (SSFA f) g = SSFA (\st -> \guts -> 
     let (st', pairs) = f st guts -- make an f-step
         -- get new results via g :: [(st, [(b, g)])]
         newResults = List.map (\(a, guts') -> (runWithStore $ g(a)) st' guts')
                               pairs
         -- merge stores and concatenate the results :: (st, [(b, g)])
         -- requires a lattice structure of a store
      in foldl (\(s, bg) -> \(s', bg') -> (s ⊔ s', bg ++ bg'))
               (st', []) newResults)

  return a = SSFA (\s -> \guts -> (s, [(a, guts)]))

instance (Addressable a t, StoreLike a s) 
   => Analysis (SingleStoreAnalysis a) 
               a                     -- address type
               s                     -- shared store
               (ProcCh a, t)         -- SingleStore Analysis' guts
               where
  fun ρ (Lam l) = SSFA (\σ -> \(_,t) ->
    let proc = Clo(l, ρ) 
     in (σ, [(proc, (Just proc,t)) ]))
  fun ρ (Ref v) = SSFA (\σ -> \(_,t) -> 
    let procs = fetch σ (ρ!v)
     in (σ, [ (proc, (Just proc,t)) | proc <- Set.toList procs ])) 

  arg ρ (Lam l) = SSFA (\σ -> \(ch, t) -> 
    let proc = Clo(l, ρ) 
     in (σ, [ (Set.singleton proc, (ch, t)) ]))
  arg ρ (Ref v) = SSFA (\σ -> \(ch, t) -> 
    let procs = fetch σ (ρ!v)
     in (σ, [ (procs, (ch,t)) ]))

  a $= d = SSFA (\σ -> \(ch, t) -> 
    let σ' = bind σ a d
    in (σ', [((), (ch, t))] ))

  alloc v = SSFA (\σ -> \(ch, t) -> (σ, [(valloc v t, (ch, t))]))

  tick ps = SSFA (\σ -> \ (Just proc, t) ->
     (σ, ([((), (Just proc, advance proc ps t))])))

  stepAnalysis store config state = runWithStore (mnext state >>= gc) store config

  inject call = ((call, Map.empty), σ0, (Nothing, τ0))


-- Enhance GC for single-store analysis

instance (Ord a, StoreLike a s) 
  => GarbageCollector ((SingleStoreAnalysis a) s g) a where
  gc ps = SSFA (\σ -> \g -> 
        let rs = Set.map (\(v, a) -> a) (reachable ps σ)
            σ' = filterStore σ (\a -> not (Set.member a rs))
         in (σ', [(ps, g)]))

----------------------------------------------------------------------
 -- Abstract Garbage Collection
----------------------------------------------------------------------

-- Free Variables
free' :: CExp -> Set Var -> Set Var
free' Exit bound = Set.empty
free' (Call f as) bound = foldl (\res -> \a -> res ⊔ (free a bound)) 
                                (free f bound) as

free :: AExp -> Set Var -> Set Var
free (Ref v) bound = if (Set.member v bound) 
                     then Set.empty 
                     else Set.singleton v
free (Lam (vs :=> ce)) bound = free' ce (bound ⊔ (Set.fromList vs))

-- `touched' (for expressions and environments)
touched' :: (Ord a) => AExp -> Env a -> Set (Var, a)
touched' f ρ = Set.fromList [(v, ρ!v) | v <- Set.toList(free f Set.empty)] 

-- `touched' for states
touched :: (Ord a) => (PΣ a) -> Set (Var, a)
touched (Call f as, ρ) = (touched' f ρ) ⊔ 
                         Set.fromList [bs | a <- as, 
                                            bs <- Set.toList (touched' a ρ)]
touched (Exit, _) = Set.empty

-- `adjacency'
adjacent :: (Ord a, StoreLike a s) => (Var, a) -> s -> Set (Var, a)
adjacent (v, addr) σ = Set.fromList [b | Clo (f, ρ) <- Set.toList(fetch σ addr),
                                         b <- Set.toList (touched' (Lam f) ρ)]

-- `reachability'
reachable :: (Ord a, StoreLike a s) => (PΣ a) -> s -> Set (Var, a)
reachable state σ = 
  let collect bs =
        -- fixpoint iteration
        let newBindings = [b' | b  <- Set.toList bs, 
                                b' <- Set.toList (adjacent b σ)]
            newResult = bs ⊔ (Set.fromList newBindings)
         in if newResult == bs
            then bs
            else collect newResult 
   -- reflexive-transitive closure
   in collect (touched state)


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

-- Simple store
instance StoreLike KAddr (Store KAddr) where
 σ0 = Map.empty  

 bind σ a d = σ ⨆ [a ==> d]
 fetch σ a = σ Main.!! a  
 replace σ a d = σ ⨆ [a ==> d]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ

----------------------------------------------------------------------
 -- Abstract Counting
----------------------------------------------------------------------

-- abstract counter
data AbsNat = AZero | AOne | AMany
     deriving (Ord, Eq, Show)

-- abstract addition
aplus :: AbsNat -> AbsNat -> AbsNat
aplus AZero n = n
aplus n AZero = n
aplus n m = AMany

instance Lattice AbsNat where
 bot = AZero
 top = AMany
 n ⊑ m = (n == bot) || (m == top) || (n == m)
 n ⊔ m = if (n ⊑ m) then m else n
 n ⊓ m = if (n ⊑ m) then n else m

class StoreLike a s => ACounter a s where
  count :: s -> a -> AbsNat

-- Counting store
type StoreWithCount a = a :-> ((D a), AbsNat)

-- counter is nullified when filtered
-- and incremented when `bind' is called
instance (Ord a) => StoreLike a (StoreWithCount a) where
 σ0 = Map.empty  
 bind σ a d = σ `update_add` [a ==> (d, AOne)]
 fetch σ a = fst $ σ Main.!! a  
 replace σ a d = σ ⨆ [a ==> (d, AZero)]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ

update_add :: (Ord k, Lattice v) => (k :-> (v, AbsNat)) -> [(k, (v, AbsNat))] -> (k :-> (v, AbsNat))
update_add f [] = f
update_add f ((k,v):tl) = Map.insertWith (\(x1, y1) -> \(x2, y2) -> (x1 ⊔ x2, y1 `aplus` y2)) k v (update_add f tl)

instance (Ord a) => ACounter a (StoreWithCount a) where
 -- fetching with default bottom
 count σ a = snd $ σ Main.!! a         

----------------------------------------------------------------------
 -- running the analysis
----------------------------------------------------------------------

-- Abstract state-space exploration algorithm
-- TODO: remove step counting and trace output 
loop :: (Analysis m a s g, Ord a, Ord g, Show a, Show g, Lattice s) =>
        [(PΣ a, g)] -> (s, Set (PΣ a, g)) -> Int -> (s, Set (PΣ a, g))

loop worklist v@(shared, oldStates) step = 
  -- trace output
  trace ("Worklist [step " ++ show step ++ "]:\n" ++ show worklist ++ "\n") $
  let newStoreStates = List.map (\(state, config) -> 
                                    stepAnalysis shared config state)
                                    worklist 
      -- compute a new shared component and new states
      (shared', states') = foldl (\(s, bg) -> \(s', bg') -> (s ⊔ s', bg ++ bg'))
                                 (shared, []) newStoreStates
      newWorkList = List.filter (\elem -> not (Set.member elem oldStates)) states'
   in if List.null newWorkList
      then v
      else let newVisited = (shared', oldStates ⊔ (Set.fromList newWorkList))
            in loop newWorkList newVisited (step + 1)

 -- compute an approximation
explore :: (Analysis m a s g, Ord a, Ord g, Show a, Show g, Lattice s) => 
        CExp -> (s, Set (PΣ a, g))

explore program = 
  let (state0, σ0, g0) = inject program
   in loop [(state0, g0)] (σ0, Set.empty) 0

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

-- a particular analysis is chosen by the type specification

-- concrete interpreter
type ConcreteGuts = (Store CAddr, Int)

concreteResult :: CExp -> ((), Set (PΣ CAddr, ConcreteGuts))
concreteResult = explore

-- abstract interpreter with a per-state store
type AbstractGuts = (ProcCh KAddr, Store KAddr, KTime)

abstractResult :: CExp -> ((), Set (PΣ KAddr, AbstractGuts))
abstractResult = explore 

-- abstract interpreter with a per-state store and counting
type AbstractGutsWithCounting = (ProcCh KAddr, StoreWithCount KAddr, KTime)

abstractResultC :: CExp -> ((), Set (PΣ KAddr, AbstractGutsWithCounting))
abstractResultC = explore 

type AbstractGutsSS = (ProcCh KAddr, KTime)
-- abstract interpreter with a single-threaded store
-- Functional dependencies are in the conflict for same guts, 
-- so only one analysis should be uncommented

-- abstractResultSS :: CExp -> (Store KAddr, Set (PΣ KAddr, AbstractGutsSS))
-- abstractResultSS = explore

-- abstract interpreter with a single-threaded store and counting

abstractResultSSC :: CExp -> (StoreWithCount KAddr, Set (PΣ KAddr, AbstractGutsSS))
abstractResultSSC = explore  


{-----------------------------------------------------------
More ideas: 

1. Perhaps, introduce pre- and post-transition procedure 
for fixpoint computation management (relevant for p.2)

----------------------------------------------------------}
