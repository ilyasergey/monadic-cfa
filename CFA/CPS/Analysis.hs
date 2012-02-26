{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- TODO: get rid of this
{-# LANGUAGE UndecidableInstances #-}

module CFA.CPS.Analysis where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.CPS
import CFA.Lattice

----------------------------------------------------------------------  
-- Abstract analysis interface.
----------------------------------------------------------------------  
-- Type parameter "g" is for guts and is passed along
-- Address is a part of the Semantic interface, but not of the analysis!!!
-- So `a' parameter should not be in the analysis, only `g' for guts

-- Do we really need functional dependencies between variables?
-- 1. Indeed, guts define the underlying monad
-- 2. Guts define the shared component
-- !! No more dependencies is needed

class Monad (m s g) => Analysis m a s g | g -> m, m -> s, g -> a where
  fun :: (Env a) -> AExp -> m s g (Val a)
  arg :: (Env a) -> AExp -> m s g (D a)

  ($=) :: a -> (D a) -> m s g ()

  updateEnv :: Env a -> [(Var, a)] ->  m s g (Env a)
  -- default implementation
  updateEnv ρ bs = return $ ρ // bs
 
  alloc :: Var -> m s g a
  tick :: (PΣ a) -> m s g ()

  stepAnalysis :: s -> g -> PΣ a -> (s, [(PΣ a, g)])
  inject :: CExp -> (PΣ a, s, g)

----------------------------------------------------------------------  
-- Generic transition
----------------------------------------------------------------------  
mnext :: Analysis m a s g => (PΣ a) -> m s g (PΣ a)
mnext ps@(Call f aes, ρ) = do  
  proc@(Clo (vs :=> call', ρ')) <- fun ρ f
  tick ps
  as  <- mapM alloc vs
  ds  <- mapM (arg ρ) aes 
  ρ'' <- updateEnv ρ' [ v ==> a | v <- vs | a <- as ]
  sequence [ a $= d | a <- as | d <- ds ]
  return $! (call', ρ'')
mnext ps@(Exit, ρ) = return $! ps

----------------------------------------------------------------------
 -- Addresses, Stores and Choices
----------------------------------------------------------------------

type ProcCh a = Maybe (Val a) -- Nondeterministic choice.

-- FunctionalDependencies again:
-- time defines addresses 
class (Ord a, Eq a) => Addressable a c | c -> a where
  τ0 :: c
  valloc :: Var -> c -> a 
  advance :: Val a -> PΣ a -> c -> c 

-- and again:
-- Store uniquely defines the type of its addresses
class (Eq a, Lattice s) => StoreLike a s | s -> a where
  σ0 :: s
  bind :: s -> a -> (D a)-> s
  replace :: s -> a -> (D a) -> s
  fetch :: s -> a -> (D a)
  filterStore :: s -> (a -> Bool) -> s 

----------------------------------------------------------------------
 -- Abstract Garbage Collection
----------------------------------------------------------------------

-- Abstract garbage collector
class Monad m => GarbageCollector m a where
  gc :: (PΣ a) -> m (PΣ a)
  -- default implementation
  gc = return

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
 -- Abstract Counting
----------------------------------------------------------------------

-- Abstract natural number
data AbsNat = AZero | AOne | AMany
     deriving (Ord, Eq, Show)

instance Lattice AbsNat where
 bot = AZero
 top = AMany
 n ⊑ m = (n == bot) || (m == top) || (n == m)
 n ⊔ m = if (n ⊑ m) then m else n
 n ⊓ m = if (n ⊑ m) then n else m

-- Abstract addition
(⊕) :: AbsNat -> AbsNat -> AbsNat
AZero ⊕ n = n
n ⊕ AZero = n
n ⊕ m = AMany

class StoreLike a s => ACounter a s where
  count :: s -> a -> AbsNat

-- Counting store
type StoreWithCount a = a :-> ((D a), AbsNat)

instance (Ord a) => ACounter a (StoreWithCount a) where
 -- fetching with default bottom
 count σ a = snd $ σ CFA.Lattice.!! a         

-- counter is nullified when filtered
-- and incremented when `bind' is called
instance (Ord a) => StoreLike a (StoreWithCount a) where
 σ0 = Map.empty  
 bind σ a d = σ `update_add` [a ==> (d, AOne)]
 fetch σ a = fst $ σ CFA.Lattice.!! a  
 replace σ a d = σ ⨆ [a ==> (d, AZero)]
 filterStore σ p = Map.filterWithKey (\k -> \v -> p k) σ

update_add :: (Ord k, Lattice v) => (k :-> (v, AbsNat)) -> [(k, (v, AbsNat))] -> (k :-> (v, AbsNat))
update_add f [] = f
update_add f ((k,v):tl) = Map.insertWith (\(x1, y1) -> \(x2, y2) -> (x1 ⊔ x2, y1 ⊕ y2)) k v (update_add f tl)

----------------------------------------------------------------------
 -- Anodization
----------------------------------------------------------------------

class StoreLike a s => AlkaliLike a s where
  addUniqueAddr  :: a -> s
  deAnodizeStore :: s -> s 
  deAnodizeEnv   :: s -> Env a -> Env a
  deAnodizeD     :: s -> D a -> D a
  reset          :: s -> s

-- a usefule instance
instance (Ord a, StoreLike a s) => StoreLike a (s, ℙ a) where 
 σ0 = (σ0, Set.empty)
 bind σ a d = (bind (fst σ) a d, snd σ)
 fetch σ a = fetch (fst σ) a 
 replace σ a d = (replace (fst σ) a d, snd σ)
 filterStore σ p = (filterStore (fst σ) p, snd σ)

-- TODO: implement!