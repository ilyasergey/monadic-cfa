{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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
import CFA.Store

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

class Monad m => Analysis m a | m -> a where
  fun :: Env a -> AExp -> m (Val a)
  arg :: Env a -> AExp -> m (D a)

  ($=) :: a -> D a -> m ()

  updateEnv :: Env a -> [(Var, a)] ->  m (Env a)
  -- default implementation
  updateEnv ρ bs = return $ ρ // bs
 
  alloc :: Var -> m a
  tick :: PΣ a -> m ()

  -- stepAnalysis :: s -> g -> PΣ a -> (s, [(PΣ a, g)])
  -- inject :: CExp -> (PΣ a, s, g)

----------------------------------------------------------------------  
-- Generic transition
----------------------------------------------------------------------  
mnext :: (Analysis m a, GarbageCollector m (PΣ a)) => PΣ a -> m (PΣ a)
mnext ps@(Call f aes, ρ) = do  
  Clo (vs :=> call', ρ') <- fun ρ f
  tick ps
  as  <- mapM alloc vs
  ds  <- mapM (arg ρ) aes 
  ρ'' <- updateEnv ρ' [ v ==> a | v <- vs | a <- as ]
  sequence [ a $= d | a <- as | d <- ds ]
  let sn = (call', ρ'')
  gc sn
  return $! sn
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

----------------------------------------------------------------------
 -- GC Machinery
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
adjacent :: (Ord a, StoreLike a s (D a)) => (Var, a) -> s -> Set (Var, a)
adjacent (v, addr) σ = Set.fromList [b | Clo (f, ρ) <- Set.toList(fetch σ addr),
                                         b <- Set.toList (touched' (Lam f) ρ)]

-- `reachability'
reachable :: (Ord a, StoreLike a s (D a)) => (PΣ a) -> s -> Set (Var, a)
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
 -- Anodization
----------------------------------------------------------------------

class StoreLike a s d => AlkaliLike a s d where
  addUniqueAddr  :: a -> s
  deAnodizeStore :: s -> s 
  deAnodizeEnv   :: s -> Env a -> Env a
  deAnodizeD     :: s -> d -> d
  reset          :: s -> s

-- a useful instance
instance (Ord a, StoreLike a s d) => StoreLike a (s, ℙ a) d where 
 σ0 = (σ0, Set.empty)
 bind σ a d = (bind (fst σ) a d, snd σ)
 fetch σ a = fetch (fst σ) a 
 replace σ a d = (replace (fst σ) a d, snd σ)
 filterStore σ p = (filterStore (fst σ) p, snd σ)

-- TODO: implement!
