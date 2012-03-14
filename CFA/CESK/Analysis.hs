{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}

module CFA.CESK.Analysis where

-- Imports.
import Data.Map as Map
import Data.Set as Set

import CFA.Lattice
import CFA.Store

{---------------- SYNTAX AND STATE-SPACE ----------------}

-- `a' stands for the nature of addresses
-- it is also a leaf of the state-space

type Var = String
type Lab = String
type Env a = Var :-> a
type Lambda = (Var, Exp)
type State a = (Exp, Env a, a)

data Exp = Ref (Var, Lab)
         | App (Exp, Exp, Lab)
         | Lam (Lambda, Lab)
  deriving (Eq, Ord, Show)

-- retrieve a label
lab :: Exp -> Lab
lab (Ref (_, l)) = l
lab (App (_, _, l)) = l
lab (Lam (_, l)) = l

data Clo a = Clo (Lambda, Env a, Lab)
  deriving (Eq, Ord)

data Kont a = Mt
            | Ar (Exp, Env a, a)
            | Fn (Lambda, Env a, a)
  deriving (Eq, Ord)

class (Eq a, Ord a) => Address a

class (Address a, Monad m) => Analysis m a where
  tick      :: State a -> m ()
  getVar    :: Env a -> Var -> m  (Clo a)
  putVar    :: Env a -> Var -> Clo a -> m (Env a)
  loadCont  :: a -> m (Kont a)
  storeCont :: Kont a -> m a

-- A small-step monadic semantics for CESK* machine
-- in Store- and Time- passing style

-- The underlying monad implemens a `time-state-store-passing style'
-- in order to disguise `alloc' calls, which use both time and state
-- (at least, in the abstract case)

{------------------ MONADIC SEMANTICS --------------------}

mstep :: (Analysis m a) => State a -> m (State a)
mstep ctx@(Ref (x, l), ρ, a) = do
  tick ctx
  Clo (v, ρ', l) <- getVar ρ x
  return $! (Lam (v, l), ρ', a)
mstep ctx@(App (e0, e1, l), ρ, a) = do
  tick ctx
  b <- storeCont (Ar (e1, ρ, a))
  return (e0, ρ, b)
mstep ctx@(Lam (v, l), ρ, a) = do
  tick ctx
  κ <- loadCont a
  case κ of
    Ar (e, ρ, a) -> do
      b <- storeCont κ
      return (e, ρ, b)
    Fn ((x, e), ρ', c) -> do
      ρ'' <- putVar ρ' x (Clo (v, ρ, l))
      return (e, ρ'', c)

{----------------- TIME-STAMPED ADDRESSES ------------------}

data Addr = Bind Var [Lab]
          | Call Lab [Lab]
  deriving (Eq, Ord, Show)

data Time = TLab Lab [Lab]
          | TMt [Lab]
  deriving (Eq, Ord, Show)

contour :: Time -> [Lab]
contour (TLab _ c) = c
contour (TMt c) = c

instance Address Addr
    
{---------------- CONCRETE INTERPRETATION ----------------}

data D = Val (Clo Addr)
       | Cont (Kont Addr)
  deriving (Eq, Ord)

type Store = Addr :-> D

data CESKx a = CESKx { 
  st :: !((Time, State Addr, Store) -> (a, Time, State Addr, Store)) 
}

instance Monad CESKx where
   return a = CESKx (\(t, s, σ) -> (a, t, s, σ)) 
   (>>=) (CESKx f) g = CESKx (\(t, s, σ) -> 
           let result = f (t, s, σ)
            in (\(a, t', s', σ') -> (st $ g(a))(t', s', σ')) result)

instance Analysis CESKx Addr where
  tick ctx@(Ref (_, _), ρ, a) = CESKx (\(t, s, σ) -> ((), t, ctx, σ))
  tick ctx@(App (_, _, l), ρ, a) = CESKx (\(t, s, σ) -> ((), TLab l (contour t), ctx, σ))
  tick ctx@(v, ρ, a) = CESKx (\(TLab l ctr, s, σ) -> 
                       let (Cont κ) = σ ! a
                        in case κ of 
                           Ar _ -> ((), TLab l ctr, ctx, σ)
                           Fn _ -> ((), TMt (l:ctr), ctx, σ))

  getVar ρ x = CESKx (\(t, s, σ) -> 
                 let (Val clo) = σ ! (ρ ! x)
                  in (clo, t, s, σ))

  putVar ρ x c = CESKx (\(t, s, σ) -> 
                 let b  = alloc t s σ
                     σ' = σ // [(b, Val c)]
                  in (ρ // [(x, b)], t, s, σ'))

  loadCont a  = CESKx (\(t, s, σ) -> 
                 let (Cont κ) = σ ! a
                  in (κ, t, s, σ))

  storeCont κ = CESKx (\(t, s, σ) -> 
                 let b  = alloc t s σ
                     σ' = σ // [(b, Cont κ)]
                  in (b, t, s, σ'))
  


-- Concrete allocator function
-- Turns the last captured time moment into the address
alloc :: Time -> State Addr -> Store -> Addr
alloc t (App (e0, _, _), _ ,_) σ = Call (lab e0) (contour t)
alloc t (Lam _, _, a) σ = 
      case σ ! a of
        Cont (Ar (e, _, _))      -> Call (lab e) (contour t)
        Cont (Fn ((x, _), _, _)) -> Bind x (contour t)

{---------------- ABSTRACT INTERPRETATION ----------------}

data KCFA a = KCFA { kf :: !((Time, State Addr, AStore) -> [(a, Time, State Addr, AStore)]) }

--TODO is it possible to abstract over the list structure?
type D1 = (ℙ D)

type AStore = Addr :-> D1

k = 1

instance Monad KCFA where
   return a = KCFA (\(t, s, σ) -> [(a, t, s, σ)]) 
   (>>=) (KCFA f) g = KCFA (\ (t, s, σ) ->
     let chs = f(t, s, σ)
      in concatMap (\ (a, t', s', σ') -> (kf $ g(a))(t', s', σ')) chs)

instance Analysis KCFA Addr where
  tick ctx@(Ref (_, _), ρ, a) = KCFA (\(t, s, σ) -> [((), t, ctx, σ)])
  tick ctx@(App (_, _, l), ρ, a) = KCFA (\(t, s, σ) -> [((), TLab l (contour t), ctx, σ)])
  tick ctx@(v, ρ, a) = KCFA (\(TLab l ctr, s, σ) -> 
                       [case κ of 
                           Ar _ -> ((), TLab l ctr, ctx, σ)
                           Fn _ -> ((), TMt (take k (l : ctr)), ctx, σ) 
                        | Cont κ <- Set.toList (σ ! a)])

  getVar ρ x   = KCFA (\(t, s, σ) -> 
                  let clos = σ ! (ρ ! x)
                   in [(clo, t, s, σ) | Val clo <- Set.toList clos])

  putVar ρ x c = KCFA (\(t, s, σ) -> do
                  b <- allocKCFA t s σ
                  let d  = (Set.singleton (Val c))
                      σ' = σ ⊎ [b ==> d]
                      ρ' = ρ // [(x, b)]
                  return (ρ', t, s, σ'))

  loadCont a   = KCFA (\(t, s, σ) -> 
                  let ks = σ ! a
                   in [(κ, t, s, σ) | Cont κ <- Set.toList ks])

  storeCont κ  = KCFA (\(t, s, σ) -> do
                  b <- allocKCFA t s σ
                  let d  = (Set.singleton (Cont κ))
                      σ' = σ ⊎ [b ==> d]
                  return (b, t, s, σ'))

-- abstract allocator function
-- similar to the concrete allocator
-- nondeterministic because of stored continuations
allocKCFA :: Time -> State Addr -> AStore -> [Addr]
allocKCFA t (App (e0, _, _), _ ,_) σ = [Call (lab e0) (contour t)]
allocKCFA t (Lam _, _, a) σ = 
      [case κ of
            Ar (e, _, _)      -> Call (lab e) (contour t)
            Fn ((x, _), _, _) -> Bind x (contour t) 
       | Cont κ <- Set.toList (σ ! a)]


{-------------------------- EXAMPLE -------------------------}

-- provide the initial state
-- State = (Exp, Env, Addr)
state0 = (Lam (("x", Ref ("x", "l2")), "l1"), Map.empty, Call "l3" [])

-- define the denotational semantics of the first step
-- literally, mstep - is a denotational semantics, induced by the 
-- abstract machine over time and store
transition = mstep state0 :: KCFA (State Addr)

-- run analysis with the suplied time and store
result = kf transition (TMt [], undefined, Map.empty)