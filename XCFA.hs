module Main where

 -- Imports.
import CPS
import Data.Map as Map
import Data.Set as Set

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
class Monad m => Analysis a m where
  fun :: (Env a)-> AExp -> m (Val a)
  arg :: (Env a)-> AExp -> m (D a)

  ($=) :: a -> (D a) -> m ()
 
  alloc :: Var -> m a
  tick :: (PΣ a) -> m ()


 -- 


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
  

data GenericAnalysis a t s b = GCFA {
  gf :: (ProcCh a,s,t) -> [(b,ProcCh a,s,t)]
}

instance Monad (GenericAnalysis a t s) where
  (>>=) (GCFA f) g = GCFA (\ (ch,σ,t) ->
    concatMap (\ (a,ch,σ',t') -> (gf $ g(a))(ch,σ',t')) (f(ch,σ,t)))
  return a = GCFA (\ (ch,σ,t) -> [(a,ch,σ,t)])


instance (Addressable a t, Storable a s) 
   => Analysis a (GenericAnalysis a t s) where
  fun ρ (Lam l) = GCFA (\ (_,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (proc,Just proc,σ,t) ])
  fun ρ (Ref v) = GCFA (\ (_,σ,t) -> 
    let procs = fetch σ (ρ!v)
     in [ (proc,Just proc,σ,t) | proc <- Set.toList procs ]) 

  arg ρ (Lam l) = GCFA (\ (ch,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (Set.singleton proc, ch, σ, t) ])
  arg ρ (Ref v) = GCFA (\ (ch,σ,t) -> 
    let procs = fetch σ (ρ!v)
     in [ (procs, ch, σ, t) ])

  a $= d = GCFA (\ (ch,σ,t) -> [((),ch,bind σ a d,t)] )

  alloc v = GCFA (\ (ch,σ,t) -> [(valloc v t, ch, σ, t)])

  tick ps = GCFA (\ (Just proc, σ, t) ->
     [((), Just proc, σ, advance proc ps t)])



 -- Generic transition
mnext :: (Analysis a m) => (PΣ a)-> m (PΣ a)
mnext ps@(Call f aes, ρ) = do  
  proc@(Clo (vs :=> call', ρ')) <- fun ρ f
  tick ps
  as <- mapM alloc vs
  ds <- mapM (arg ρ) aes 
  let ρ'' = ρ' // [ v ==> a | v <- vs | a <- as ]
  sequence [ a $= d | a <- as | d <- ds ]
  return $! (call', ρ'')


 -- Abstract state-space exploration algorithm
explore :: 
  (Analysis a m, Addressable a t, Storable a s) 
  => CExp -> ((PΣ a)-> m (PΣ a)) -> [(PΣ a,s,t)]
explore call =
 let
  pς0 = (call, ρ0)

  visited :: Set.Set (PΣ a, s, t)
  visited = Set.empty
 in error "foo"



 -- Example: Concrete Semantics

data Concrete a b = 
 Concrete { cf :: (Store a,Int) -> (b,Store a,Int) }

data CAddr = CBind Var Int
  deriving (Eq,Ord)


instance Monad (Concrete CAddr) where
  (>>=) (Concrete f) g = Concrete (\ (σ,t) ->
    let (a, σ', t') = f(σ,t)
     in (cf $ g(a))(σ',t'))
  return a = Concrete (\ (σ,t) -> (a,σ,t))


instance Analysis CAddr (Concrete CAddr) where
  fun ρ (Lam l) = Concrete (\ (σ,t) -> 
    let proc = Clo(l, ρ)
     in (proc,σ,t))
  fun ρ (Ref v) = Concrete (\ (σ,t) -> 
    let [proc] = Set.toList $ σ!(ρ!v)
     in (proc,σ,t))

  arg ρ (Lam l) = Concrete (\ (σ,t) ->
    let proc = Clo(l, ρ) 
     in (Set.singleton proc, σ, t))
  arg ρ (Ref v) = Concrete (\ (σ,t) -> 
    let procs = σ!(ρ!v)
     in (procs, σ, t))

  a $= d = Concrete (\ (σ,t) -> ((),σ ⨆ [a ==> d],t) )

  alloc v = Concrete (\ (σ,t) -> (CBind v t, σ, t))

  tick (call, ρ) = Concrete (\ (σ,n) -> ((), σ, n+1))





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


mnext_KCFA :: (PΣ KAddr) ->
 (GenericAnalysis KAddr KTime (Store KAddr)) (PΣ KAddr)
mnext_KCFA = mnext 




main :: IO ()
main = do
       return ()
       

