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
data Σ = Eval PΣ Store Time
  deriving (Eq,Ord)
type PΣ = (CExp, Env)
type Env = Var :-> Addr
type Store = Addr :-> D
type D = ℙ Val
data Val = Clo (Lambda, Env)
  deriving (Eq,Ord)
data Addr = Bind Var Time
  deriving (Eq,Ord)
data Time = CallSeq [CExp]
  deriving (Eq,Ord)



class Monad m => Analysis m where
  fun :: Env -> AExp -> m Val
  arg :: Env -> AExp -> m D

  ($=) :: Addr -> D -> m ()
 
  alloc :: Var -> m Addr
  tick :: PΣ -> m ()

 -- class Monad m where
 --   (>>=) :: m a -> (a -> m b) -> m b
 --   (>>) :: m a -> m b -> m b
 --   return :: a -> m a
 --   fail :: String -> m a


type ProcCh = Maybe Val

data KCFA a = KCFA { kf :: !((ProcCh,Store,Time) -> [(a,ProcCh,Store,Time)]) }

k = 1

 -- return a >>= k  =  k a
 -- m >>= return  =  m
 -- m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h



instance Monad KCFA where
  (>>=) (KCFA f) g = KCFA (\ (ch,σ,t) ->
    concatMap (\ (a,ch,σ',t') -> (kf $ g(a))(ch,σ',t')) (f(ch,σ,t)))
  return a = KCFA (\ (ch,σ,t) -> [(a,ch,σ,t)])


instance Analysis KCFA where
  fun ρ (Lam l) = KCFA (\ (_,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (proc,Just proc,σ,t) ])
  fun ρ (Ref v) = KCFA (\ (_,σ,t) -> 
    let procs = σ!(ρ!v)
     in [ (proc,Just proc,σ,t) | proc <- Set.toList procs ])

  arg ρ (Lam l) = KCFA (\ (ch,σ,t) ->
    let proc = Clo(l, ρ) 
     in [ (Set.singleton proc, ch, σ, t) ])
  arg ρ (Ref v) = KCFA (\ (ch,σ,t) -> 
    let procs = σ!(ρ!v)
     in [ (procs, ch, σ, t) ])

  a $= d = KCFA (\ (ch,σ,t) -> [((),ch,σ ⨆ [a ==> d],t)] )

  alloc v = KCFA (\ (ch,σ,t) -> [(Bind v t, ch, σ, t)])

  tick (call, ρ) = KCFA (\ (ch,σ,CallSeq t) ->
    [((), ch, σ, CallSeq (take k (call:t)))])


mnext :: (Analysis m) => PΣ -> m PΣ
mnext ps@(Call f aes, ρ) = do  
  proc@(Clo (vs :=> call', ρ')) <- fun ρ f
  tick ps
  as <- mapM alloc vs
  ds <- mapM (arg ρ) aes 
  let ρ'' = ρ' // [ v ==> a | v <- vs | a <- as ]
  sequence [ a $= d | a <- as | d <- ds ]
  return $! (call', ρ'')



main :: IO ()
main = do
       return ()
       

