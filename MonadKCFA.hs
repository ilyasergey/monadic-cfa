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
data Σ = Ctx Store
  deriving (Eq,Ord)
type Ctx = (CExp, Env, Time)
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
  funEval :: Env -> AExp -> m Val
  argEval :: Env -> AExp -> m D

  ($=) :: Addr -> D -> m ()
 
  alloc :: Time -> Var -> m Addr
  tick :: (Ctx,Time) -> m Time

 -- class Monad m where
 --   (>>=) :: m a -> (a -> m b) -> m b
 --   (>>) :: m a -> m b -> m b
 --   return :: a -> m a
 --   fail :: String -> m a



data Exact a = Exact !(Store -> (a,Store))
data KCFA a = KCFA { kf :: !(Store -> [(a,Store)]) }


k = 1

 -- return a >>= k  =  k a
 -- m >>= return  =  m
 -- m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h



instance Monad KCFA where
  (>>=) (KCFA f) g = KCFA (\ σ ->
     let chs = f(σ)
      in concatMap (\ (a, σ') -> (kf $ g(a))(σ')) chs)
  return a = KCFA (\ σ -> [(a,σ)])


instance Analysis KCFA where
  funEval ρ (Lam l) = KCFA (\ σ ->
    let proc = Clo(l, ρ) 
     in [ (proc,σ) ])
  funEval ρ (Ref v) = KCFA (\ σ -> 
    let procs = σ!(ρ!v)
     in [ (proc,σ) | proc <- Set.toList procs ])

  argEval ρ (Lam l) = KCFA (\ σ ->
    let proc = Clo(l, ρ) 
     in [ (Set.singleton proc, σ) ])
  argEval ρ (Ref v) = KCFA (\ σ -> 
    let procs = σ!(ρ!v)
     in [ (procs, σ) ])

  a $= d = KCFA (\ σ -> [((),σ ⨆ [a ==> d])])

  alloc t' v = KCFA (\ σ -> [(Bind v t', σ)])

  tick ((call, ρ, _),CallSeq t) = KCFA (\ σ ->
    [(CallSeq (take k (call:t)), σ)])


mnext :: (Analysis m) => (CExp,Env,Time) -> m (CExp,Env,Time)
mnext ctx@(Call f aes, ρ, t) = do  
  clo@(Clo (vs :=> call', ρ')) <- funEval ρ f
  t' <- tick(ctx,t)  
  as <- mapM (alloc t') vs
  ds <- mapM (argEval ρ) aes 
  let ρ'' = ρ' // [ v ==> a | v <- vs | a <- as ]
  sequence [ a $= d | a <- as | d <- ds ]
  return $! (call', ρ'', t')



main :: IO ()
main = do
       return ()
       

