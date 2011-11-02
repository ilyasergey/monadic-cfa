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
type Σ = (CExp, Env, Store, Time)
type Env = Var :-> Addr
type Store = Addr :-> D
type D = ℙ Val
data Val = Clo (Lambda, Env)
  deriving (Eq,Ord)
type Addr = (Var,Time)
type Time = [CExp]


 -- Helpers.
arg :: (AExp, Env, Store) -> D
arg (Ref v, ρ, σ) = σ!(ρ!v)
arg (Lam l, ρ, σ) = Set.singleton (Clo (l, ρ))


 -- k-CFA-style allocation.
k = 1

tick_Call :: (Val,Σ) -> Time
tick_Call (_,(call,_,_,t)) = take k (call:t)

alloc_Call :: (Var, Time, Val, Σ) -> Addr
alloc_Call (v, t', proc, ς) = (v,t')

 -- Transition.
next :: Σ -> [Σ]
next ς@(Call f aes, ρ, σ, t) = [ (call, ρ'', σ', t') |
    proc@(Clo (vs :=> call, ρ')) <- Set.toList (arg (f, ρ, σ)),
    let t'  = tick_Call (proc, ς),
    let as  = [ alloc_Call(v, t', proc, ς) | v <- vs],
    let ds  = [ arg(ae, ρ, σ) | ae <- aes ],
    let ρ'' = ρ' // [ v ==> a | v <- vs | a <- as ],
    let σ'  = σ  ⨆  [ a ==> d | a <- as | d <- ds ] ]


main :: IO ()
main = do
       return ()

