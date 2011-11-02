module Main where
-- Should be run with the followinf options:
-- -XTypeOperators -XParallelListComp -XTypeSynonymInstances 
-- -XMultiParamTypeClasses -XScopedTypeVariables -XImplicitParams
-- -XTupleSections

-- Imports.
import Data.Map as Map hiding (map)
import Data.Set as Set hiding (map)
import qualified Data.List as L

-- Abbreviations.
type k :-> v = Map.Map k v
type ℙ a = Set.Set a

(==>) :: a -> b -> (a,b)
(==>) x y = (x,y)

(//) :: Ord k => (k :-> v) -> [(k,v)] -> (k :-> v)
(//) f [] = f
(//) f ((x,y):tl) = Map.insert x y (f // tl)


{--------------------- DOMAIN THEORY ---------------------}

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

(⊎) :: (Ord k, Lattice v) => (k :-> v) -> [(k,v)] -> (k :-> v)
f ⊎ [] = f
f ⊎ ((k,v):tl) = Map.insertWith (⊔) k v (f ⊎ tl)

(!!) :: (Ord k, Lattice v) => (k :-> v) -> k -> v
f !! k = Map.findWithDefault bot k f


{---------------- SYNTAX  ----------------}

-- `a' stands for the nature of addresses
-- it is also a leaf of the state-space

type Var = String
type FieldName = Var
type ClassName = String
type MethodName = String
type Lab = String

type Class = (ClassName, Maybe ClassName, [(ClassName, FieldName)],
                        Konstr, [Method])

type Konstr = (ClassName, [(ClassName, Var)], [Var], [(FieldName, Var)])

type Method = (ClassName, MethodName, [(ClassName, Var)],
                          [(ClassName, Var)], [Stmt])

data Stmt = Asgn Var Var Lab
          | Lkp Var Var FieldName Lab
          | MCall Var Var MethodName [Var] Lab
          | New Var ClassName [Var] Lab
          | Cast Var ClassName Var Lab
          | Ret Var Lab
          deriving (Eq,Ord)

data ClassTable = CTable [Class]

{---------------- HELPERS ----------------}                 

-- retrieve labels
lab :: Stmt -> Lab
lab (Asgn _ _ l) = l
lab (Lkp _ _ _ l) = l
lab (MCall _ _ _ _ l) = l
lab (New _ _ _ l) = l
lab (Cast _ _ _ l) = l
lab (Ret _ l) = l

-- get class name
name :: Class -> ClassName
name (cn, _, _, _, _) = cn

super :: Class -> Maybe ClassName
super (_, cn, _, _, _) = cn

-- findClass
findClass :: ClassTable -> ClassName -> Maybe Class
findClass (CTable classes) cn = L.find (\c -> (name c) == cn) classes

-- returns ALL fields for the given class name (including super's)
allFields :: ClassTable -> ClassName -> [FieldName]
allFields table cn = maybe [] (\clz@(_, _, pairs, _, _) -> 
                      let properFields = L.map snd pairs
                       in case (super clz) of
                          Just superName -> properFields ++ (allFields table superName)
                          Nothing        -> properFields) 
                        (findClass table cn)

-- transitive method lookup
method :: ClassTable -> ClassName -> MethodName -> Method
method table cn m = 
  case findClass table cn of
       Just clz@(_, _, _, _, methods) -> 
            case L.find (\(_, mname, _, _, _) -> mname == m) methods of
                 Just mtd  -> mtd
                 Nothing -> maybe undefined (\sup -> method table sup m) (super clz) 
       Nothing -> undefined

-- find class constructors
konstr :: Class -> Konstr
konstr (_, _, _, k, _) = k

-- get the list of field mappings by a chain of constructors for a given class
classFieldMappings :: ClassTable -> ClassName -> [a] -> [(FieldName, a)]
classFieldMappings table cn values = 
                   maybe [] (\clz -> fieldMappings table (konstr clz) values) 
                         (findClass table cn)

fieldMappings :: ClassTable -> Konstr -> [a] -> [(FieldName, a)]
fieldMappings table (cn, params, superBindings, thisBindings) values =
     let paramBindings = Map.empty // (zip (map snd params) values)
         thisMappings = map (\(f, v) -> (f, paramBindings ! v)) thisBindings
         superArgs = map (\v -> paramBindings ! v) superBindings
      in case (superArgs, 
              (findClass table cn) >>= (return . konstr)) of
              (h:t, Just superKonstr) -> 
                     thisMappings ++ (fieldMappings table superKonstr superArgs)
              _   -> thisMappings


{---------------- STATE-SPACE ----------------}                 

-- a - for addresses

type BEnv a = Var :-> a
type Kont a = (Var, [Stmt], BEnv a, a)
type State a = ([Stmt], BEnv a, a)
type Obj a = (ClassName, BEnv a)

class (Eq a, Ord a) => Address a

{----------------- MONADIC SEMANTICS ------------------}

-- Hint: Add new primitives as they appear in the semantics
class (Address a, Monad m) => JavaSemanticInterface m a where
  tick           :: State a -> m ()
  getObj         :: BEnv a -> Var -> m (Obj a)
  putObj         :: BEnv a -> Var -> Obj a -> m ()
  getCont        :: a -> m (Kont a)
  putCont        :: MethodName -> (Kont a) -> m a
  getC           :: (?table :: ClassTable) => ClassName -> m ([Obj a] -> m (BEnv a))
  getM           :: (?table :: ClassTable) => Obj a -> MethodName -> m Method
  initBEnv       :: BEnv a -> [Var] -> [Var] -> m (BEnv a)

 
mstep :: (JavaSemanticInterface m a, ?table :: ClassTable) => State a -> m (State a)
mstep ctx@((Asgn v v' l):succ, β, pk) = do
      tick ctx
      d <- getObj β v'
      putObj β v d
      return $! (succ, β, pk) 
mstep ctx@((Ret v l):[], β, pk) = do
      tick ctx
      (v', s, β', pk') <- getCont pk
      d <- getObj β v
      putObj β' v' d
      return $! (s, β', pk')
mstep ctx@((Lkp v v' f l):succ, β, pk) = do
      tick ctx
      (c, β') <- getObj β v'
      d <- getObj β' f
      putObj β v d
      return $! (succ, β, pk)
mstep ctx@((Cast v cn v' l):succ, β, pk) = do
      tick ctx
      d <- getObj β v'
      putObj β v d
      return $! (succ, β, pk) 
mstep ctx@((New v cn vs l):succ, β, pk) = do
      tick ctx
      ructor <- getC cn
      ds <- sequence [getObj β vi | vi <- vs]    
      β' <- ructor ds
      let d' = (cn, β')
      putObj β v d'
      return $! (succ, β, pk)     
mstep ctx@((MCall v v0 m vs l):succ, β, pk) = do
      tick ctx      
      d0 <- getObj β v0
      (cn, _ , params, locals, body) <- getM d0 m
      ds <- sequence [getObj β vi | vi <- vs]    
      let κ = (v, succ, β, pk)
      pk' <- putCont m κ
      let vs'' = map snd params
      let vs''' = map snd locals
      let β' = Map.empty // ["this" ==> (β ! v0)]
      β'' <- initBEnv β' vs'' vs'''
      sequence [putObj β'' vi di | vi <- vs'' | di <- ds]
      return $! (body, β'', pk')     
      
{----------------- TIME-STAMPED ADDRESSES ------------------}

data Addr = AVar Var [Lab]
          | ACall MethodName [Lab]
  deriving (Eq, Ord, Show)

type Time = [Lab]

instance Address Addr


{---------------- CONCRETE INTERPRETATION ----------------}

data D = Val (Obj Addr)
       | Cont (Kont Addr)
  deriving (Eq, Ord)

-- TODO: implement the concrete interpreter

{---------------- ABSTRACT INTERPRETATION ----------------}

-- Used EXACTLY the same monad as for KCFA in Lambda

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

instance JavaSemanticInterface KCFA Addr where
  tick ctx@(stmts, _, _) = KCFA (\(t, s, σ) -> [((), take k ((lab (head stmts)):t), ctx, σ)])
  
  getObj β v = KCFA (\(t, s, σ) -> 
               [(d, t, s, σ) | Val d <- Set.toList $ σ!(β!v)])

  putObj β v d = KCFA (\(t, s, σ) -> 
                 [((), t, s, σ ⊎ [(β!v) ==> (Set.singleton (Val d))])])

  getCont pk = KCFA (\(t, s, σ) -> 
               [(κ, t, s, σ) | Cont κ <- Set.toList $ σ ! pk])

  putCont m κ = KCFA (\(t, s, σ) -> 
                let b = alloc_k t m in
                [(b, t, s, σ ⊎ [b ==> (Set.singleton (Cont κ))])])

  initBEnv β vs'' vs''' = KCFA (\(t, s, σ) -> 
                           let pairs' = map (\v -> (v, alloc t v)) vs''
                               pairs'' = map (\v -> (v, alloc t v)) vs''' in
                           let β' = β // pairs' // pairs'' in
                           [(β', t, s, σ)])

  getC cn  = KCFA (\(t, s, σ) ->  
             -- updates a store and returns an environment of all class fields
             let ructor = (\ds -> KCFA(\(t', s', σ') -> 
                   let fs = allFields ?table cn -- compute all fields
                       as = map (alloc t) fs    -- appropriate addresses for fields
                       fBindings = zip fs as    -- bindings [field |-> addr]
                       -- mapping from all class fields to provided arguments
                       fMappings = Map.empty // classFieldMappings ?table cn ds 
                       -- heap is updated according to the mappings
                       σ'' = σ' ⊎ [ai ==> (Set.singleton (Val $ fMappings ! fi)) | (fi, ai) <- fBindings]
                       -- new environment is create
                       β' = Map.empty // fBindings
                    in [(β', t', s', σ'')]))
             in [(ructor, t, s, σ)])

  getM (cn, _) m = KCFA (\(t, s, σ) -> [(method ?table cn m, t, s, σ)])

alloc :: Time -> Var -> Addr
alloc t v = AVar v (take k t)

alloc_k :: Time -> MethodName -> Addr
alloc_k t m = ACall m (take k t)
