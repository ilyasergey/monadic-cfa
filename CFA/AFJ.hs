{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

module CFA.AFJ where

import Data.Set as Set
import Data.Map as Map
import Data.List as L

import CFA.Lattice

----------------------------------------------------------------------  
 -- ANF FJ Syntax and gelper functions
----------------------------------------------------------------------  

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
          deriving (Eq, Ord, Show)

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
     let paramBindings = Map.empty // (zip (L.map snd params) values)
         thisMappings = L.map (\(f, v) -> (f, paramBindings Map.! v)) thisBindings
         superArgs = L.map (\v -> paramBindings Map.! v) superBindings
      in case (superArgs, 
              (findClass table cn) >>= (return . konstr)) of
              (h:t, Just superKonstr) -> 
                     thisMappings ++ (fieldMappings table superKonstr superArgs)
              _   -> thisMappings


