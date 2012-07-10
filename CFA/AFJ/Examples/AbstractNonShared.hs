{-# LANGUAGE TypeSynonymInstances #-}

module CFA.AFJ.Examples where

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import CFA.Store
import CFA.AFJ
import CFA.AFJ.Analysis
import CFA.Runner

----------------------------------------------------------------------
-- abstract interpreter with a per-state store
----------------------------------------------------------------------

import CFA.AFJ.Analysis.NonShared

----------------------------------------------------------------------
-- example program
----------------------------------------------------------------------

{-

class B {}

class A {
  private final B myB; 
  
  public A(B givenB) {
    this.myB = givenB;
  }
  
  B foo() {
    B tmpB;
    tmpB = this.myB;
    return B;
  }
}

// Main method of the AFJ program

void main () {
  A mainA;
  B mainB;
  B mainB1;
  mainB = new B();
  mainA = new A(mainB);
  mainB1 = mainA.foo();  
}

-}

bClass :: Class
bClass = ("B", Nothing, [], ("B", [], [], []), [])

aClass :: Class
aClass = ("A", Nothing, 
               [("B", "myB")], ("A", [("B", "givenB")], [], [("myB", "givenB")]), 
               [
                 ("B", "foo", [], [("B", "tmpB")], 
                                  [Lkp "tmpB" "this" "myB" "l1", 
                                   Ret "tmpB" "l2"])])

ctable :: ClassTable
ctable = CTable [aClass, bClass]

mainVars  = ["mainA", "mainB", "mainB1"]
mainStmts = [ New "mainB" "B" [] "l3"
            , New "mainA" "A" ["mainB"] "l4"
            , MCall "mainB1" "mainA" "foo" [] "l5"
              ]

----------------------------------------------------------------------

abstractResult :: ClassTable -> [Var] -> [Stmt] -> Set (PState Addr, Time, Store Addr)
abstractResult ct vars stmts = runAnalysis ct (injectToState vars stmts) 

-- Try:
-- abstractResult ctable mainVars mainStmts