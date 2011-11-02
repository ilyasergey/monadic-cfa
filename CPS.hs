module CPS where

-- Syntax.
type Var = String

data Lambda = [Var] :=> CExp
  deriving (Ord,Eq)

data AExp = Ref Var
          | Lam Lambda
  deriving (Ord,Eq)

data CExp = Call AExp [AExp]
          | Exit
  deriving (Ord,Eq)

