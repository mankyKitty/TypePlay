module TypePlay.Types
  ( Type
  , Expr(..)
  , Kinds(..)
  , Env(..)
  , Sym
  , ErrorMsg
  , TC
  ) where

import Data.Text (Text)

type Sym = Text

data Expr
  = Var Sym
  | App Expr Expr
  | Lam Sym Type Expr
  | Pi Sym Type Type
  | Kind Kinds
  deriving (Eq, Read, Show)

type Type = Expr

data Kinds
  = Star
  | Box
  deriving (Eq, Read, Show)

-- x e( e \x:t.e 

-- Type checker will take an expression and return the type.
-- The TC will also need the types of all free vars in the expr.

-- Representing the environment is a list of vars and their respective types.
newtype Env = Env [(Sym, Type)] deriving (Show)

-- Type checking will be written using a monadic style
-- so we can have some error handling funnies.
type ErrorMsg = Text

type TC a = Either ErrorMsg a
