{-# LANGUAGE OverloadedStrings #-}
module TypePlay.Check.SimplyTyped where

import Prelude hiding (map,foldl,elem)
import Data.List (map,foldl,(\\),union,elem)

import Data.Text (Text)
import qualified Data.Text as T

import Control.Monad (when)
import Control.Monad.Trans.Error (throwError)
import Data.Monoid ((<>))

type Sym = Text

data Expr
  = Var Sym
  | App Expr Expr
  | Lam Sym Type Expr
  deriving (Eq, Read, Show)
  
-- Simple Typing (t -> t B)
data Type
	= Base
	| Arrow Type Type
	deriving (Eq, Read, Show)

-- x e e \x:t.e 

-- Type checker will take an expression and return the type.
-- The TC will also need the types of all free vars in the expr.

-- Representing the environment is a list of vars and their respective types.
newtype Env = Env [(Sym, Type)] deriving (Show)

initialEnv :: Env
initialEnv = Env []

extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env ((s,t) : r)

-- Type checking will be written using a monadic style
-- so we can have some error handling funnies.
type ErrorMsg = Text

type TC a = Either ErrorMsg a

findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
	case lookup s r of
		Just t -> return t
		Nothing -> throwError $ "Cannot find variable " <> s
		
tCheck :: Env -> Expr -> TC Type
tCheck r (Var s) =
	findVar r s
tCheck r (App f a) = do
	tf <- tCheck r f
	case tf of
		Arrow at rt -> do
			ta <- tCheck r a
			when (ta /= at) $ throwError "Bad function argument type"
			return rt
		_ -> throwError "Non-function in application"
tCheck r (Lam s t e) = do
	let r' = extend s t r
	te <- tCheck r' e
	return $ Arrow t te

typeCheck :: Expr -> Type
typeCheck e =
	case tCheck initialEnv e of
		Left msg -> error ("Type error:\n" <> msg)
		Right t -> t


-- (\x. \y.x)(\z.z)
-- App (Lam "x" $ Lam "y" $ Var "x") (Lam "z" $ Var "z")

-- In beta reduction, on the lambda form is a redex.
-- (\x.e)a reduces to e[x:=a]
-- This means that all (free) occurrences of 'x' in 'e' become 'a'

-- alpha-substitution, which is simply renaming a bound variable. 
-- \x.x can be changed to \y.y

-- Start with normal order to WHNF. Weak Head Normal Form.
-- In WHNF - ensure there is no redex along the "spine" of the expr.

-- Starting from the root and following the left branch in applications.
-- Walk down the spine collecting arguments (right branch of App) until
-- we reach a lambda or a variable.
-- If we reach a variable we have WHNF so reconsititute the App again.
-- If we reach a lambda we get to the crux of evaluation
	-- We need a Beta-reduction
		-- for App (Lam v e) a then v[e:=a] 
		-- we use the `subst` function for this
		
whnf :: Expr -> Expr
whnf ee = spine ee []
	where 
		spine (App f a) as = spine f (a:as)
		spine (Lam s e) (a:as) = spine (subst s a e) as
		spine f as = foldl App f as

-- Free variables are those that occur in an Expr, but are not bound
-- within that Expr. Collect them in a list.

freeVars :: Expr -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a) = freeVars f `union` freeVars a
freeVars (Lam i e) = freeVars e \\ [i]

-- Now for substitution
-- subst b[v:=x]
subst :: Sym -> Expr -> Expr -> Expr
subst v x b = sub b
	where 
		sub e@(Var i) = if i == v then x else e
		sub (App f a) = App (sub f) (sub a)
              	sub (Lam i e) =
                		if v == i then Lam i e
                		else if i `elem` fvx then
                        		let
                        			i' = cloneSym e i
                        			e' = substVar i i' e
                         		in Lam i' (sub e')
                		else Lam i (sub e)
              	fvx = freeVars x
              	cloneSym e i = loop i
              		where 
              			loop i' = if i' `elem` vars then loop (i <> "'") else i'
              	            	vars = fvx <> freeVars e
              	           
substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' e = subst s (Var s') e

-- For comparing Exprs without alpha-conversions
alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v') = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s e) (Lam s' e') = alphaEq e (substVar s' s e')
alphaEq _               _                = False

-- Reduction to Normal Form (where no redexes remain)
nf :: Expr -> Expr
nf ee = spine ee []
	where
		spine (App f a) as = spine f (a:as)
		spine (Lam s e) [] = Lam s (nf e)
		spine (Lam s e) (a:as) = spine (subst s a e) as
		spine f as = app f as
		
		app f as = foldl App f (map nf as)
		
betaEq :: Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

-- Testing !
--[z,s,m,n] = map (Var . (:[])) "zsmn"
--app2 f x y = App (App f x) y
--zero  = Lam "s" $ Lam "z" z
--one   = Lam "s" $ Lam "z" $ App s z
--two   = Lam "s" $ Lam "z" $ App s $ App s z
--three = Lam "s" $ Lam "z" $ App s $ App s $ App s z
--plus  = Lam "m" $ Lam "n" $ Lam "s" $ Lam "z" $ app2 m s (app2 n s z)