{-# LANGUAGE OverloadedStrings #-}
module TypePlay.Check.PolyMorph where

import Prelude hiding (map,foldl,elem)
import Data.List (map,foldl,(\\),union,elem)

import TypePlay.Types

import Control.Monad (when,liftM)

import Data.Monoid ((<>))

initialEnv :: Env
initialEnv = Env []

extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env ((s,t) : r)

findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
  case lookup s r of
   Just t -> Right t
   Nothing -> Left $ "Cannot find variable " <> s

tCheck :: Env -> Expr -> TC Type
tCheck r (Var s) = findVar r s
tCheck r (App f a) = do
  tf <- tCheckRed r f
  case tf of
   Pi x at rt -> do
     ta <- tCheck r a
     when (not (betaEq ta at)) $ Left "Bad function argument type"
     Right $ subst x a rt
   _ -> Left "Non-function in application"
tCheck r (Lam s t e) = do
  _ <- tCheck r t
  let r' = extend s t r
  te <- tCheck r' e
  let lt = Pi s t te
  _ <- tCheck r lt
  return lt
tCheck r (Pi x a b) = do
  s <- tCheckRed r a
  let r' = extend x a r
  t <- tCheckRed r' b
  when ((s,t) `notElem` allowedKinds) $ Left "Bad abstraction"
  Right t
tCheck _ (Kind Star) = Right $ Kind Box
tCheck _ (Kind Box) = Left "Found a box"

tCheckRed :: Env -> Expr -> TC Type
tCheckRed r e = liftM whnf (tCheck r e)

typeCheckExpr :: Expr -> TC Type
typeCheckExpr = tCheck initialEnv

typeCheckWithEnv :: Env -> Expr -> TC Type
typeCheckWithEnv ev ex = tCheck ev ex

allowedKinds :: [(Type, Type)]
allowedKinds =
  [(Kind Star, Kind Star)
  ,(Kind Star, Kind Box)
  ,(Kind Box, Kind Star)
  ,(Kind Box, Kind Box)]

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
    spine (Lam s _ e) (a:as) = spine (subst s a e) as
    spine f as = foldl App f as

-- Free variables are those that occur in an Expr, but are not bound
-- within that Expr. Collect them in a list.

freeVars :: Expr -> [Sym]
freeVars (Var s)     = [s]
freeVars (App f a)   = freeVars f `union` freeVars a
freeVars (Lam i t e) = freeVars t `union` (freeVars e \\ [i])
freeVars (Pi i k t)  = freeVars k `union` (freeVars t \\ [i])
freeVars (Kind _)    = []

-- Now for substitution
-- subst b[v:=x]
subst :: Sym -> Expr -> Expr -> Expr
subst v x = sub
  where
    sub e@(Var i) = if i == v then x else e
    sub (App f a) = App (sub f) (sub a)
    sub (Lam i t e) = abstr Lam i t e
    sub (Pi i t e) = abstr Pi i t e
    sub (Kind k) = Kind k
    fvx = freeVars x
    cloneSym e i = loop i
      where
        loop i' = if i' `elem` vars then loop (i <> "'") else i'
        vars = fvx <> freeVars e
    abstr con i t e =
      if v == i then con i (sub t) e
      else if i `elem` fvx then
             let
               i' = cloneSym e i
               e' = substVar i i' e
             in con i' (sub t) (sub e')
           else
             con i (sub t) (sub e)

substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' e = subst s (Var s') e

-- For comparing Exprs without alpha-conversions
alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v) (Var v')           = v == v'
alphaEq (App f a) (App f' a')      = alphaEq f f' && alphaEq a a'
alphaEq (Lam i t e) (Lam i' t' e') = alphaEq e (substVar i' i e') && alphaEq t t'
alphaEq (Pi i t e) (Pi i' t' e')   = alphaEq e (substVar i' i e') && alphaEq t t'
alphaEq (Kind k) (Kind k')         = k == k'
alphaEq _               _          = False

-- Reduction to Normal Form (where no redexes remain)
nf :: Expr -> Expr
nf ee = spine ee []
  where
    spine (App f a) as = spine f (a:as)
    spine (Lam s t e) [] = Lam s (nf t) (nf e)
    spine (Lam s _ e) (a:as) = spine (subst s a e) as
    spine (Pi s k t) as = app (Pi s (nf k) (nf t)) as
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
