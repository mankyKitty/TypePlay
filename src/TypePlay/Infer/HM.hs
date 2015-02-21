{-# LANGUAGE OverloadedStrings,NoImplicitPrelude #-}
module TypePlay.Infer.HM where

import Prelude hiding (map,concat)

import Data.List (map,concat,nub,union,intersect)
import Data.Text (Text)
import qualified Data.Text as T

import Data.Monoid ((<>),mconcat)

type Id = Text

enumId :: Int -> Id
enumId = ("v" <>) . T.pack . show

data Kind
  = Star
  | Kfun Kind Kind
  deriving (Eq,Show)

data Type
  = TVar Tyvar
  | TCon Tycon
  | TAp Type Type
  | TGen Int
  deriving (Eq,Show)

data Tyvar = Tyvar Id Kind
  deriving (Eq,Show)

data Tycon = Tycon Id Kind
  deriving (Eq,Show)

type Subst = [(Tyvar, Type)]

data InferenceErr
  = SubstMerge
  | Unification Type Type
  | DoesNotOccur Tyvar [Tyvar]
  | KindsDontMatch Kind Kind
  | TypesDontMatch Type Type
  | ClassMisMatch Id Id
  | NoSuperClassFound Id
  | NoInstancesOfClass Id

type Infer a = Either InferenceErr a

instance Show InferenceErr where
  show SubstMerge = "Substitution Merge Failed"
  show (Unification t1 t2)
    = "Unable to unify" <> show t1 <> " with " <> show t2
  show (DoesNotOccur tv t)
    = show t <> " not found in " <> show tv
  show (KindsDontMatch k1 k2)
    = mconcat
      [ "Incorrect Kind.\n Found ("
      , show k1
      , ").\nExpected ("
      , show k2
      ]
  show (TypesDontMatch t t')
    = mconcat
      [ "Could not match types:\n"
      , show t
      , " with "
      , show t'
      ]
  show (ClassMisMatch i i')
    = mconcat
      [ "Type Classes differ.\n Found("
      , show i
      , "). Expected ("
      , show i'
      , ")."
      ]
  show (NoSuperClassFound i)
    = mconcat
      [ "No type class matching: "
      , show i
      , " found."
      ]
  show (NoInstancesOfClass i)
    = mconcat
      [ "No instances of "
      , show i
      , " found in current environment."
      ]

typeConst :: Text -> Kind -> Type
typeConst i = TCon . Tycon i

tUnit    = typeConst "()" Star
tChar    = typeConst "Char" Star
tInt     = typeConst "Int" Star
tInteger = typeConst "Integer" Star
tFloat   = typeConst "Float" Star
tDouble  = typeConst "Double" Star

tList   = typeConst "[]" $ Kfun Star Star
tArrow  = typeConst "(->)" $ Kfun Star $ Kfun Star Star
tTuple2 = typeConst "(,)" $ Kfun Star $ Kfun Star Star

tString :: Type
tString = list tChar

infixr 4 `fn`
fn :: Type -> Type -> Type
a `fn` b = TAp (TAp tArrow a) b

list :: Type -> Type
list = TAp tList

pair :: Type -> Type -> Type
pair a b = TAp (TAp tTuple2 a) b

class HasKind t where
  kind :: t -> Kind

instance HasKind Tyvar where
  kind (Tyvar v k) = k
  
instance HasKind Tycon where
  kind (Tycon v k) = k

instance HasKind Type where
  kind (TCon tc) = kind tc
  kind (TVar u) = kind u
  kind (TAp t _) = case kind t of
                     (Kfun _ k) -> k

nullSubst :: Subst
nullSubst = []

(+->) :: Tyvar -> Type -> Subst
u +-> t = [(u,t)]

class Types t where
  apply :: Subst -> t -> t
  tv    :: t -> [Tyvar]

instance Types Type where
  apply s (TVar u) = case lookup u s of
                       Just t -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply s t         = t
  
  tv (TVar u)  = [u]
  tv (TAp l r) = tv l `union` tv r
  tv t         = []

instance Types a => Types [a] where
  apply s = fmap (apply s)
  tv      = nub . concat . fmap tv

infixr 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = [ (u, apply s1 t) | (u,t) <- s2] <> s1

merge :: Subst -> Subst -> Infer Subst
merge s1 s2 = if agree
  then Right $ s1 <> s2
  else Left SubstMerge
  where
    agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v))
                (gFst s1 `intersect` gFst s2)
    gFst = fmap fst

mgu :: Type -> Type -> Infer Subst
mgu (TAp l r) (TAp l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  return $ s2 @@ s1
mgu (TVar u) t            = varBind u t
mgu t (TVar u)            = varBind u t
mgu (TCon tc1) (TCon tc2)
  | tc1 == tc2 = return nullSubst
mgu t1 t2                 = Left $ Unification t1 t2

varBind :: Tyvar -> Type -> Infer Subst
varBind u t
  | t == TVar u      = return nullSubst
  | u `elem` tv t    = Left $ DoesNotOccur u $ tv t
  | kind u /= kind t = Left $ KindsDontMatch (kind u) (kind t)
  | otherwise        = return $ u +-> t

match :: Type -> Type -> Infer Subst
match (TAp l r) (TAp l' r') = do
  sl <- match l l'
  sr <- match r r'
  merge sl sr
match (TVar u) t
  | kind u == kind t = return $ u +-> t
match (TCon tcl) (TCon tcr)
  | tcl == tcr = return nullSubst
match t1 t2 = Left $ TypesDontMatch t1 t2

-- Type Classes
data Qual t = [Pred] :=> t
  deriving (Show,Eq)

data Pred = IsIn Id Type
  deriving (Show,Eq)

-- Example 'Num a => a -> Int'
-- [IsIn "Num" (TVar (Tyvar "a" Star))]
--   :=> (TVar (Tyvar "a" Star) 'fn' tInt)

instance Types t => Types (Qual t) where
  apply s (ps :=> t) = apply s ps :=> apply s t
  tv (ps :=> t)      = tv ps `union` tv t

instance Types Pred where
  apply s (IsIn i t) = IsIn i (apply s t)
  tv (IsIn i t)      = tv t

mguPred :: Pred -> Pred -> Infer Subst
mguPred = lift mgu

matchPred :: Pred -> Pred -> Infer Subst
matchPred = lift match

lift 
  :: (Type -> Type -> Infer b)
  -> Pred
  -> Pred
  -> Infer b
lift m (IsIn i t) (IsIn i' t')
  | i == i' = m t t'
  | otherwise = Left $ ClassMisMatch i i'

type Class = ([Id], [Inst])
type Inst  = Qual Pred

data ClassEnv = ClassEnv
  { classes :: Id -> Maybe Class
  , defaults :: [Type]
  }

super :: ClassEnv -> Id -> Infer [Id]
super ce i = case classes ce i of
               Just (is, its) -> return is
               Nothing -> Left $ NoSuperClassFound i

insts :: ClassEnv -> Id -> Infer [Inst]
insts ce i = case classes ce i of
               Just (is, its) -> return its
               Nothing -> Left $ NoInstancesOfClass i

modify :: ClassEnv -> Id -> Class -> ClassEnv
modify ce i c = ce { classes = \j -> if i == j
  then Just c
  else classes ce j
  }

initialEnv :: ClassEnv
initialEnv = ClassEnv { classes = \i -> Nothing
                      , defaults = [tInteger, tDouble]
                      }

