{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
module Core where

import Bound
import Bound.Name
import Control.Monad
import Control.Monad.Trans.Class
import Data.Bifunctor
import Prelude hiding (pi)
import Prelude.Extras

import SrcLoc
import FastString

data Term n a
  = Var    !a
  | Bind   !(Binder n (Term n a)) (Scope (Name n ()) (Term n) a)
  | App    !(Term n a) !(Term n a)
  | Let    !Int (Prog n a) (Scope (Name n Int) (Term n) a)
  | Type
  | HardTerm HardTerm
  | Pair   !(Term n a) !(Term n a)
  | Split  !(Term n a) (Scope (Name n ()) (Scope (Name n ()) (Term n)) a)
  | Enum   [n]
  | Label  n
  | Lift   !(Term n a)
  | Box    !(Term n a)
  | Force  !(Term n a)
  | Rec    !(Term n a)
  | Fold   !(Term n a)
  | Unfold !(Term n a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data HardTerm
  = String  String
  | Integer Integer
  | StringT
  | IntegerT
  deriving (Eq,Ord,Show)

instance Eq n => Eq1 (Term n)
instance Ord n => Ord1 (Term n)
instance Show n => Show1 (Term n)

data Binder n a
  = Lam   (Name n ())
  | Pi    (Name n a)
  | Sigma (Name n a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Prog n a =
  ( Name n (Type n a,Scope (Name n Int) (Term n) a)
  , [Name n (Scope (Name n Int) (Type n) a, Scope (Name n Int) (Term n) a)]
  )

type LVar   = Located FastString
type Type n = Term n

instance Applicative (Term n) where
  pure  = Var
  (<*>) = ap

instance Monad (Term n) where
  return = Var
  (>>=)  = bindTerm

bindTerm :: Term n a -> (a -> Term n b) -> Term n b
bindTerm tm f = case tm of
  Var a      -> f a
  Bind b s   -> Bind (fmap (`bindTerm` f) b) (s >>>= f)
  App e1 e2  -> App (bindTerm e1 f) (bindTerm e2 f)
  Let n p e  -> Let n (bindProg p f) (e >>>= f)
  Type       -> Type
  HardTerm h -> HardTerm h
  Pair e1 e2 -> Pair (bindTerm e1 f) (bindTerm e2 f)
  Split b s  -> Split (bindTerm b f) (s >>>= (lift . f))
  Enum ls    -> Enum ls
  Label l    -> Label l
  Lift t     -> Lift (bindTerm t f)
  Box t      -> Box (bindTerm t f)
  Force t    -> Force (bindTerm t f)
  Rec t      -> Rec (bindTerm t f)
  Fold t     -> Fold (bindTerm t f)
  Unfold t   -> Unfold (bindTerm t f)

bindProg :: Prog n a -> (a -> Term n b) -> Prog n b
bindProg (p0,ps) f =
  ( fmap (bimap (`bindTerm` f) (>>>= f)) p0
  , map  (fmap (bimap (>>>= f) (>>>= f))) ps
  )

data Value m n
  = Neutral (Neutral m n)
  | VType
  | VBind (Binder n (Value m n)) (Value m n -> m (Value m n))

data Neutral m n
  = NVar n
  | NApp (Neutral m n) (Value m n)

-- * Smart constructors
type CoreTerm = Term LVar LVar
type CoreType = CoreTerm

q :: (Name LVar CoreTerm -> Binder LVar CoreTerm) -> [(LVar,CoreTerm)]
  -> CoreTerm -> CoreTerm
q f = flip (foldr (\(v,b) e -> Bind (f (Name v b)) (abstract1Name v e)))

lam :: [LVar] -> CoreTerm -> CoreTerm
lam = flip (foldr (\v e -> Bind (Lam (Name v ())) (abstract1Name v e)))

split :: CoreTerm -> (LVar,LVar) -> CoreTerm -> CoreTerm
split t1 (x,y) t2 = Split t1 (abstract1Name x (abstract1Name y t2))

pis' :: [(LVar,CoreType)] -> CoreType -> CoreType
pis' = q Pi

pis :: [LVar] -> CoreType -> CoreType -> CoreType
pis ns t = pis' (map (,t) ns)

pi :: LVar -> CoreType -> CoreType -> CoreType
pi n t = pis' [(n,t)]

sigmas' :: [(LVar,CoreType)] -> CoreType -> CoreType
sigmas' = q Sigma

sigmas :: [LVar] -> CoreType -> CoreType -> CoreType
sigmas ns t = sigmas' (map (,t) ns)

sigma :: LVar -> CoreType -> CoreType -> CoreType
sigma n t = sigmas' [(n,t)]

(->-) :: CoreType -> CoreType -> CoreType
(->-) = pi (noLoc (fsLit ""))

(-*-) :: CoreType -> CoreType -> CoreType
(-*-) = sigma (noLoc (fsLit ""))
