{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings,
             ScopedTypeVariables, FlexibleContexts, GeneralizedNewtypeDeriving,
             LambdaCase, ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}

import Bound
import Bound.Name
-- import Bound.Scope
-- import Bound.Var
-- import Control.Comonad
import Control.Monad
-- import Control.Monad.Except
-- import Control.Monad.Trans.Maybe
import Data.Bifunctor
-- import Data.List
import Data.String
import Prelude.Extras
-- import qualified Data.Set
-- import Debug.Trace

data Term n a
  = Var !a
  | Type
  | Q !(Binder n (Term n a)) (Scope (Name n ()) (Term n) a)
  | Let !Int (Prog n a) (Scope (Name n Int) (Term n) a)
  | App !(Term n a) !(Term n a)
  | Pair !(Term n a) !(Term n a) (Annotation (Term n a))
  | Split !(Term n a) !(n,n) (Scope (Name n Tup) (Term n) a) (Annotation (Term n a))
  | Enum [n]
  | Label n (Annotation (Term n a))
  | Case !(Term n a) [(n,Term n a)] (Annotation (Term n a))
  | Lift !(Term n a)
  | Box !(Term n a)
  | Force !(Term n a)
  | BeleiveMe (Annotation (Term n a))
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Type = Term

data Binder n f
  = Pi    n f
  | Lam   n (Annotation f)
  | Sigma n f
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

newtype Annotation f = A { unA :: Maybe f }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Prog n a = [Name n ( Scope (Name n Int) (Type n) a
                        , Scope (Name n Int) (Term n) a)]

data Tup = Fst | Snd
  deriving (Eq,Ord,Show)

instance Eq n => Eq1 (Term n)
instance Ord n => Ord1 (Term n)
instance Show n => Show1 (Term n)

instance Applicative (Term n) where
  pure  = Var
  (<*>) = ap

instance Monad (Term n) where
  return = Var
  (>>=)  = bindTerm

bindTerm :: Term n a -> (a -> Term n b) -> Term n b
bindTerm (Var x)               f = f x
bindTerm Type                  _ = Type
bindTerm (Q b s)               f = Q (fmap (`bindTerm` f) b) (s >>>= f)
bindTerm (Let n p s)           f = Let n (bindProg p f) (s >>>= f)
bindTerm (App e u)             f = App (bindTerm e f) (bindTerm u f)
bindTerm (Pair l r ann)        f = Pair (bindTerm l f) (bindTerm r f)
                                        (fmap (`bindTerm` f) ann)
bindTerm (Split t (x,y) s ann) f = Split (bindTerm t f) (x,y) (s >>>= f)
                                         (fmap (`bindTerm` f) ann)
bindTerm (Enum ns)             _ = Enum ns
bindTerm (Label n ann)         f = Label n (fmap (`bindTerm` f) ann)
bindTerm (Case t alts ann)     f = Case (bindTerm t f)
                                        (map (second (`bindTerm` f)) alts)
                                        (fmap (`bindTerm` f) ann)
bindTerm (Lift t)              f = Lift (bindTerm t f)
bindTerm (Box t)               f = Box (bindTerm t f)
bindTerm (Force t)             f = Force (bindTerm t f)
bindTerm (BeleiveMe ann)       f = BeleiveMe (fmap (`bindTerm` f) ann)

bindProg :: Prog n a -> (a -> Term n b) -> Prog n b
bindProg ps f = map (fmap (bimap (>>>= f) (>>>= f))) ps

instance IsString a => IsString (Term n a) where
  fromString = Var . fromString

data Env f g a
  = Env
  { ctx :: a -> f a
  , def :: a -> g a
  }

data EnvEntry f a
  = Cloj (f a)
  | Id   a
  deriving Functor

type EnvEntry' n = EnvEntry (Term n)
type Env' n      = Env (Term n) (EnvEntry' n)

emptyEnv :: Show a => Env f g a
emptyEnv = Env (\x -> error ("No declaration for: " ++ show x))
               (\x -> error ("No definition for: " ++ show x))
