{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings,
             ScopedTypeVariables, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wall #-}


import Bound
import Bound.Name
import Control.Comonad
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Prelude.Extras

newtype Eval a = Eval (Except String a)
  deriving (Functor, Applicative, Monad, MonadError String)

data Term n a
  = Var !a
  | Type
  | Pi (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  | Let !Int (Prog n a) (Scope (Name n Int) (Term n) a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Value n
  = Neutral (Neutral n)
  | VType
  | VPi (Value n) (Value n -> Eval (Value n))

data Neutral n
  = NVar n
  | NApp (Neutral n) (Value n)

instance Eq n => Eq1 (Term n)
instance Ord n => Ord1 (Term n)
instance Show n => Show1 (Term n)

type Type n = Term n

type Prog n a =
  ( Name n (Type n a,Scope (Name n Int) (Term n) a)
  , [Name n (Scope (Name n Int) (Type n) a, Scope (Name n Int) (Term n) a)]
  )

instance Applicative (Term n) where
  pure  = Var
  (<*>) = ap

instance Monad (Term n) where
  return = Var
  (>>=)  = bindTerm

bindTerm :: Term n a -> (a -> Term n b) -> Term n b
bindTerm (Var x) f     = f x
bindTerm Type _        = Type
bindTerm (Pi tm s) f   = Pi (fmap (`bindTerm` f) tm) (s >>>= f)
bindTerm (Let n p s) f = Let n (bindProg p f) (s >>>= f)

bindProg :: Prog n a -> (a -> Term n b) -> Prog n b
bindProg (p0,ps) f =
  ( fmap (bimap (`bindTerm` f) (>>>= f)) p0
  , map  (fmap (bimap (>>>= f) (>>>= f))) ps
  )

data Env m f g a
  = Env
  { ctx :: a -> m (f a)
  , def :: a -> m (EnvEntry f g a)
  }

data EnvEntry f g a
  = Cloj (f a)
  | Val g
  deriving Functor

extendEnvLet :: (MonadError String m, Show n)
             => Env m (Term n) (Value n) a
             -> Int
             -> Prog n a
             -> Env m (Term n) (Value n) (Var (Name n Int) a)
extendEnvLet (Env ctxOld defOld) sz (p0,ps) = Env ctx' def'
  where
    ctx' (B x)  = case extract x of
                    0 -> return (F <$> (fst $ extract p0))
                    n | n < sz -> return . fromScope . fst . extract $ (ps!!(n-1))
                    _ -> throwError ("undeclared variable: " ++ show x)
    ctx' (F tm) = (fmap . fmap) F (ctxOld tm)

    def' (B x)  = case extract x of
                    n | n < sz -> return . Cloj . fromScope . snd . extract $ (ps!!n)
                    _ -> throwError ("undefined variable: " ++ show x)
    def' (F tm) = (fmap . fmap) F (defOld tm)

extendEnvPi :: (MonadError String m, Show n)
            => Env m (Term n) (Value n) a
            -> Term n a
            -> Env m (Term n) (Value n) (Var (Name n ()) a)
extendEnvPi (Env ctxOld defOld) tm = Env ctx' def'
  where
    ctx' (B _)   = return (F <$> tm)
    ctx' (F tm') = (fmap . fmap) F (ctxOld tm')

    def' (B x)   = return (Val $ Neutral (NVar $ name x))
    def' (F tm') = (fmap . fmap) F (defOld tm')

extendEnvPiV :: (MonadError String m, Show n)
             => Env m (Term n) (Value n) a
             -> Term n a
             -> Value n
             -> Env m (Term n) (Value n) (Var (Name n ()) a)
extendEnvPiV (Env ctxOld defOld) tm v = Env ctx' def'
  where
    ctx' (B _)   = return (F <$> tm)
    ctx' (F tm') = (fmap . fmap) F (ctxOld tm')

    def' (B _)   = return (Val v)
    def' (F tm') = (fmap . fmap) F (defOld tm')

infer :: Show n => Env Eval (Term n) (Value n) a -> Term n a -> Eval (Type n a)
infer env (Var x)             = ctx env x
infer _   Type                = return Type
infer env (Pi tm s) = do
  check env (extract tm) Type
  let env' = extendEnvPi env (extract tm)
  check env' (fromScope s) Type
  return Type

infer env (Let n p s) = do
    let env' = extendEnvLet env n p
    s' <- infer env' (fromScope s)
    return (Let n p (toScope s'))

check :: Env Eval (Term n) (Value n) a -> Term n a -> Term n a -> Eval ()
check = undefined

eval :: Show n => Env Eval (Term n) (Value n) a -> Term n a -> Eval (Value n)
eval env (Var x) = do
  k <- def env x
  case k of
    Cloj tm -> eval env tm
    Val v   -> return v

eval _ Type = return VType

eval env (Pi tm s) = do
  tmv <- eval env (extract tm)
  return (VPi tmv (\x -> let env' = extendEnvPiV env (extract tm) x
                         in eval env' (fromScope s)))

eval env (Let n p s) =
  let env' = extendEnvLet env n p
  in  eval env' (fromScope s)
