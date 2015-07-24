{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Evaluate where

import Bound
import Bound.Name
import Control.Comonad
import Control.Monad.Except

import Core
import Environment

newtype Eval a = Eval (Except String a)
  deriving (Functor, Applicative, Monad, MonadError String)

eval :: Env Eval (Term n) (Value Eval n) a
     -> Term n a
     -> Eval (Value Eval n)
eval env (Var x) = do
  k <- lookupDef env x
  case k of
    Cloj tm -> eval env tm
    Val v   -> return v

eval _ Type = return VType

quote :: (Eq n, Monad m) => (n -> Term n a) -> Value m n -> m (Term n a)
quote k = quote' 0 k undefined

quote' :: (Eq n, Monad m)
       => Int -> (n -> Term n a) -> (Int -> Term n a) -> Value m n
       -> m (Term n a)
quote' q k l (Neutral n)  = quoteNeutral q k l n
quote' q _ _ VType        = return Type
quote' q k l (VTmp n)     = return (l (q-n-1))
quote' q k l (VBind (Pi v) f)    = do
  v' <- quote' q k l (extract v)
  s  <- f (VTmp q)
  let n a = Name (name v) a
  s' <- quote' (q+1) (Var . F . k) (intToVar (n ()) l) s
  return (Bind (Pi (n v')) (Scope s'))

quoteNeutral :: (Eq n, Monad m)
             => Int -> (n -> Term n a) -> (Int -> Term n a) -> Neutral m n
             -> m (Term n a)
quoteNeutral _ k _ (NVar n)   = return (k n)
quoteNeutral q k l (NApp e u) = App <$> quoteNeutral q k l e <*> quote' q k l u

intToVar :: Monad f => b -> (Int -> f a) -> Int -> f (Var b (f a))
intToVar n f i
  | i == 0    = return (B n)
  | otherwise = return . F $ f (i - 1)
