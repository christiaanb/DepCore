{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Evaluate where

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
