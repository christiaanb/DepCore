{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
module Environment where

import Bound
import Bound.Name
import Control.Comonad
import Control.Monad.Except

import Core

data Env m f g a = Env
                 { lookupTyp :: a -> m (f a)
                 , lookupDef :: a -> m (EnvEntry f g a)
                 }

data EnvEntry f g a
  = Cloj (f a)
  | Val  g
  deriving Functor

extendEnvLet :: (Show n, MonadError String m)
             => Env m (Term n) (Value m n) a
             -> Int
             -> Prog n a
             -> Env m (Term n) (Value m n) (Var (Name n Int) a)
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

extendEnv :: Monad m
          => Env m (Term n) (Value m n) a
          -> Type n a
          -> Env m (Term n) (Value m n) (Var (Name n ()) a)
extendEnv (Env ctxOld defOld) bType = Env ctx' def'
  where
    ctx' (B _)  = return (F <$> bType)
    ctx' (F tm) = (fmap . fmap) F (ctxOld tm)

    def' (B x)  = return (Val $ Neutral (NVar $ name x))
    def' (F tm) = (fmap . fmap) F (defOld tm)

extendEnvV :: Monad m
           => Env m (Term n) (Value m n) a
           -> Type n a
           -> Value m n
           -> Env m (Term n) (Value m n) (Var b a)
extendEnvV (Env ctxOld defOld) bType v = Env ctx' def'
  where
    ctx' (B _)  = return (F <$> bType)
    ctx' (F tm) = (fmap . fmap) F (ctxOld tm)

    def' (B _)  = return (Val v)
    def' (F tm) = (fmap . fmap) F (defOld tm)
