{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings,
             ScopedTypeVariables, FlexibleContexts, GeneralizedNewtypeDeriving,
             Rank2Types, GADTs #-}
{-# OPTIONS_GHC -Wall #-}


import Bound
import Bound.Name
import Bound.Var
import Control.Comonad
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Prelude.Extras

newtype Eval a = Eval { runEval :: (Except String a) }
  deriving (Functor, Applicative, Monad, MonadError String)

data Term n a
  = Var !a
  | Type
  | Pi (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  | Let !Int (Prog n a) (Scope (Name n Int) (Term n) a)
  | App (Term n a) (Term n a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Value n a
  = Neutral (Neutral n a)
  | VType
  | VPi (Name n (Value n a)) (Value n a -> Eval (Value n a))
  | VTmp (Var (Name n ()) a)

data Neutral n a
  = NVar n
  | NApp (Neutral n a) (Value n a)

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
bindTerm (App e u) f   = App (bindTerm e f) (bindTerm u f)

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
             => Env m (Term n) (Value n b) a
             -> Int
             -> Prog n a
             -> Env m (Term n) (Value n b) (Var (Name n Int) a)
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
            => Env m (Term n) (Value n n) a
            -> Term n a
            -> Env m (Term n) (Value n n) (Var (Name n ()) a)
extendEnvPi (Env ctxOld defOld) tm = Env ctx' def'
  where
    ctx' (B _)   = return (F <$> tm)
    ctx' (F tm') = (fmap . fmap) F (ctxOld tm')

    def' (B x)   = return (Val $ Neutral (NVar $ name x))
    def' (F tm') = (fmap . fmap) F (defOld tm')

extendEnvPiV :: (MonadError String m, Show n)
             => Env m (Term n) (Value n a) a
             -> Term n a
             -> Value n a
             -> Env m (Term n) (Value n a) (Var (Name n ()) a)
extendEnvPiV (Env ctxOld defOld) tm v = Env ctx' def'
  where
    ctx' (B _)   = return (F <$> tm)
    ctx' (F tm') = (fmap . fmap) F (ctxOld tm')

    def' (B _)   = return (Val v)
    def' (F tm') = (fmap . fmap) F (defOld tm')

infer :: Show n
      => Env Eval (Term n) (Value n n) a
      -> Term n a
      -> Eval (Type n a)
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

check :: Env Eval (Term n) (Value b n) a -> Term n a -> Term n a -> Eval ()
check = undefined

-- eval :: Show n => Env Eval (Term n) (Value n c) a -> Term n a -> Eval (Value n c)
-- eval env (Var x) = do
--   k <- def env x
--   case k of
--     Cloj tm -> eval env tm
--     Val v   -> return v

eval _ Type = return VType

-- eval env (Pi tm s) = do
--   tmv <- eval env (extract tm)
--   return (VPi (Name (name tm) tmv)
--               (VScope (\x -> let env' = extendEnvPiV env (extract tm) x
--                              in  eval undefined (fromScope s)
--                       )
--               ))
-- --               (VScope (\x -> let env' = extendEnvPiV env (extract tm) x
--                      in eval env' (fromScope s))))

-- eval env (Let n p s) =
--   let env' = extendEnvLet env n p
--   in  eval env' (fromScope s)

-- quote :: forall n a b . (a -> Term n a) -> Value n a -> Eval (Term n a)
-- -- quote z k (Neutral n) = neutralQuote k n
-- -- quote z k (VPi v f) = do
-- --   v' <- quote z k (extract v)
-- --   s' <- quote z (Var . F . k) =<< (f (Neutral $ NVar z))
-- --   return (Pi (Name (name v) v') (Scope s'))
-- quote k (Neutral n) = neutralQuote k n
-- quote k (VPi v f) = do
--   v' <- quote k (extract v)
--   let p :: Value n (Var (Name n ()) a)
--       p = vfree (B (Name (name v) ()))
--   -- s' <- f p
--   -- s' <- quote (Var . F . k) undefined
--   -- return (Pi (Name (name v) v') (Scope s'))
--   (Pi (Name (name v) v') . toScope) <$> (quote _ =<< (_ (f p)))

-- quote :: Eq n => a -> (n -> a) -> (a -> n) -> Value n -> Eval (Term n a)
-- quote i g k (VPi v f) = do
--   v' <- quote i g k (extract v)
--   s  <- f (vfree (_ (B (Name (name v) ()))))
--   s' <- quote (F (Var i)) (F . Var . g) (k . unvar) s
--   return (Pi (Name (name v) v') (Scope s'))
-- quote _ _ _ VType = return Type
-- quote i g k (Neutral n) = neutralQuote i g k n

-- aap :: a
--     -> (a -> Term n a)
--     -> Value n a
--     -> Eval (Term n a)
-- aap _ k (Neutral n) = neutralQuote k n
-- aap a k (VPi v (VScope f)) = do
--   v' <- aap k (extract v)
--   s  <- f (vfree (B (Name (name v) ())))
--   s' <- aap undefined s
--   return (Pi (Name (name v) v') (toScope s'))

-- aap a k (VPi2 v f) = do
--   v' <- aap a k (extract v)
--   s  <- fmap undefined (f (vfree a))
--   s' <- aap (B (Name (name v) ())) Var s
--   return (Pi (Name (name v) v') (Scope s'))

-- aap :: (n -> Term n a) -> Value n a -> Eval (Scope (Name n ()) (Term n) a)
-- aap k (VPi v f) = do
--   v' <- aap k (extract v)
--   (Pi (Name (name v) v') . lift) <$> (aap k =<< (f (VTmp (B (Name (name v) ())))))
-- aap _ (VTmp a)    = return (Scope $ Var a)
-- aap k (Neutral n) = _ n

-- aap0 :: Value String (Term String String) -> Eval (Term String String)
-- aap0 x = aap Var x

-- neutralQuote :: (n -> Term n a) -> Neutral n (Term n a) -> Eval (Term n a)
-- neutralQuote k (NVar n) = return (k n)

--   v' <- quote (extract v)
--   s  <- f (vfree (k (name v)))
--   s' <- quote s
--   return (Pi (Name (name v) undefined) (toScope s'))
  -- return (Pi (Name (name v) _) (Scope s'))
-- aap (Neutral (NVar n)) = return (unvar (Var . B) id n)

-- noot :: n -> Var (Name n ()) (Term n a)
-- noot n = B (Name n ())

-- quote :: (a -> Term n a) -> Value n a -> Eval (Term n a)
-- quote k (Neutral n) = neutralQuote k n
-- quote k (VPi v f) = do
--   v' <- quote k (extract v)
--   s  <- f (VTmp undefined)
--   s' <- quote undefined s
--   -- undefined
--   return (Pi (Name (name v) v') (Scope s'))


-- neutralQuote :: (a -> Term n a) -> Neutral n a -> Eval (Term n a)
-- neutralQuote k (NVar n) = return (k n)

-- quote0 :: Value String String -> Eval (Term String String)
-- quote0 = quote _ _

-- neutralQuote :: Eq n => a -> (n -> a) -> (a -> n) -> Neutral n -> Eval (Term n a)
-- neutralQuote _ g k (NVar n)   = return (Var (g n))
-- neutralQuote i g k (NApp n v) = do
--   n' <- neutralQuote i g k n
--   v' <- quote i g k v
--   return (App n' v')

-- vfree :: a -> Value n a
-- vfree = Neutral . NVar

-- unvar :: Var b (Term n a) -> a
-- unvar (F (Var i)) = i


-- quote0 :: Value String -> Eval (Term String String)
-- quote0 v = quote _ _ _ v

data Term2 n a
  = Var2 !a
  | Type2
  | Pi2 (Name n (Term2 n a)) (Scope (Name n ()) (Term2 n) a)
  | App2 (Term2 n a) (Term2 n a)
  deriving (Functor, Show)

instance Show n => Show1 (Term2 n)

instance Applicative (Term2 n) where
  pure  = Var2
  (<*>) = ap

instance Monad (Term2 n) where
  return = Var2
  (>>=)  = bindTerm2

bindTerm2 :: Term2 n a -> (a -> Term2 n b) -> Term2 n b
bindTerm2 (Var2 x) f     = f x
bindTerm2 Type2 _        = Type2
bindTerm2 (Pi2 tm s) f   = Pi2 (fmap (`bindTerm2` f) tm) (s >>>= f)
bindTerm2 (App2 e u) f   = App2 (bindTerm2 e f) (bindTerm2 u f)

data Value2 n
  = Neutral2 (Neutral2 n)
  | VType2
  | VPi2 (Name n (Value2 n)) (Value2 n -> Eval (Value2 n))
  | VTmp2 Int

data Neutral2 n
  = NVar2 n
  | NApp2 (Neutral2 n) (Value2 n)

quote :: Eq n => Int -> (n -> Term2 n a) -> (Int -> Term2 n a) -> Value2 n -> Eval (Term2 n a)
quote q k l (Neutral2 n) = quoteNeutral q k l n
quote q _ _ VType2       = return Type2
quote q k l (VTmp2 n)    = return (l (q-n-1))
quote q k l (VPi2 v f)   = do
  v' <- quote q k l (extract v)
  Pi2 (Name (name v) v') . Scope <$> (quote (q+1) (Var2 . F . k) (subF (Name (name v) ()) l) =<< (f (VTmp2 q)))

quoteNeutral :: Eq n => Int -> (n -> Term2 n a) -> (Int -> Term2 n a) -> Neutral2 n -> Eval (Term2 n a)
quoteNeutral _ k _ (NVar2 n)   = return (k n)
quoteNeutral q k l (NApp2 e u) = App2 <$> quoteNeutral q k l e <*> quote q k l u

subF :: Monad f => b -> (Int -> f a) -> Int -> f (Var b (f a))
subF n f i | i == 0    = return (B n)
           | otherwise = return . F $ f (i - 1)

