{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings,
             ScopedTypeVariables, FlexibleContexts, GeneralizedNewtypeDeriving,
             LambdaCase, ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}

import Bound
import Bound.Name
-- import Bound.Scope
-- import Bound.Var
import Control.Comonad
import Control.Monad
import Control.Monad.Except
-- import Control.Monad.Trans.Maybe
import Data.Bifunctor
-- import Data.List
import Data.String
import Prelude.Extras
-- import qualified Data.Set
-- import Debug.Trace

newtype Eval a = Eval { runEval :: (Except String a) }
  deriving (Functor, Applicative, Monad, MonadError String)

doEval :: Show a => Eval a -> IO ()
doEval t = case runExcept $ runEval t of
             Left s  -> putStrLn s
             Right a -> print a

data Term n a
  = Var (Annotation (Term n a)) !a
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
  | Assume (Term n a, Term n a) (Term n a)
  | Require (Term n a) (Scope () (Term n) a, Scope () (Term n) a)
  | BelieveMe (Annotation (Term n a))
  | Impossible (Annotation (Term n a))
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Type = Term

data Binder n f
  = Pi    n f
  | Lam   n (Annotation f)
  | Sigma n f
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

newtype Annotation f = Ann { unAnn :: Maybe f }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type Prog n a = [Name n ( Scope (Name n Int) (Type n) a
                        , Scope (Name n Int) (Term n) a)]

data Tup = Fst | Snd
  deriving (Eq,Ord,Show)

instance Eq n => Eq1 (Term n)
instance Ord n => Ord1 (Term n)
instance Show n => Show1 (Term n)

instance Applicative (Term n) where
  pure  = Var noAnn
  (<*>) = ap

instance Monad (Term n) where
  return = Var noAnn
  (>>=)  = bindTerm

bindTerm :: Term n a -> (a -> Term n b) -> Term n b
bindTerm (Var _ x)             f = f x
bindTerm Type                  _ = Type
bindTerm (Q b s)               f = Q (fmap (`bindTerm` f) b) (s >>>= f)
bindTerm (Let n p s)           f = Let n (bindProg p f) (s >>>= f)
bindTerm (App e u)             f = App (bindTerm e f) (bindTerm u f)
bindTerm (Pair l r an)         f = Pair (bindTerm l f) (bindTerm r f)
                                        (fmap (`bindTerm` f) an)
bindTerm (Split t (x,y) s an)  f = Split (bindTerm t f) (x,y) (s >>>= f)
                                         (fmap (`bindTerm` f) an)
bindTerm (Enum ns)             _ = Enum ns
bindTerm (Label n an)          f = Label n (fmap (`bindTerm` f) an)
bindTerm (Case t alts an)      f = Case (bindTerm t f)
                                        (map (second (`bindTerm` f)) alts)
                                        (fmap (`bindTerm` f) an)
bindTerm (Lift t)              f = Lift (bindTerm t f)
bindTerm (Box t)               f = Box (bindTerm t f)
bindTerm (Force t)             f = Force (bindTerm t f)
bindTerm (Assume (l,r) t)      f = Assume (bindTerm l f,bindTerm r f)
                                          (bindTerm t f)
bindTerm (Require t (l,r))     f = Require (bindTerm t f)
                                           (l >>>= f, r >>>= f)
bindTerm (BelieveMe an)        f = BelieveMe (fmap (`bindTerm` f) an)
bindTerm (Impossible an)       f = Impossible (fmap (`bindTerm` f) an)

bindProg :: Prog n a -> (a -> Term n b) -> Prog n b
bindProg ps f = map (fmap (bimap (>>>= f) (>>>= f))) ps

instance IsString a => IsString (Term n a) where
  fromString = Var noAnn . fromString

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

noAnn :: Annotation a
noAnn = Ann Nothing

ann :: a -> Annotation a
ann = Ann . Just

inferType :: (Eq a, Eq n, Ord n, Show n, Show a)
          => Env' n a
          -> Term n a
          -> Eval (Term n a,Type n a)
inferType env tm = tcTerm env tm Nothing

checkType :: (Eq a, Eq n, Ord n, Show n, Show a)
          => Env' n a
          -> Term n a
          -> Type n a
          -> Eval (Term n a,Type n a)
checkType env tm ty = tcTerm env tm (Just ty)

tcTerm :: (Eq a, Eq n, Ord n, Show n, Show a)
       => Env' n a
       -> Term n a
       -> Maybe (Type n a)
       -> Eval (Term n a,Type n a)
tcTerm env (Var (Ann ma) a) Nothing = do
  ty <- maybe (return (ctx env a)) return ma
  return (Var (ann ty) a,ty)

tcTerm _ t@Type Nothing = return (t,Type)

tcTerm env (Q (Pi n tyA) tyB) Nothing = do
  atyA <- tcType env tyA
  let env' = extendEnvQ env atyA
  atyB <- tcType env' (fromScope tyB)
  return (Q (Pi n atyA) (toScope atyB), Type)

tcTerm env (Q (Lam n (Ann tmM)) s) Nothing = do
  tyA <- maybe (throwError "Must annotate lambda") return tmM
  atyA <- tcType env tyA
  let env' = extendEnvQ env atyA
  (ebody,atyB) <- inferType env' (fromScope s)
  return (Q (Lam n (ann atyA)) (toScope ebody)
         ,Q (Pi n atyA) (toScope atyB)
         )

tcTerm env t@(Q (Lam _ _) _) (Just x) = tcTerm' env t =<< eval env x

tcTerm env (Q (Sigma n tyA) tyB) Nothing = do
  atyA <- tcType env tyA
  let env' = extendEnvQ env atyA
  atyB <- tcType env' (fromScope tyB)
  return (Q (Sigma n atyA) (toScope atyB),Type)

tcTerm env (Let n prog body) an = do
  (env',prog') <- checkProg env prog
  (abody,ty) <- tcTerm env' (fromScope body) (fmap (fmap F) an)
  return (Let n prog' (toScope abody),Let n prog' (toScope ty))

tcTerm env (App t u) Nothing = do
  (at,atty) <- inferType env t
  eval env atty >>= \case
    VQ (Pi _ tyA) tyB -> do
      (au,_) <- checkType env u tyA
      return (App at au,instantiate1Name au tyB)
    _ -> throwError "tcTerm: expected pi"

tcTerm env t@(Pair l r an1) an2 = do
  ty <- matchAnnots env t an1 an2
  eval env ty >>= \case
    VQ (Sigma _ tyA) tyB -> do
      (al,_) <- checkType env l tyA
      let tyB' = instantiate1Name l tyB
      (ar,_) <- checkType env r tyB'
      return (Pair al ar (ann ty), ty)
    _ -> throwError "tcTerm: expected sigma"

-- tcTerm env tm (Just ty) = do
--   (atm,ty') <- inferType env tm
--   eq env ty' ty
--   return (atm,ty)

tcTerm' :: (Eq a, Eq n, Ord n, Show n, Show a)
        => Env' n a
        -> Term n a
        -> Value n a
        -> Eval (Term n a,Type n a)
tcTerm' env (Q (Lam n (Ann ma)) body) (VQ (Pi m tyA) tyB) = do
  maybe (return ()) (eq env tyA) ma
  let env' = extendEnvQ env tyA
  (ebody,_) <- checkType env' (fromScope body) (fromScope tyB)
  return (Q (Lam n (ann tyA)) (toScope ebody)
         ,Q (Pi m tyA) tyB
         )

tcTerm' _ (Q (Lam _ _) _) ty = throwError ("check': expected pi: " ++ show (quote ty))

tcType :: (Eq a, Eq n, Ord n, Show n, Show a)
       => Env' n a
       -> Type n a
       -> Eval (Type n a)
tcType env tm = do
  (atm,_) <- checkType env tm Type
  return atm

checkProg :: (Eq a, Eq n, Ord n, Show n, Show a)
          => Env' n a
          -> Prog n a
          -> Eval (Env' n (Var (Name n Int) a), Prog n a)
checkProg env p = do
  let env' = extendEnvLet env p
  p' <- mapM (checkProg' env' . fmap (bimap fromScope fromScope)) p
  return (env',map (fmap (bimap toScope toScope)) p')

checkProg' :: (Eq a, Eq n, Ord n, Show n, Show a)
           => Env' n a
           -> Name n (Type n a, Term n a)
           -> Eval (Name n (Type n a, Term n a))
checkProg' env (Name n (ty,tm)) = do
  aty     <- tcType env ty
  (atm,_) <- checkType env tm aty
  return (Name n (aty,atm))

extendEnvQ :: Env' n a
           -> Term n a
           -> Env' n (Var (Name n ()) a)
extendEnvQ (Env ctxOld defOld) tm = Env ctx' def'
  where
    ctx' (B _)   = F <$> tm
    ctx' (F tm') = F <$> ctxOld tm'

    def' x@(B _) = Id x
    def' (F tm') = F <$> defOld tm'

extendEnvLet :: Env' n a
             -> Prog n a
             -> Env' n (Var (Name n Int) a)
extendEnvLet (Env ctxOld defOld) ps = Env ctx' def'
  where
    ctx' (B x)  = fromScope . fst . extract . (ps!!) $ extract x
    ctx' (F tm) = F <$> ctxOld tm

    def' (B x)  = Cloj . fromScope . snd . extract . (ps!!) $ extract x
    def' (F tm) = F <$> defOld tm

data Value n a
  = Neutral (Neutral n a)
  | VType
  | VQ (Binder n (Term n a)) (Scope (Name n ()) (Term n) a)
  | VPair  (Term n a) (Term n a)
  | VEnum [n]
  | VLabel n
  | VLift  (Type n a)
  | VBox   (Boxed n a)
  | VBelieveMe
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

newtype Boxed n a = Boxed { unBoxed :: Term n a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Neutral n a
  = NVar a
  | NApp (Neutral n a) (Term n a)
  | NSplit (Neutral n a) (n,n) (Scope (Name n Tup) (Term n) a)
  | NCase (Neutral n a) [(n,Term n a)]
  | NForce (Neutral n a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Eq n => Eq1 (Value n)
instance Ord n => Ord1 (Value n)
instance Show n => Show1 (Value n)

eval :: (MonadError String m, Eq n)
     => Env' n a -> Term n a -> m (Value n a)
eval = undefined

quote :: Value n a -> Term n a
quote = undefined

class Equal f where
  eq :: (MonadError String m, Eq a, Eq n, Show n, Show a)
     => Env' n a -> f n a -> f n a -> m ()

instance Equal Term where
  eq = undefined

matchAnnots :: (Eq a, Eq n, Ord n, Show n, Show a)
            => Env' n a -> Term n a -> Annotation (Term n a) -> Maybe (Type n a)
            -> Eval (Type n a)
matchAnnots _   e (Ann Nothing) Nothing   = throwError (show e ++ " requires annotation")
matchAnnots _   _ (Ann Nothing) (Just ty) = return ty
matchAnnots env _ (Ann (Just ty)) Nothing = do
  aty <- tcType env ty
  return aty
matchAnnots env _ (Ann (Just ty1)) (Just ty2) = do
  aty1 <- tcType env ty1
  eq env aty1 ty2
  return aty1
