{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings,
             ScopedTypeVariables, FlexibleContexts, GeneralizedNewtypeDeriving,
             LambdaCase, ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}

import Bound
import Bound.Name
import Bound.Scope
-- import Bound.Var
import Control.Comonad
import Control.Monad
import Control.Monad.Except
-- import Control.Monad.Trans.Maybe
import Data.Bifunctor
import Data.List
import Data.String
import Prelude.Extras
import qualified Data.Set
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
  | Require (Term n a) (Scope (Name n ()) (Term n) a, Scope (Name n ()) (Term n) a)
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
  , constraints :: Maybe [Constraint]
  }

data Constraint = Constraint

data EnvEntry f a
  = Cloj (f a)
  | Id   a
  deriving Functor

type EnvEntry' n = EnvEntry (Term n)
type Env' n      = Env (Term n) (EnvEntry' n)

emptyEnv :: Show a => Env f g a
emptyEnv = Env (\x -> error ("No declaration for: " ++ show x))
               (\x -> error ("No definition for: " ++ show x))
               (Just [])

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

tcTerm env (Q (Lam n (Ann ma)) body) (Just x) = eval env x >>= \case
    VQ (Pi m tyA) tyB -> do
      maybe (return ()) (eq env tyA) ma
      let env' = extendEnvQ env tyA
      (ebody,_) <- checkType env' (fromScope body) (fromScope tyB)
      return (Q (Lam n (ann tyA)) (toScope ebody)
             ,Q (Pi m tyA) tyB
             )
    ty' -> throwError ("check': expected pi: " ++ show (quote ty'))

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

tcTerm _ t@(Enum ls) Nothing =
  if nub ls /= ls
     then throwError "tcTerm: duplicate labels"
     else return (t,Type)

tcTerm env t@(Label l an1) an2 = do
  ty <- matchAnnots env t an1 an2
  eval env ty >>= \case
    VEnum ls | l `elem` ls -> return (Label l (ann ty),Enum ls)
             | otherwise   -> throwError "tcTerm: label not of enum"
    _ -> throwError "tcTerm: expected enum"

tcTerm env t@(Split p (x,y) body ann1) ann2 = do
  ty <- matchAnnots env t ann1 ann2
  (apr,pty) <- inferType env p
  sigmab <- eval env pty
  case sigmab of
    VQ (Sigma _ tyA) tyB -> do
      let env' = extendEnvSplit env tyA tyB x y apr
      (abody,_) <- checkType env' (fromScope body) (F <$> ty)
      return (Split apr (x,y) (toScope abody) (ann ty),ty)
    _ -> throwError "tcTerm: split: expected sigma"

tcTerm env t@(Case scrut alts ann1) ann2 = do
  ty <- matchAnnots env t ann1 ann2
  (ascrut,sty) <- inferType env scrut
  enum <- eval env sty
  case enum of
    VEnum ls ->
      let ls' = map fst alts
      in  if (Data.Set.fromList ls) /= (Data.Set.fromList ls')
             then throwError ("tcTerm: labels don't match: " ++ show (ls,ls'))
             else do
               alts' <- mapM (\(l,u) -> do let env' = extendEnvCase env ascrut l
                                           (au,_) <-  checkType env' u ty
                                           return (l,au)) alts
               return (Case ascrut alts' (ann ty),ty)
    _ -> throwError "tcTerm: case: expected enum"

tcTerm env (Lift ty) Nothing = do
  aty <- tcType env ty
  return (Lift aty,Type)

tcTerm env (Box t) Nothing = do
  (at,aty) <- inferType env t
  return (Box at, Lift aty)

tcTerm env (Box t) (Just ty) = do
  eval env ty >>= \case
    VLift ty' -> do
      (at,_) <- checkType env t ty'
      return (Box at,Lift ty')
    _ -> throwError "tcTerm: Box: expected lift"

tcTerm env (Force t) Nothing = do
  (at,aty) <- inferType env t
  eval env aty >>= \case
    VLift ty' -> return (Force at,ty')
    _ -> throwError "tcTerm: Force: expected lift"

tcTerm env (Force t) (Just ty) = checkType env t (Lift ty)

tcTerm _ (Require ty (l,r)) Nothing = do
  -- TODO: check context validity
  -- |- Gamma,x:sigma,t==p
  return (Require ty (l,r),Type)

tcTerm env t@(BelieveMe ann1) ann2 = do
  expectedTy <- matchAnnots env t ann1 ann2
  return (BelieveMe (ann expectedTy), expectedTy)

tcTerm env t@(Impossible ann1) ann2 = do
  expectedTy <- matchAnnots env t ann1 ann2
  case constraints env of
    Nothing -> return (Impossible (ann expectedTy),expectedTy)
    _ -> throwError "tcTerm: consistent context"

tcTerm env tm (Just (Require ty (l,r))) = do
  eq env (instantiate1Name tm l) (instantiate1Name tm r)
  checkType env tm ty

tcTerm env tm (Just ty) = do
  (atm,ty') <- inferType env tm
  case ty' of
    Require ty'' (l,r) -> do
      eq env (instantiate1Name tm l) (instantiate1Name tm r)
      eq env ty'' ty
    _ -> eq env ty' ty
  return (atm,ty)

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
extendEnvQ (Env ctxOld defOld cs) tm = Env ctx' def' cs
  where
    ctx' (B _)   = F <$> tm
    ctx' (F tm') = F <$> ctxOld tm'

    def' x@(B _) = Id x
    def' (F tm') = F <$> defOld tm'

extendEnvLet :: Env' n a
             -> Prog n a
             -> Env' n (Var (Name n Int) a)
extendEnvLet (Env ctxOld defOld cs) ps = Env ctx' def' cs
  where
    ctx' (B x)  = fromScope . fst . extract . (ps!!) $ extract x
    ctx' (F tm) = F <$> ctxOld tm

    def' (B x)  = Cloj . fromScope . snd . extract . (ps!!) $ extract x
    def' (F tm) = F <$> defOld tm

extendEnvConstraint :: Env' n a
                    -> Term n a
                    -> Term n a
                    -> Env' n a
extendEnvConstraint = undefined

extendEnvSplit :: Eq a
               => Env' n a
               -> Type n a
               -> Scope (Name n ()) (Type n) a
               -> n -> n -> Term n a
               -> Env' n (Var (Name n Tup) a)
extendEnvSplit (Env ctxOld defOld cs) tyA tyB x y p =
    extendEnvConstraint (Env ctx' def' cs)
                        (F <$> p)
                        (Pair (Var noAnn (B (Name x Fst)))
                              (Var noAnn (B (Name y Snd))) noAnn)
  where
    ctx' (B (Name _ Fst)) = F <$> tyA
    ctx' (B (Name _ Snd)) = fromScope (mapBound (const (Name x Fst)) tyB)
    ctx' (F tm')  = F <$> ctxOld tm'

    def' b@(B _) = Id b
    def' (F tm') = F <$> defOld tm'

extendEnvCase :: Eq a
              => Env' n a
              -> Term n a -> n
              -> Env' n a
extendEnvCase env tm l = extendEnvConstraint env tm (Label l noAnn)

data Value n a
  = Neutral (Neutral n a)
  | VType
  | VQ (Binder n (Term n a)) (Scope (Name n ()) (Term n) a)
  | VPair  (Term n a) (Term n a)
  | VEnum [n]
  | VLabel n
  | VLift  (Type n a)
  | VBox   (Boxed n a)
  | VRequire (Term n a) (Scope (Name n ()) (Term n) a, Scope (Name n ()) (Term n) a)
  | VBelieveMe
  | VImpossibe
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
eval env (Var _ x)         = case def env x of
                               Cloj tm -> eval env tm
                               Id v    -> return (Neutral (NVar v))
eval _   Type              = return VType
eval _   (Q b s)           = return (VQ b s)
eval env (Let _ p s)       = let inst = instantiateName es
                                 es   = inst . defs p
                             in  eval env (inst s)
eval env (App t u)         = flip (evalApp env) u =<< eval env t
eval _   (Pair l r _)      = return (VPair l r)
eval env (Split t xy s _)  = flip (evalSplit env xy) s =<< eval env t
eval _   (Enum ls)         = return (VEnum ls)
eval _   (Label l _)       = return (VLabel l)
eval env (Case t as _)     = flip (evalCase env) as =<< eval env t
eval _   (Lift t)          = return (VLift t)
eval _   (Box t)           = return (VBox (Boxed t))
eval env (Force t)         = force env =<< eval env t
eval _   (Require t (l,r)) = return (VRequire t (l,r))
eval _   (BelieveMe _)     = return VBelieveMe
eval _   (Impossible _)    = return VImpossibe

evalApp :: (MonadError String m, Eq n)
        => Env' n a -> Value n a -> Term n a -> m (Value n a)
evalApp env (VQ (Lam _ _) s) u = eval env (instantiate1Name u s)
evalApp _   (Neutral t) u      = return (Neutral (NApp t u))
evalApp _   _ _                = throwError ("evalApp: function expected")

evalSplit :: (MonadError String m, Eq n)
          => Env' n a
          -> (n,n)
          -> Value n a
          -> Scope (Name n Tup) (Term n) a
          -> m (Value n a)
evalSplit env _ (VPair l r) s = do
  eval env (instantiateName (\case {Fst -> l;Snd -> r}) s)
evalSplit _ xy (Neutral n) s = return (Neutral (NSplit n xy s))
evalSplit _ _ _ _ = throwError "evalSplit: Pair expected"

evalCase :: (MonadError String m, Eq n)
         => Env' n a
         -> Value n a
         -> [(n,Term n a)]
         -> m (Value n a)
evalCase env (VLabel l) as = case lookup l as of
  Just t  -> eval env t
  Nothing -> throwError "evalCase: case not matched"
evalCase _ (Neutral n) as = return (Neutral (NCase n as))
evalCase _ _ _ = throwError "evalCase: Label expected"

force :: (MonadError String m, Eq n)
      => Env' n a
      -> Value n a
      -> m (Value n a)
force env (VBox (Boxed c)) = eval env c
force _   (Neutral n)      = return (Neutral (NForce n))
force _   _                = throwError "force: Box expected"

defs :: Prog n a -> Int -> Scope (Name n Int) (Term n) a
defs ps i = snd . extract $ (ps!!i)

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
