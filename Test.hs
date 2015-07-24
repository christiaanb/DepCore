{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings,
             ScopedTypeVariables, FlexibleContexts, GeneralizedNewtypeDeriving,
             Rank2Types, GADTs, LambdaCase, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}


import Bound
import Bound.Name
import Control.Comonad
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Data.List
-- import Data.Functor.Invariant
import Prelude.Extras

newtype Eval a = Eval { runEval :: (Except String a) }
  deriving (Functor, Applicative, Monad, MonadError String)

data Term n a
  = Var !a
  | Type
  | Pi  (Name n (Term n a))         (Scope (Name n ()) (Term n) a)
  | Lam (Name n (Maybe (Term n a))) (Scope (Name n ()) (Term n) a)
  | Let !Int (Prog n a) (Scope (Name n Int) (Term n) a)
  | App (Term n a) (Term n a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Eq n => Eq1 (Term n)
instance Ord n => Ord1 (Term n)
instance Show n => Show1 (Term n)

type Type n = Term n

type Prog n a = [Name n ( Scope (Name n Int) (Type n) a
                        , Scope (Name n Int) (Term n) a)]


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
bindTerm (Lam tmM s) f = Lam ((fmap.fmap) (`bindTerm` f) tmM) (s >>>= f)
bindTerm (Let n p s) f = Let n (bindProg p f) (s >>>= f)
bindTerm (App e u) f   = App (bindTerm e f) (bindTerm u f)

bindProg :: Prog n a -> (a -> Term n b) -> Prog n b
bindProg ps f = map (fmap (bimap (>>>= f) (>>>= f))) ps

data Value n a
  = Neutral (Neutral n a)
  | VType
  | VPi  (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  | VLam (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Neutral n a
  = NVar a
  | NApp (Neutral n a) (Term n a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Eq n => Eq1 (Value n)
instance Ord n => Ord1 (Value n)
instance Show n => Show1 (Value n)

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

emptyEnv :: Env f g a
emptyEnv = Env (error "aap") (error "noot")

infer :: (Eq a, Eq n, Show n, Show a)
      => Env (Term n) (EnvEntry' n) a
      -> Term n a
      -> Eval (Type n a)
infer env (Var x)   = return (ctx env x)
infer _   Type      = return Type
infer env (Pi tm s) = do
  check env (extract tm) Type
  let env' = extendEnvPi env (extract tm)
  check env' (fromScope s) Type
  return Type
infer env (Lam (Name n (Just tm)) s) = do
  check env tm Type
  let env' = extendEnvPi env tm
  s' <- infer env' (fromScope s)
  return (Pi (Name n tm) (toScope s'))
infer env (Let n p s) = do
  env' <- checkProg env p
  s' <- infer env' (fromScope s)
  return (Let n p (toScope s'))
infer env (App t u) = do
  infer' env t >>= \case
    VPi v s -> do check env u (extract v)
                  return (instantiate1Name u s)
    _ -> throwError "infer: expected pi"
infer _ (Lam _ _) = throwError "infer: cannot infer un-annotated Lambda"

infer' :: (Eq a, Eq n, Show n, Show a)
       => Env' n a
       -> Term n a
       -> Eval (Value n a)
infer' env tm = eval env =<< infer env tm

extendEnvPi :: Env' n a
            -> Term n a
            -> Env' n (Var (Name n ()) a)
extendEnvPi (Env ctxOld defOld) tm = Env ctx' def'
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


checkProg :: (Eq a, Eq n, Show n, Show a)
          => Env' n a -> Prog n a
          -> Eval (Env' n (Var (Name n Int) a))
checkProg env p = do
  let env' = extendEnvLet env p
  mapM_ (checkProg' env' . bimap fromScope fromScope . extract) p
  return env'

checkProg' :: (Eq a, Eq n, Show n, Show a)
           => Env' n a
           -> (Type n a, Term n a)
           -> Eval ()
checkProg' env (ty,tm) = do
  check env ty Type
  check env tm ty

check :: (Eq a, Eq n, Show n, Show a) => Env' n a -> Term n a -> Term n a -> Eval ()
check env (Let _ p s) c = do
  env' <- checkProg env p
  check env' (fromScope s) (F <$> c)

check env t a = check' env t =<< eval env a

check' :: (Eq a, Eq n, Show n, Show a) => Env' n a -> Term n a -> Value n a -> Eval ()
check' env (Lam v s) (VPi ty s') = do
  maybe (return ()) (eq env (extract ty)) (extract v)
  let env' = extendEnvPi env (extract ty)
  check env' (fromScope s) (fromScope s')
check' _ (Lam _ _) v = throwError ("check': expected pi: " ++ show v)
check' env t a       = do b <- infer' env t
                          eq env a b

eval :: MonadError String m => Env' n a -> Term n a -> m (Value n a)
eval env (Var x)     = case def env x of
                         Cloj tm -> eval env tm
                         Id v    -> return (Neutral (NVar v))
eval _   Type        = return VType
eval _   (Pi v s)    = return (VPi v s)
eval _   (Lam v s)   = return (VLam (fmap (maybe (error "eval: unannotated Lam") id) v) s)
eval env (Let _ p s) = let inst = instantiateName es
                           es   = inst . defs p
                       in  eval env (inst s)
eval env (App t u)   = flip (evalApp env) u =<< eval env t

evalApp :: MonadError String m => Env' n a -> Value n a -> Term n a -> m (Value n a)
evalApp env (VLam _ s) u  = eval env (instantiate1Name u s)
evalApp _   (Neutral t) u = return (Neutral (NApp t u))
evalApp _   _ _           = throwError ("evalApp: function expected")

defs :: Prog n a -> Int -> Scope (Name n Int) (Term n) a
defs ps i = snd . extract $ (ps!!i)

class Equal f where
  eq :: (MonadError String m, Eq a, Eq n, Show n, Show a) => Env' n a -> f n a -> f n a -> m ()

instance Equal Term where
  eq env t1 t2 = do
    e1 <- eval env t1
    e2 <- eval env t2
    eq env e1 e2

instance Equal Value where
  eq env (Neutral n1) (Neutral n2) = eq env n1 n2
  eq env (VPi t0 s0)  (VPi t1 s1)  = do
    eq env (extract t0) (extract t1)
    let env' = extendEnvPi env (extract t0)
    eq env' (fromScope s0) (fromScope s1)
  eq env (VLam _ s0)  (VLam _ s1)  = do
    let env' = extendEnvPi env (error "eq: VLAM")
    eq env' (fromScope s0) (fromScope s1)
  eq _ v0 v1 | v0 == v1  = return ()
             | otherwise = throwError ("eq: Different values:" ++ show (v0,v1) )

instance Equal Neutral where
  eq _ (NVar i0) (NVar i1)
    | i0 == i1  = return ()
    | otherwise = throwError "eq: Different variables"
    -- | otherwise = do
    --     let ei0 = def env i0
    --         ei1 = def env i1
    --     case (ei0,ei1) of
    --       (Id j0, Id j1) -> unless (j0 == j1) (throwError "eq: Different variables")
    --       (Cloj t0, Cloj t1) -> eq env t0 t1
    --       _ -> throwError "eq: Variable vs Neutral"
  eq env (NApp t0 u0) (NApp t1 u1) = do
    eq env t0 t1
    eq env u0 u1
  eq _ _ _ = throwError "eq: Different Neutrals"

let_ :: Eq a => [(a,Type a a,Type a a)] -> Term a a -> Term a a
let_ []   b = b
let_ bs   b = Let (length bs) (map mkP bs) (abstr b)
  where
    as    = map (\(x,_,_) -> x) bs
    abstr = abstractName (`elemIndex` as)
    mkP (nm,ty,tm) = Name nm (abstr ty,abstr tm)

lam :: Eq a => a -> Term a a -> Term a a
lam v e = Lam (Name v Nothing) (abstract1Name v e)

lam' :: Eq a => a -> Type a a -> Term a a -> Term a a
lam' v t e = Lam (Name v (Just t)) (abstract1Name v e)

pi_ :: Eq a => (a,Type a a) -> Term a a -> Term a a
pi_ (v,b) e = Pi (Name v b) (abstract1Name v e)

app :: Term n a -> [Term n a] -> Term n a
app f args = foldl App f args

test :: Term String String
test = let_ [("Eq"
             ,pi_ ("a",Type) (pi_ ("",Var "a") (pi_ ("",Var "a") Type))
             ,lam' "a" Type (lam' "x" (Var "a") (lam' "y" (Var "a") (pi_ ("P",pi_ ("",Var "a") Type) (pi_ ("",App (Var "P") (Var "x")) (App (Var "P") (Var "y")))))))
            ,("refl"
             ,pi_ ("a",Type) (pi_ ("x",Var "a") (app (Var "Eq") [Var "a",Var "x",Var "x"]))
             ,lam' "a" Type (lam' "x" (Var "a") (lam' "P" (pi_ ("",Var "a") Type) (lam' "px" (App (Var "P") (Var "x")) (Var "px"))))
             )
            ,("A"
             ,Type
             ,Type
             )
            ,("a"
             ,Var "a"
             ,Type
             )
            ,("b"
             ,Var "A"
             ,Var "a"
             )
            ,("t0"
             ,app (Var "Eq") [Var "A",Var "a",Var "b"]
             ,app (Var "refl") [Var "A",Var "a"]
             )
            ]
       (Var "t0")
