{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures,
             NoMonomorphismRestriction, TupleSections, OverloadedStrings,
             ScopedTypeVariables, FlexibleContexts, GeneralizedNewtypeDeriving,
             Rank2Types, GADTs, LambdaCase, ViewPatterns, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}


import Bound
import Bound.Name
import Bound.Scope
import Bound.Var
import Control.Comonad
import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Data.Bifunctor
import Data.List
import Data.String
-- import Data.Functor.Invariant
import Prelude.Extras
import qualified Data.Set
import Debug.Trace

newtype Eval a = Eval { runEval :: (Except String a) }
  deriving (Functor, Applicative, Monad, MonadError String)

doEval :: Show a => Eval a -> IO ()
doEval t = case runExcept $ runEval t of
             Left s  -> putStrLn s
             Right a -> print a

data Term n a
  = Var !a
  | Type
  | Pi  (Name n (Term n a))         (Scope (Name n ()) (Term n) a)
  | Lam (Name n (Maybe (Term n a))) (Scope (Name n ()) (Term n) a)
  | Let !Int (Prog n a) (Scope (Name n Int) (Term n) a)
  | App (Term n a) (Term n a)
  | Sigma (Name n (Term n a))       (Scope (Name n ()) (Term n) a)
  | Pair (Term n a) (Term n a)
  | Split (Term n a) (n,n) (Scope (Name n Tup) (Term n) a)
  | Enum [n]
  | Label n
  | Case (Term n a) [(n,Term n a)]
  | Lift (Term n a)
  | Box (Term n a)
  | Force (Term n a)
  | Rec (Term n a)
  | Fold (Term n a)
  | Unfold (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  | BeleiveMe
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Tup = Fst | Snd
  deriving (Eq,Ord,Show)

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
bindTerm (Var x) f      = f x
bindTerm Type _         = Type
bindTerm (Pi tm s) f    = Pi (fmap (`bindTerm` f) tm) (s >>>= f)
bindTerm (Lam tmM s) f  = Lam ((fmap.fmap) (`bindTerm` f) tmM) (s >>>= f)
bindTerm (Let n p s) f  = Let n (bindProg p f) (s >>>= f)
bindTerm (App e u) f    = App (bindTerm e f) (bindTerm u f)
bindTerm (Sigma tm s) f = Sigma (fmap (`bindTerm` f) tm) (s >>>= f)
bindTerm (Pair l r) f   = Pair (bindTerm l f) (bindTerm r f)
bindTerm (Split t xy s) f = Split (bindTerm t f) xy (s >>>= f)
bindTerm (Enum ls) _    = Enum ls
bindTerm (Label l) _    = Label l
bindTerm (Case t as) f  = Case (bindTerm t f) (map (second (`bindTerm` f)) as)
bindTerm (Lift t) f     = Lift (bindTerm t f)
bindTerm (Box t) f      = Box (bindTerm t f)
bindTerm (Force t) f    = Force (bindTerm t f)
bindTerm (Rec t) f      = Rec (bindTerm t f)
bindTerm (Fold t) f     = Fold (bindTerm t f)
bindTerm (Unfold t s) f = Unfold (fmap (`bindTerm` f) t) (s >>>= f)
bindTerm BeleiveMe _    = BeleiveMe

bindProg :: Prog n a -> (a -> Term n b) -> Prog n b
bindProg ps f = map (fmap (bimap (>>>= f) (>>>= f))) ps

instance IsString a => IsString (Term n a) where
  fromString = Var . fromString

data Value n a
  = Neutral (Neutral n a)
  | VType
  | VPi    (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  | VLam   (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  | VSigma (Name n (Term n a)) (Scope (Name n ()) (Term n) a)
  | VPair  (Term n a) (Term n a)
  | VEnum [n]
  | VLabel n
  | VLift  (Type n a)
  | VBox   (Boxed n a)
  | VRec   (Type n a)
  | VFold  (Term n a)
  | VBeleiveMe
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

newtype Boxed n a = Boxed { unBoxed :: Term n a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Neutral n a
  = NVar a
  | NApp (Neutral n a) (Term n a)
  | NSplit (Neutral n a) (n,n) (Scope (Name n Tup) (Term n) a)
  | NCase (Neutral n a) [(n,Term n a)]
  | NForce (Neutral n a)
  | NUnfold (Name n (Neutral n a)) (Scope (Name n ()) (Term n) a)
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

emptyEnv :: Show a => Env f g a
emptyEnv = Env (\x -> error ("No declaration for: " ++ show x))
               (\x -> error ("No definition for: " ++ show x))

infer :: (Eq a, Eq n, Ord n, Show n, Show a)
      => Env (Term n) (EnvEntry' n) a
      -> Term n a
      -> Eval (Type n a)
infer env (Var x)   = return (ctx env x)
infer _   Type      = return Type
infer env (Pi tm s) = do
  check env (extract tm) Type
  let env' = extendEnvQ env (extract tm)
  check env' (fromScope s) Type
  return Type
infer env (Lam (Name n (Just tm)) s) = do
  check env tm Type
  let env' = extendEnvQ env tm
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
infer env (Sigma tm s) = do
  check env (extract tm) Type
  let env' = extendEnvQ env (extract tm)
  check env' (fromScope s) Type
  return Type
infer _ (Enum ls) = if nub ls /= ls
                       then throwError "infer: duplicate lables"
                       else return Type
infer env (Box t) = Lift <$> infer env t
infer env (Fold t) = Rec . Box <$> infer env t
infer env (Force t) = do
  a <- infer' env t
  case a of
    VLift b -> return b
    _       -> throwError "infer: expected Lifted type"
infer env (Lift a) = check env a Type >> return Type
infer env (Rec a) = check env a (Lift Type) >> return Type

infer _ (Lam _ _) = throwError "infer: cannot infer un-annotated Lambda"
infer _ (Pair _ _) = throwError "infer: cannot infer un-annotated Pair"
infer _ (Split _ _ _) = throwError "infer: cannot infer un-annotated Split"
infer _ (Label _) = throwError "infer: cannot infer un-annotated Label"
infer _ (Case _ _) = throwError "infer: cannot infer un-annotated Case"
infer _ (Unfold _ _) = throwError "infer: cannot infer un-annotated Unfold"
infer _ BeleiveMe = throwError "infer: cannot infer un-annotated BeleiveMe"

infer' :: (Eq a, Eq n, Ord n, Show n, Show a)
       => Env' n a
       -> Term n a
       -> Eval (Value n a)
infer' env tm = eval env =<< infer env tm

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

extendEnvSplit :: Eq a
               => Env' n a
               -> Type n a
               -> Scope (Name n ()) (Type n) a
               -> n -> n -> Maybe a
               -> Env' n (Var (Name n Tup) a)
extendEnvSplit (Env ctxOld defOld) tyA tyB x y mA = Env ctx' def'
  where
    ctx' (B (Name _ Fst)) = F <$> tyA
    ctx' (B (Name _ Snd)) = fromScope (mapBound (const (Name x Fst)) tyB)
    ctx' (F tm')  = F <$> ctxOld tm'

    def' b@(B _) = Id b
    def' (F tm')
      | Just tm' == mA = Cloj $ Pair (Var (B (Name x Fst))) (Var (B (Name y Snd)))
      | otherwise      = F <$> defOld tm'

extendEnvCase :: Eq a
              => Env' n a
              -> a -> n
              -> Env' n a
extendEnvCase env i l = env {def = def'}
  where
    def' a | a == i    = Cloj (Label l)
           | otherwise = def env a

extendEnvUnfold :: Eq a
                => Env' n a
                -> Type n a
                -> n
                -> Maybe a
                -> Env' n (Var (Name n ()) a)
extendEnvUnfold (Env ctxOld defOld) tyA tName tM = Env ctx' def'
  where
    ctx' (B _)   = F <$> Force tyA
    ctx' (F tm') = F <$> ctxOld tm'

    def' b@(B _) = Id b
    def' (F tm')
      | Just tm'  == tM = Cloj (Fold (Var (B (Name tName ()))))
      | otherwise       = F <$> defOld tm'

checkProg :: (Eq a, Eq n, Ord n, Show n, Show a)
          => Env' n a -> Prog n a
          -> Eval (Env' n (Var (Name n Int) a))
checkProg env p = do
  let env' = extendEnvLet env p
  mapM_ (checkProg' env' . bimap fromScope fromScope . extract) p
  return env'

checkProg' :: (Eq a, Eq n, Ord n, Show n, Show a)
           => Env' n a
           -> (Type n a, Term n a)
           -> Eval ()
checkProg' env (ty,tm) = do
  check env ty Type
  check env tm ty

check :: (Eq a, Eq n, Ord n, Show n, Show a)
      => Env' n a -> Term n a -> Term n a -> Eval ()
check env (Let _ p s) c = do
  env' <- checkProg env p
  check env' (fromScope s) (F <$> c)

check env (Split t (x,y) u) c = do
  sigmab <- infer' env t
  case sigmab of
    VSigma tyA tyB -> do
      t' <- eval env t
      let tM   = case t' of
                   Neutral (NVar i) -> Just i
                   _ -> Nothing
          env' = extendEnvSplit env (extract tyA) tyB x y tM
      check env' (fromScope u) (F <$> c)
    _ -> throwError ("check: Split: expected sigma: " ++ show sigmab)

check env (Case t as) c = do
  enum <- infer' env t
  case enum of
    VEnum ls ->
      let ls' = map fst as
      in  if (Data.Set.fromList ls) /= (Data.Set.fromList ls')
            then throwError ("check: Labels don't match: " ++ show (ls,ls'))
            else do
              t' <- eval env t
              case t' of
                Neutral (NVar i) ->
                  mapM_ (\(l,u) -> let env' = extendEnvCase env i l
                                   in  check env' u c) as
                _ -> mapM_ (\(_,u) -> check env u c) as
    _ -> throwError ("check: Case: expected Enum: " ++ show enum)

check env (Unfold t s) c = do
  vrec <- infer' env (extract t)
  case vrec of
    VRec a -> do
      t' <- eval env (extract t)
      let tM = case t' of
                 Neutral (NVar i) -> Just i
                 _ -> Nothing
          env' = extendEnvUnfold env a (name t) tM
      check env' (fromScope s) (F <$> c)
    _ -> throwError ("check: Unfold: expected Rec: " ++ show vrec)

check env (Force t) c = check env t (Lift c)

check env t a = check' env t =<< eval env a

check' :: (Eq a, Eq n, Ord n, Show n, Show a) => Env' n a -> Term n a -> Value n a -> Eval ()
check' env (Lam v s) (VPi ty s') = do
  maybe (return ()) (eq env (extract ty)) (extract v)
  let env' = extendEnvQ env (extract ty)
  check env' (fromScope s) (fromScope s')
check' _ (Lam _ _) v = throwError ("check': expected pi: " ++ show v)
check' env (Pair l r) (VSigma ty s) = do
  check env l (extract ty)
  let s' = instantiate1Name l s
  check env r s'
check' _ (Pair _ _) v = throwError ("check': expected sigma: " ++ show v)
check' _ (Label l) (VEnum ls) | l `elem` ls = return ()
check' _ (Label _) _ = throwError "check': Label"
check' env (Box t) (VLift a) = check env t a
check' env (Fold t) (VRec a) = check' env t =<< eval env (Force a)
check' _ BeleiveMe v = trace ("BeleiveMe: " ++ show v) (return ()) -- throwError ("BeleiveMe: " ++ show v)
check' env t a       = do b <- infer' env t
                          t' <- infer env t
                          catchError (eq env a b)
                                     (\s -> throwError (s ++ "\nt: " ++ show t' ++ "\na: " ++ show a))

eval :: (MonadError String m, Eq n)
     => Env' n a -> Term n a -> m (Value n a)
eval env (Var x)     = case def env x of
                         Cloj tm -> eval env tm
                         Id v    -> return (Neutral (NVar v))
eval _   Type        = return VType
eval _   (Pi v s)    = return (VPi v s)
eval _   (Lam v s)   = do v' <- sequence $
                                fmap (maybe
                                        (throwError "eval: un-annotated Lam")
                                        return)
                                     v
                          return (VLam v' s)
eval env (Let _ p s) = let inst = instantiateName es
                           es   = inst . defs p
                       in  eval env (inst s)
eval env (App t u)   = flip (evalApp env) u =<< eval env t
eval _   (Sigma v s) = return (VSigma v s)
eval _   (Pair l r)  = return (VPair l r)
eval env (Split t xy s) = flip (evalSplit env xy) s =<< eval env t
eval _   (Enum ls)   = return (VEnum ls)
eval _   (Label l)   = return (VLabel l)
eval env (Case t as) = flip (evalCase env) as =<< eval env t
eval _   (Lift t)    = return (VLift t)
eval _   (Box t)     = return (VBox (Boxed t))
eval env (Force t)   = force env =<< eval env t
eval _   (Rec t)     = return (VRec t)
eval _   (Fold t)    = return (VFold t)
eval env (Unfold t s) = flip (unfold env (name t)) s =<< eval env (extract t)
eval _   BeleiveMe   = return VBeleiveMe

evalApp :: (MonadError String m, Eq n)
        => Env' n a -> Value n a -> Term n a -> m (Value n a)
evalApp env (VLam _ s) u  = eval env (instantiate1Name u s)
evalApp _   (Neutral t) u = return (Neutral (NApp t u))
evalApp _   _ _           = throwError ("evalApp: function expected")

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

unfold :: (MonadError String m, Eq n)
       => Env' n a
       -> n
       -> Value n a
       -> Scope (Name n ()) (Term n) a
       -> m (Value n a)
unfold env _ (VFold c)    b = eval env (instantiate1Name c b)
unfold _   n (Neutral n') b = return (Neutral (NUnfold (Name n n') b))
unfold _   _ _            _ = throwError "unfold: Fold expected"

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
  eq env (VPi t0 s0)  (VPi t1 s1) = do
    eq env (extract t0) (extract t1)
    let env' = extendEnvQ env (extract t0)
    eq env' (fromScope s0) (fromScope s1)
  eq env (VLam v s0)  (VLam _ s1)  = do
    let env' = extendEnvQ env (extract v)
    eq env' (fromScope s0) (fromScope s1)
  eq env (VSigma t0 s0)  (VSigma t1 s1) = do
    eq env (extract t0) (extract t1)
    let env' = extendEnvQ env (extract t0)
    eq env' (fromScope s0) (fromScope s1)
  eq env (VPair u0 t0) (VPair u1 t1) =
    eq env u0 u1 >>
    eq env t0 t1
  eq env (VLift u0) (VLift u1) = eq env u0 u1
  eq env (VBox u0) (VBox u1) = eq env u0 u1
  eq env (VRec u0) (VRec u1) = eq env u0 u1
  eq env (VFold u0) (VFold u1) = eq env u0 u1
  eq _ v0 v1 | v0 == v1  = return ()
             | otherwise = throwError ("eq: Different values:" ++
                                       "\nv0: " ++ show v0 ++
                                       "\nv1: " ++ show v1)

instance Equal Neutral where
  eq _ (NVar i0) (NVar i1)
    | i0 == i1  = return ()
    | otherwise = throwError ("eq: Different variables: " ++ show (i0,i1))
    -- | otherwise = do
    --     let ei0 = def env i0
    --         ei1 = def env i1
    --     case (ei0,ei1) of
    --       (Id j0, Id j1) -> unless (j0 == j1) (throwError "eq: Different variables")
    --       (Cloj t0, Cloj t1) -> eq env t0 t1
    --       _ -> throwError "eq: Variable vs Neutral"
  eq env (NApp t0 u0) (NApp t1 u1) =
    eq env t0 t1 >>
    eq env u0 u1
  eq env (NSplit t0 _ u0) (NSplit t1 _ u1) = do
    eq env t0 t1
    let env' = Env (unvar (\n -> error (show (name n) ++ " undefined")) (fmap F . ctx env))
                   (unvar (Id . B) (fmap F . def env))
    eq env' (fromScope u0) (fromScope u1)
  eq env (NCase t0 as0) (NCase t1 as1) = do
    eq env t0 t1
    let eqBranches [] [] = return ()
        eqBranches ((l0,u0):lsu0) ((l1,u1):lsu1)
          | l0 == l1 = eq env u0 u1 >> eqBranches lsu0 lsu1
        eqBranches _ _ = throwError "eq: Case: branches differ"
    eqBranches as0 as1
  eq env (NForce t0) (NForce t1) = eq env t0 t1
  eq env (NUnfold t0 u0) (NUnfold t1 u1) = do
    eq env (extract t0) (extract t1)
    let env' = Env (unvar (\n -> error ("eq Neutral: " ++ show (name n) ++ " undefined")) (fmap F . ctx env))
               (unvar (Id . B) (fmap F . def env))
    eq env' (fromScope u0) (fromScope u1)
  eq _ n0 n1 = throwError ("eq: Different Neutrals: \nn0\n" ++ show n0 ++ "\nn1:\n" ++ show n1)

instance Equal Boxed where
  eq env (Boxed t0) (Boxed t1) = eqBox env t0 t1

eqBox :: (MonadError String m, Eq a, Eq n, Show n, Show a)
      => Env' n a
      -> Term n a -> Term n a
      -> m ()
eqBox env (Var i0) (Var i1)
  | i0 == i1  = return ()
  | otherwise = do
      let ei0 = def env i0
          ei1 = def env i1
      case (ei0,ei1) of
        (Id j0, Id j1) -> unless (j0 == j1) (throwError "eqBox: Different variables")
        (Cloj t0, Cloj t1) -> eq env t0 t1
        _ -> throwError "eqBox: Variable vs Neutral"
eqBox env (Let _ p t) c =
  let inst = instantiateName es
      es   = inst . defs p
  in  eq env (inst t) c
eqBox env c c'@(Let _ _ _) = eqBox env c' c
eqBox env (Pi t0 u0) (Pi t1 u1) = do
  eqBox env (extract t0) (extract t1)
  let env' = extendEnvQ env (extract t0)
  eq env' (Boxed (fromScope u0)) (Boxed (fromScope u1))
eqBox env (Sigma t0 u0) (Sigma t1 u1) = do
  eqBox env (extract t0) (extract t1)
  let env' = extendEnvQ env (extract t0)
  eq env' (Boxed (fromScope u0)) (Boxed (fromScope u1))
eqBox env (Lam t0 u0) (Lam t1 u1) = do
  v' <- runMaybeT $ do t0' <- MaybeT (return (extract t0))
                       t1' <- MaybeT (return (extract t1))
                       lift $ eq env t0' t1'
                       return t0'
  case v' of
    Just v'' -> let env' = extendEnvQ env v'' in eq env' (fromScope u0) (fromScope u1)
    _ -> throwError "eqBox: un-annotated Lambda"
eqBox env (App t0 u0) (App t1 u1) = eqBox env t0 t1 >> eqBox env u0 u1
eqBox env (Pair t0 u0) (Pair t1 u1) = eqBox env t0 t1 >> eqBox env u0 u1
eqBox env (Split t0 _ s0) (Split t1 _ s1) = do
  eqBox env t0 t1
  let env' = Env (unvar (\n -> error ("eqBox Split: " ++ show (name n) ++ " undefined")) (fmap F . ctx env))
                 (unvar (Id . B) (fmap F . def env))
  eq env' (Boxed (fromScope s0)) (Boxed (fromScope s1))
eqBox env (Case t0 as0) (Case t1 as1) =
  eqBox env t0 t1 >>
  zipWithM_ (\(l0,t0') (l1,t1') ->
              if l0 == l1 then eqBox env t0' t1'
                          else throwError "eqBox Case"
            ) as0 as1
eqBox env (Lift t0) (Lift t1) = eqBox env t0 t1
eqBox env (Box t0) (Box t1) = eqBox env t0 t1
eqBox env (Force t0) (Force t1) = eqBox env t0 t1
eqBox env (Rec t0) (Rec t1) = eqBox env t0 t1
eqBox env (Fold t0) (Fold t1) = eqBox env t0 t1
eqBox env (Unfold t0 u0) (Unfold t1 u1) = do
  eqBox env (extract t0) (extract t1)
  let env' = Env (unvar (\n -> error ("eqBox Unfold: " ++ show (name n) ++ " undefined")) (fmap F . ctx env))
                 (unvar (Id . B) (fmap F . def env))
  eq env' (Boxed (fromScope u0)) (Boxed (fromScope u1))
eqBox _ t0 t1 | t0 == t1  = return () -- Type, Label, Enum
              | otherwise = throwError "eqBox: Different terms"

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

sigma :: Eq a => (a,Type a a) -> Term a a -> Term a a
sigma (v,b) e = Sigma (Name v b) (abstract1Name v e)

app :: Term n a -> [Term n a] -> Term n a
app f args = foldl App f args

split :: Eq a => Term a a -> (a,a) -> Term a a -> Term a a
split t (x,y) u = Split t (x,y) (abstractName (\z -> if z == x then Just Fst else if z == y then Just Snd else Nothing) u)

unfold_ :: Eq a => Term a a -> a -> Term a a -> Term a a
unfold_ t v u = Unfold (Name v t) (abstract1Name v u)

unfold' :: (Eq a, IsString a) => Term a a -> Term a a
unfold' t     = unfold_ t "x_unfold" "x_unfold"

(->-) :: Term String String -> Term String String -> Term String String
(->-) t = pi_ ("",t)
infixr 5 ->-

(-*-) :: Term String String -> Term String String -> Term String String
(-*-) t = sigma ("",t)
infixr 4 -*-

test :: Term String String
test = let_ [("Eq"
             ,pi_ ("a",Type) (pi_ ("","a") (pi_ ("","a") Type))
             ,lam' "a" Type (lam' "x" "a" (lam' "y" "a" (pi_ ("P",pi_ ("","a") Type) (pi_ ("",App "P" "x") (App "P" "y"))))))
            ,("refl"
             ,pi_ ("a",Type) (pi_ ("x","a") (app "Eq" ["a","x","x"]))
             ,lam' "a" Type (lam' "x" "a" (lam' "P" (pi_ ("","a") Type) (lam' "px" (App "P" "x") "px")))
             )
            ,("A"
             ,Type
             ,Type
             )
            ,("a"
             ,"a"
             ,Type
             )
            ,("b"
             ,"A"
             ,"a"
             )
            ,("t0"
             ,app "Eq" ["A","a","b"]
             ,app "refl" ["A","a"]
             )
            ]
       (Var "t0")

empty :: [(String,Type String String,Term String String)]
empty = [("Empty",Type,Enum [])]

unit :: [(String,Type String String,Term String String)]
unit  = [("Unit",Type,Enum ["unit"])]

bool :: [(String,Type String String,Term String String)]
bool  = empty ++ unit ++
        [("Bool",Type,Enum ["true","false"])
        ,("T"
         ,"Bool" ->- Type
         ,lam' "b" ("Bool")
                  (Case (Var "b") [("true","Unit")
                                  ,("false","Empty")])
         )
        ]

nat :: [(String,Type String String,Term String String)]
nat   = bool ++
        [("Nat"
         ,Type
         ,sigma ("l",Enum ["z","s"]) (Case "l" [("z","Unit")
                                               ,("s",Rec (Box "Nat"))])
         )
        ,("zero"
         ,"Nat"
         ,Pair (Label "z") (Label "unit"))
        ,("suc"
         ,"Nat" ->- "Nat"
         ,lam' "n" "Nat" $ Pair (Label "s") (Fold "n")
         )
        ,("eqNat"
         ,"Nat" ->- "Nat" ->- "Bool"
         ,lam' "m" "Nat" $
          lam' "n" "Nat" $
          split "m" ("lm","m'") $
          split "n" ("ln","n'") $
          Force (Case "lm" [("z",Case "ln" [("z",Box $ Label "true")
                                           ,("s",Box $ Label "false")])
                           ,("s",Case "ln" [("z",Box $ Label "false")
                                           ,("s",Box $ app "eqNat" [unfold' "m'",unfold' "n'"])
                                           ])
                           ])
         )
        ,("EqNat"
         ,"Nat" ->- "Nat" ->- Type
         ,lam' "m" "Nat" $ lam' "n" "Nat" $ App "T" (app "eqNat" ["m","n"])
         )
        ,("reflNat"
         ,pi_ ("n","Nat") (app "EqNat" ["n","n"])
         ,lam' "n" "Nat" $ split "n" ("nl","n'") $
            Force (Case "nl" [("z",Box (Label "unit"))
                             ,("s",Box (App "reflNat" (unfold' "n'")))
                             ])
         )
        ,("substNat"
         ,pi_ ("P","Nat" ->- Type) $ pi_ ("m","Nat") $ pi_ ("n","Nat") $
          app "EqNat" ["m","n"] ->- App "P" "m" ->- App "P" "n"
         ,lam' "P" ("Nat" ->- Type) $ lam' "m" "Nat" $ lam' "n" "Nat" $
          lam' "q" (app "EqNat" ["m","n"]) $ lam' "x" (App "P" "m") $
          split "m" ("lm","m'") $
          split "n" ("ln","n'") $ Force $
            Case "lm" [("z",Case "ln" [("z",Case "m'" [("unit",Case "n'" [("unit",Box "x")])])
                                      ,("s",Case "q" [])
                                      ])
                      ,("s",Case "ln" [("z",Case "q" [])
                                      ,("s",Box $
                                            unfold_ "m'" "m'" $
                                            unfold_ "n'" "n'" $
                                            app "substNat" [lam' "i" "Nat" (App "P" (App "suc" "i"))
                                                           ,"m'","n'","q","x"])])]
         )
        ,("symNat"
         ,pi_ ("m","Nat") $ pi_ ("n","Nat") $ app "EqNat" ["m","n"] ->-
          app "EqNat" ["n","m"]
         ,lam' "m" "Nat" $ lam' "n" "Nat" $ lam' "p" (app "EqNat" ["m","n"]) $
          app "substNat" [lam' "i" "Nat" $ app "EqNat" ["i","m"]
                         ,"m","n","p",App "reflNat" "m"]
         )
        ,("transNat"
         ,pi_ ("i","Nat") $ pi_ ("j","Nat") $ pi_ ("k","Nat") $
          app "EqNat" ["i","j"] ->- app "EqNat" ["j","k"] ->- app "EqNat" ["i","k"]
         ,lam' "i" "Nat" $ lam' "j" "Nat" $ lam' "k" "Nat" $
          lam' "p" (app "EqNat" ["i","j"]) $ lam' "q" (app "EqNat" ["j","k"]) $
          app "substNat" [lam' "x" "Nat" $ app "EqNat" ["i","x"]
                         ,"j","k","q","p"
                         ]
         )
        ]

fin :: [(String,Type String String,Term String String)]
fin = nat ++
      [("Fin"
       ,"Nat" ->- Type
       ,lam' "n" "Nat" $ split "n" ("ln","n'") $ Force $
          Case "ln" [("z",Box "Empty")
                    ,("s",Box (sigma ("l",Enum ["z","s"]) $
                        Case "l" [("z","Unit")
                                 ,("s",App "Fin" (unfold' "n'"))]))
                    ]
       )
      ]

vec :: [(String,Type String String,Term String String)]
vec = fin ++
      [("Vec"
       ,"Nat" ->- Type ->- Type
       ,lam' "m" "Nat" $ lam' "a" Type $ split "m" ("lm","m'") $ Force $
          Case "lm" [("z",Box "Unit")
                    ,("s",Box ("a" -*- app "Vec" [unfold' "m'","a"]))
                    ]
       )
      ,("nth"
       ,pi_ ("a",Type) $ pi_ ("n","Nat") $ app "Vec" ["n","a"] ->- App "Fin" "n" ->- "a"
       ,lam' "a" Type $ lam' "n" "Nat" $ lam' "xs" (app "Vec" ["n","a"]) $ lam' "i" (App "Fin" "n") $
          split "n" ("ln","n'") $ Force $
          Case "ln" [("z",Case "i" [])
                    ,("s",split "xs" ("x","xs'") $ split "i" ("li","i'") $
                        Case "li" [("z",Box "x")
                                  ,("s",Box (app "nth" ["a",unfold' "n'", "xs'", "i'"]))
                                  ]
                      )
                    ]
       )
      ]

fin' :: [(String,Type String String,Term String String)]
fin'   = nat ++
        [("Fin"
         ,"Nat" ->- Type
         ,lam' "n" "Nat" $ sigma ("l",Enum ["z","s"]) $
            Case "l" [("z",sigma ("n'","Nat") (app "EqNat" [App "suc" "n'","n"]))
                     ,("s",sigma ("n'","Nat") (Rec (Box (App "Fin" "n'")) -*- app "EqNat" [App "suc" "n'","n"]))
                     ]
         )
        ]

vec' :: [(String,Type String String,Term String String)]
vec'   = fin' ++
        [("Vec"
         ,"Nat" ->- Type ->- Type
         ,lam' "n" "Nat" $ lam' "A" Type $ sigma ("l",Enum ["nil","cons"]) $
            Case "l" [("nil",app "EqNat" ["zero","n"] )
                     ,("cons",sigma ("n'","Nat") ("A" -*- Rec (Box (app "Vec" ["n'","A"])) -*- app "EqNat" [App "suc" "n'","n"]))
                     ]
         )
        ,("nil"
         ,pi_ ("A",Type) $ app "Vec" ["zero","A"]
         ,lam' "A" Type $ Pair (Label "nil") (App "reflNat" "zero")
         )
        ,("cons"
         ,pi_ ("n","Nat") $ pi_ ("A",Type) $ "A" ->- app "Vec" ["n","A"] ->- app "Vec" [App "suc" "n","A"]
         ,lam' "n" "Nat" $ lam' "A" Type $ lam' "a" "A" $ lam' "v" (app "Vec" ["n","A"]) $
            Pair (Label "cons") (Pair "n" (Pair "a" (Pair (Fold "v") (App "reflNat" (App "suc" "n")))))
         )
        ,("lookup"
         ,pi_ ("A",Type) $ pi_ ("n","Nat") $ (App "Fin" "n") ->- (app "Vec" ["n","A"]) ->- "A"
         ,lam' "A" Type $ lam' "n" "Nat" $ lam' "i" (App "Fin" "n") $ lam' "xs" (app "Vec" ["n","A"]) $
            split "i" ("li","i'") $ Force $
              Case "li" [("s",split "i'" ("fn","i''") $ split "i''" ("fr","feq") $
                            split "xs" ("xc","xs'") $
                              Case "xc" [("cons",split "xs'" ("xn","xs''") $ split "xs''" ("xa","xs3") $
                                                 split "xs3" ("xr","xseq") $ Box $
                                                 app "lookup" ["A","fn",(unfold' "fr"),
                                                    app "substNat" [lam' "k" "Nat" (app "Vec" ["k","A"])
                                                                   ,"xn","fn"
                                                                   ,app "transNat" [App "suc" "xn","n",App "suc" "fn"
                                                                                   ,"xseq"
                                                                                   ,app "symNat" [App "suc" "fn","n","feq"]
                                                                                   ]
                                                                   ,unfold' "xr"]])
                                        ,("nil",Case (app "substNat" [lam' "k" "Nat" (app "EqNat" ["zero","k"]),"n",App "suc" "fn"
                                                                        ,app "symNat" [App "suc" "fn","n","feq"]
                                                                        ,"xs'"]) [])])
                        ,("z",split "i'" ("fn","feq") $ split "xs" ("xc","xs'") $
                                Case "xc" [("cons",split "xs'" ("xn","xbs") $ split "xbs" ("xa","xb") $ Box "xa")
                                          ,("nil" ,Case (app "substNat" [lam' "k" "Nat" (app "EqNat" ["zero","k"]),"n",App "suc" "fn"
                                                                        ,app "symNat" [App "suc" "fn","n","feq"]
                                                                        ,"xs'"]) [])
                                          ])
                        ]
         )
          ,("tail"
           ,pi_ ("n","Nat") $ pi_ ("a",Type) $ app "Vec" [App "suc" "n","a"] ->- app "Vec" ["n","a"]
           ,lam' "n" "Nat" $ lam' "a" Type $ lam' "as" (app "Vec" [App "suc" "n","a"]) $
            split "as" ("l","as'") $ Force $
            Case "l" [("cons",split "as'" ("m","abs") $ split "abs" ("a'","bsn") $
                       split "bsn" ("bs","n'") $
                       Box (app "substNat" [lam' "x" "Nat" (app "Vec" ["x","a"])
                                           ,"m"
                                           ,"n"
                                           ,"n'"
                                           ,unfold' "bs"]
                                           ))
                     ,("nil",Case "as'" [])
                     ]
           )
        ]

test1 :: Term String String
test1 = let_ vec' "tail"
