module Check where

import Bound
import Bound.Name
import Control.Comonad
import Control.Monad.Except
import Data.Bifunctor
import Data.List
import Data.Set as Set

import Core
import Environment
import Evaluate

duplicateLabels :: Show n => [n] -> Eval a
duplicateLabels ls = throwError ("duplicate labels: " ++ show ls)

declaredTwice :: Show n => Name n b -> Eval a
declaredTwice n = throwError ("declared twice: " ++ show (name n))

-- * Checking

checkProg :: (Show n, Eq n, Show a)
          => Env Eval (Term n) (Value Eval n) a -> Int -> Prog n a
          -> Eval (Env Eval (Term n) (Value Eval n) (Var (Name n Int) a))
checkProg env n p@(p0,ps) = do
  undefined
  let (ty0,tm0) = extract p0
      env'      = extendEnvLet env n p
  check env ty0 Type
  check env' (fromScope tm0) (fmap F ty0)
  mapM_ (checkProg' env' . bimap fromScope fromScope . extract) ps
  return env'

checkProg' :: (Show n,Eq n,Show a)
           => Env Eval (Term n) (Value Eval n) a
           -> (Type n a, Term n a)
           -> Eval ()
checkProg' env (ty,tm) = do
  check env ty Type
  check env tm ty

check :: (Show n,Eq n,Show a)
      => Env Eval (Term n) (Value Eval n) a
      -> Term n a
      -> Type n a
      -> Eval ()
check env (Let n p s) c = do
  env' <- checkProg env n p
  check env' (fromScope s) (fmap F c)

check env (Split t s) c =
  do sigmab <- infer' env t
     undefined
     -- case sigmab of
     --   VBind (Sigma v) f -> do


-- * Inferring

infer :: (Eq n, Show n, Show a)
      => Env Eval (Term n) (Value Eval n) a
      -> Term n a
      -> Eval (Type n a)
infer env (Var a) = lookupTyp env a

infer env (Bind (Pi b) s) = do
  let ty = extract b
  check env ty Type
  let env' = extendEnv env ty
  check env' (fromScope s) Type
  return Type

infer env (Bind (Sigma b) s) = do
  let ty = extract b
  check env ty Type
  let env' = extendEnv env ty
  check env' (fromScope s) Type
  return Type

infer env (Let n p s) = do
  env' <- checkProg env n p
  t <- infer env' (fromScope s)
  return (Let n p (toScope t))

infer env (App t u) = error "infer App: undefined"

infer _ Type = pure Type

infer _ (HardTerm h) = inferHardTerm h

infer _ (Enum ls) = if length (nub ls) < length ls
                       then duplicateLabels ls
                       else return Type

infer env (Lift t) = do check env t Type
                        return Type

infer env (Box t) = infer env t

infer env (Force  _) = error "infer Force: undefined"

infer env (Rec t) = do check env t (Lift Type)
                       return Type

infer _ t = throwError ("Not inferable: " ++ show t)

inferHardTerm (String _)  = pure (HardTerm StringT)
inferHardTerm (Integer _) = pure (HardTerm IntegerT)
inferHardTerm StringT     = pure Type
inferHardTerm IntegerT    = pure Type

infer' :: (Eq n, Show n, Show a)
       => Env Eval (Term n) (Value Eval n) a
       -> Term n a
       -> Eval (Value Eval n)
infer' env tm = eval env =<< infer env tm
