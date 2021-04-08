{-# LANGUAGE BangPatterns, ScopedTypeVariables, GADTs, GeneralizedNewtypeDeriving #-}
module Eval where

import Prog
import Twee.Pretty
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Typeable
import Data.Maybe

data Some f where
  Some :: Type a => f a -> Some f

args :: Prog -> [Some Var]
args (Arg x _ prog) = Some x:args prog
args (Body _) = []

body :: Prog -> Stmt
body (Arg _ _ prog) = body prog
body (Body stmt) = stmt

newtype Env = Env { unEnv :: Map String (Some Identity) }
  deriving Pretty
instance Show Env where show = prettyShow

insertEnv :: Type a => Var a -> a -> Env -> Env
insertEnv (Var x) v (Env env) = Env (Map.insert x (Some (Identity v)) env)

lookupEnv :: Type a => Var a -> Env -> a
lookupEnv (Var x) (Env env) =
  case Map.findWithDefault (error "variable not bound") x env of
    Some (Identity v) ->
      fromMaybe (error "ill-typed variable") $ cast v

boundEnv :: Env -> [Some Var]
boundEnv (Env env) = map toVar (Map.toList env)
  where
    toVar (x, Some (_ :: Identity a)) =
      Some (Var x :: Var a)

class Pretty1 f where
  pPrintPrec1 :: Pretty a => PrettyLevel -> Rational -> f a -> Doc

instance Pretty1 Identity where
  pPrintPrec1 l p (Identity x) = pPrintPrec l p x

instance Pretty1 f => Pretty (Some f) where
  pPrintPrec l p (Some x) = pPrintPrec1 l p x

instance Show1 f => Show (Some f) where
  showsPrec p (Some x) = showsPrec1 p x

exec :: Env -> Stmt -> ([(String, Env)], Env)
exec env (x := e) =
  ([], insertEnv x (eval env e) env)
exec env Skip = ([], env)
exec env (p `Then` q) =
  let
    (envs1, env1) = exec env p
    (envs2, env2) = exec env1 q
  in (envs1 ++ envs2, env2)
exec env (If e p1 p2) =
  if eval env e
  then exec env p1
  else exec env p2
exec env (While e1 e2 p) =
  if eval env e2 then
    if eval env e1
    then exec env (p `Then` While e1 e2 p)
    else exec env Skip
  else error "invariant false"
exec env (Assert e) =
  if eval env e
  then ([], env)
  else error "assertion failed"
exec env (Point msg) =
  ([(msg, env)], env)

eval :: Env -> Expr a -> a
eval _ (Value x) =
  x
eval env (Local x) =
  lookupEnv x env
eval env (Not e) =
  not (eval env e)
eval env (And e1 e2) =
  eval env e1 && eval env e2
eval env (Or e1 e2) =
  eval env e1 || eval env e2
eval env (Plus e1 e2) =
  eval env e1 + eval env e2
eval env (Minus e1 e2) =
  eval env e1 - eval env e2
eval env (Div e1 e2) =
  eval env e1 `safeDiv` eval env e2
  where
    safeDiv _ 0 = 0
    safeDiv x y = x `div` y
eval env (Rel r e1 e2) =
  evalRel r (eval env e1) (eval env e2)
eval env (Pairwise r e1 e2) =
  and [evalRel r x y | x <- xs, y <- ys]
  where
    !xs = Set.toList (eval env e1)
    !ys = Set.toList (eval env e2)
eval env (Ordered r e) =
  and [evalRel r x y | (i, x) <- xs, (j, y) <- xs, i < j]
  where
    !xs = Map.toList (arrayContents (eval env e))
eval env (At e1 e2) =
  index (eval env e2) (eval env e1)
  where
    index i arr =
      Map.findWithDefault 0 i (arrayContents arr)
eval env (Update e1 e2 e3)
  | idx < 0 || idx >= arrayLength arr = arr
  | otherwise = arr {
      arrayContents =
          Map.insert idx val (arrayContents arr) }
  where
    !arr = eval env e1
    !idx = eval env e2
    !val = eval env e3
eval env (Length e) =
  arrayLength (eval env e)
eval env (Image e) =
  Set.fromList (Map.elems (arrayContents (eval env e)))
eval env (Concat e1 e2) =
  Array (len1 + len2) (xs1 `Map.union` Map.mapKeys (+ len1) xs2)
  where
    !(Array len1 xs1) = eval env e1
    !(Array len2 xs2) = eval env e2
eval env (Restrict e1 e2) =
  arr {
    arrayContents = Map.restrictKeys (arrayContents arr) set }
  where
    !arr = eval env e1
    !set = eval env e2
eval env (Union e1 e2) =
  Set.union (eval env e1) (eval env e2)
eval env (Interval e1 e2) =
  Set.fromList [eval env e1..eval env e2-1]
eval env (Singleton e) =
  Set.singleton $! eval env e
eval env (Null e) =
  Set.null (eval env e)

evalRel :: (Ord a, Num a) => Relation -> a -> a -> Bool
evalRel Eq = (==)
evalRel Ne = (/=)
evalRel Lt = (<)
evalRel Le = (<=)
evalRel Gt = (>)
evalRel Ge = (>=)

postOf :: Prog -> Env -> Env
postOf prog env = snd (exec env (body prog))

checkEnv :: Prog -> Env -> Bool
checkEnv (Arg _ cond prog) env =
  eval env cond && checkEnv prog env
checkEnv (Body _) _ = True

preProg :: Prog -> Expr Bool
preProg (Arg _ cond prog) = cond &&& preProg prog
preProg (Body stmt) = pre stmt
  
pre :: Stmt -> Expr Bool
pre stmt = fst (pre' stmt)
  where
    -- Boolean: was the statement side effect-free?
    pre' (_ := _) = (true, False)
    pre' Skip = (true, True)
    pre' (p `Then` q) =
      case pre' p of
        (e, False) -> (e, False)
        (e, True) ->
          let (e', b) = pre' q in
          (e &&& e', b)
    pre' (If cond p q) =
      let
        (e1, b1) = pre' p
        (e2, b2) = pre' q
      in ((cond ==> e1) &&& (nott cond ==> e2), b1 && b2)
    pre' (While _ e _) = (true, False)
    pre' (Assert e) = (e, True)
    pre' (Point _) = (true, True)
