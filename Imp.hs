{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators, MultiParamTypeClasses #-}
module Imp where

import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as Map
import Data.Map(Map)

data Prog =
    If Exp Prog Prog
  | While Exp Prog
  | Prog `Then` Prog
  | Skip
  | Point
  | Var := Exp
  deriving (Eq, Ord, Show)

infixr 4 `Then`
infix 5 :=

type Var = String

data Val = Bool Bool | Int Int | Array [Int]
  deriving (Eq, Ord, Show)

data Exp =
    Val Val
  | Var Var
  | Not Exp
  | Len Var
  | Exp :&&: Exp
  | Exp :=: Exp
  | Exp :<: Exp
  | Exp :/: Exp
  | Exp :+: Exp
  | Var :@: Exp
  deriving (Eq, Ord, Show)

infix 6 :&&:
infix 6 :=:
infix 6 :<:
infix 6 :/:
infixr 6 :+:
infix 7 :@:

type Env = Map Var Val

bsearch :: Prog
bsearch =
  "lo" := Val (Int 0) `Then`
  "hi" := Len "arr" `Then`
  "found" := Val (Bool False) `Then`
  While (Not (Var "found") :&&: Not (Var "lo" :=: Var "hi"))
    (Point `Then`
     "mid" := (Var "lo" :+: Var "hi") :/: Val (Int 2) `Then`
     If (Var "x" :<: "arr" :@: Var "mid")
       ("hi" := Var "mid")
       (If ("arr" :@: Var "mid" :<: Var "x")
         ("lo" := Var "mid" :+: Val (Int 1))
         ("found" := Val (Bool True) `Then` "idx" := Var "mid")))

run :: Prog -> Env -> Env
run p env = execState (exec (return ()) p) env

collect :: Prog -> Env -> [Env]
collect p env =
  execWriter (execStateT (exec (get >>= tell . return) p) env)

test =
  collect bsearch $ Map.fromList
    [("x", Int 8),
     ("arr", Array [0,2,3,5,8,9])]

exec :: MonadState Env m => m () -> Prog -> m ()
exec point (If e p1 p2) = do
  Bool x <- evalM e
  if x then exec point p1 else exec point p2
exec point (While e p) = do
  Bool x <- evalM e
  when x $ do { exec point p; exec point (While e p) }
exec point (p1 `Then` p2) = do
  exec point p1
  exec point p2
exec _ Skip = return ()
exec point Point = point
exec _ (x := e) = do
  y <- evalM e
  modify (Map.insert x y)

evalM :: MonadState Env m => Exp -> m Val
evalM exp = do
  env <- get
  return (eval env exp)

eval :: Env -> Exp -> Val
eval _ (Val x) = x
eval env (Var x) = Map.findWithDefault undefined x env
eval env (Len x) =
  let Array xs = Map.findWithDefault undefined x env
  in Int (length xs)
eval env (Not exp) =
  let Bool x = eval env exp
  in Bool (not x)
eval env (e1 :&&: e2) =
  let Bool x = eval env e1
      Bool y = eval env e2
  in Bool (x && y)
eval env (e1 :=: e2) =
  Bool (eval env e1 == eval env e2)
eval env (e1 :<: e2) =
  let Int x = eval env e1
      Int y = eval env e2
  in Bool (x < y)
eval env (e1 :/: e2) =
  let Int x = eval env e1
      Int y = eval env e2
  in Int (x `div` y)
eval env (e1 :+: e2) =
  let Int x = eval env e1
      Int y = eval env e2
  in Int (x + y)
eval env (x :@: idx) =
  let Array xs = Map.findWithDefault undefined x env
      Int i = eval env idx
  in Int (xs !! i)
