{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Imp where

import Prelude hiding (lookup)
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.List hiding (lookup)
import Data.Maybe
import Data.Typeable(cast)
import Test.QuickCheck hiding (Fun, collect)
import QuickSpec.Explore
import QuickSpec.Explore.Polymorphic
import QuickSpec.Type hiding (Value, cast)
import QuickSpec.Term hiding (V, int)

data Prog =
    If Exp Prog Prog
  | While Exp Prog
  | Prog `Then` Prog
  | Skip
  | Point
  | ProgVar := Exp
deriving instance Show Prog

infixr 4 `Then`
infix 5 :=

data Val = Int Int | Bool Bool | Array [Int]
  deriving (Eq, Ord, Show)

type Exp = Term Fun

data ProgVar = V Type String
  deriving (Eq, Ord, Show)

data Fun =
  Val Val | ProgVar ProgVar |
  Not | And | Eq | Lt |
  Plus | Div |
  Index | Slice | Len
  deriving (Eq, Ord, Show)

int :: Int -> Exp
int x = App (Val (Int x)) []

bool :: Bool -> Exp
bool x = App (Val (Bool x)) []

array :: [Int] -> Exp
array xs = App (Val (Array xs)) []

progVar :: ProgVar -> Exp
progVar x = App (ProgVar x) []

nott :: Exp -> Exp
nott e = App Not [e]

andd :: Exp -> Exp -> Exp
andd e1 e2 = App And [e1, e2]

eq :: Exp -> Exp -> Exp
eq e1 e2 = App Eq [e1, e2]

lt :: Exp -> Exp -> Exp
lt e1 e2 = App Lt [e1, e2]

plus :: Exp -> Exp -> Exp
plus e1 e2 = App Plus [e1, e2]

divide :: Exp -> Exp -> Exp
divide e1 e2 = App Div [e1, e2]

index :: Exp -> Exp -> Exp
index e1 e2 = App Index [e1, e2]

slice :: Exp -> Exp -> Exp -> Exp
slice e1 e2 e3 = App Slice [e1, e2, e3]

len :: Exp -> Exp
len e = App Len [e]

type Env = Map ProgVar Val

run :: (Var -> Val) -> Prog -> Env -> Env
run var p env = runReader (execStateT (exec (return ()) p) env) var

collect :: (Var -> Val) -> Prog -> Env -> [Env]
collect var p env =
  runReader (execWriterT (execStateT (exec (get >>= tell . return) p) env)) var

exec :: (MonadState Env m, MonadReader (Var -> Val) m) => m () -> Prog -> m ()
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

evalM :: (MonadState Env m, MonadReader (Var -> Val) m) => Exp -> m Val
evalM exp = do
  env <- get
  var <- ask
  return (eval (env, var) exp)

eval :: (Env, Var -> Val) -> Term Fun -> Val
eval _ (App (Val x) []) = x
eval (_, env) (Var x) = env x
eval (env, _) (App (ProgVar x) []) =
  Map.findWithDefault undefined x env
eval env (App Len [e]) =
  let Array xs = eval env e in
  Int (length xs)
eval env (App Not [e]) =
  let Bool x = eval env e in
  Bool (not x)
eval env (App And [e1, e2]) =
  let Bool x = eval env e1
      Bool y = eval env e2
  in Bool (x && y)
eval env (App Eq [e1, e2]) =
  Bool (eval env e1 == eval env e2)
eval env (App Lt [e1, e2]) =
  let Int x = eval env e1
      Int y = eval env e2
  in Bool (x < y)
eval env (App Plus [e1, e2]) =
  let Int x = eval env e1
      Int y = eval env e2
  in Int (x + y)
eval env (App Div [e1, e2]) =
  let Int x = eval env e1
      Int y = eval env e2
  in Int (x `div` y)
eval env (App Index [e1, e2]) =
  let Array xs = eval env e1
      Int i = eval env e2
  in Int (xs !! i)
eval env (App Slice [e1, e2, e3]) =
  let Array xs = eval env e1
      Int i = eval env e2
      Int j = eval env e3
  in Array (drop i (take j xs))

bsearch :: Prog
bsearch =
  lo := int 0 `Then`
  hi := len (progVar arr) `Then`
  found := bool False `Then`
  While (andd (nott (progVar found)) (nott (eq (progVar lo) (progVar hi))))
    (Point `Then`
     mid := divide (plus (progVar lo) (progVar hi)) (int 2) `Then`
     If (lt (progVar x) (index (progVar arr) (progVar mid)))
       (hi := progVar mid)
       (If (lt (index (progVar arr) (progVar mid)) (progVar x))
         (lo := plus (progVar mid) (int 1))
         (found := bool True `Then` idx := progVar mid)))

x, lo, hi, mid, idx, arr, found :: ProgVar
lo = V intTy "lo"
hi = V intTy "hi"
mid = V intTy "mid"
idx = V intTy "idx"
x = V intTy "x"
arr = V arrayTy "arr"
found = V boolTy "found"

intTy, boolTy, arrayTy :: Type
intTy = typeOf (undefined :: Int)
boolTy = typeOf (undefined :: Bool)
arrayTy = typeOf (undefined :: [Int])

bsearchEnv :: Int -> [Int] -> Env
bsearchEnv vx varr =
  Map.fromList [(x, Int vx), (arr, Array varr)]

newtype SortedList a = SortedList [a] deriving (Eq, Ord, Show)

instance (Ord a, Arbitrary a) => Arbitrary (SortedList a) where
  arbitrary = SortedList . sort <$> arbitrary

genEnv :: Gen Env
genEnv = do
  x <- arbitrary
  SortedList xs <- arbitrary
  return (bsearchEnv x xs)

genPoint :: Gen Env
genPoint =
  ((collect undefined bsearch <$> genEnv) `suchThat` (not . null)) >>= elements

prop_bsearch :: Int -> SortedList Int -> Bool
prop_bsearch x (SortedList xs) =
  found_ == (x `elem` xs) &&
  (not found_ || xs !! mid_ == x)
  where
    res = run undefined bsearch (bsearchEnv x xs)
    Bool found_ = Map.findWithDefault undefined found res
    Int mid_ = Map.findWithDefault undefined mid res
