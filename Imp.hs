{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Twee.Pretty hiding (Mode)
import Control.Monad
import QuickSpec.Internal.Term hiding (Var, Sized, subst, evalTerm, Mode)
import qualified QuickSpec.Internal.Term as QS
import Data.Typeable
-- import Data.List hiding (lookup)
-- import Data.Maybe
-- import Data.Typeable(cast)
-- import Test.QuickCheck hiding (Fun, collect)
import QuickSpec.Internal.Explore
import QuickSpec.Internal.Explore.Polymorphic
import QuickSpec.Internal.Type hiding (Value, cast, Type, typeOf, toValue, fromValue)
import qualified QuickSpec.Internal.Type as QS
-- import QuickSpec.Term hiding (V, int)
-- import qualified QuickSpec.Term as QS
import qualified QuickSpec.Internal.Pruning.Twee as Twee
import qualified QuickSpec.Internal.Testing.QuickCheck as QuickCheck
import QuickSpec.Internal.Terminal
import QuickSpec.Internal.Pruning.Background(Background)
import QuickSpec.Internal.Haskell(arbitraryFunction)
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import QuickSpec.Internal.Explore.Conditionals
import QuickSpec.Internal.Prop
import Data.Maybe
import Data.List
import Test.QuickCheck hiding (Ordered, (==>))
import qualified Test.QuickCheck as QC
import Control.Enumerable
import Data.Reflection
import Control.Search hiding (Not, And, (|||), (&&&), (==>), nott, true, false, Options)
import Control.Spoon
import Control.DeepSeq
import GHC.Generics
import Data.Function
import Control.Monad.IO.Class
import Debug.Trace
import Control.Spoon
import Numeric.Natural
import QuickSpec.Internal.Pruning
import GHC.Stack
import Control.Monad.Trans.State.Strict
import Text.Printf
import Control.Monad.Trans.Class

data Prog where
  Arg  :: Type a => Var a -> Expr Bool -> Prog -> Prog
  Body :: Stmt -> Prog

args :: Prog -> [Some Var]
args (Arg x _ prog) = Some x:args prog
args (Body _) = []

body :: Prog -> Stmt
body (Arg _ _ prog) = body prog
body (Body stmt) = stmt

data Some f where
  Some :: Type a => f a -> Some f

data Stmt where
  (:=) :: Type a => Var a -> Expr a -> Stmt
  Skip :: Stmt
  Then :: Stmt -> Stmt -> Stmt
  If :: Expr Bool -> Stmt -> Stmt -> Stmt
  While :: Expr Bool -> Expr Bool -> Stmt -> Stmt
  Assert :: Expr Bool -> Stmt
  Point :: Stmt
deriving instance Show Stmt

data Expr a where
  Value   :: Type a => Value -> Expr a
  Local   :: Type a => Var a -> Expr a
  Unknown :: Type a => Unknown a -> Expr a
  -- Boolean expressions
  Not :: Expr Bool -> Expr Bool
  And :: Expr Bool -> Expr Bool -> Expr Bool
  Or  :: Expr Bool -> Expr Bool -> Expr Bool
  -- Arithmetic expressions
  Plus1 :: (Type a, Num a, a ~ Integer) => Expr a -> Expr a -> Expr a
  Plus2 :: (Type a, Num a, a ~ Index) => Expr a -> Expr a -> Expr a
  Minus1 :: (Type a, Num a, a ~ Integer) => Expr a -> Expr a -> Expr a
  Minus2 :: (Type a, Num a, a ~ Index) => Expr a -> Expr a -> Expr a
  Div1  :: (Type a, Integral a, a ~ Integer) => Expr a -> Expr a -> Expr a
  Div2  :: (Type a, Integral a, a ~ Index) => Expr a -> Expr a -> Expr a
  -- Relations
  Rel1 :: (Type a, Ord a, a ~ Integer) => Relation -> Expr a -> Expr a -> Expr Bool
  Rel2 :: (Type a, Ord a, a ~ Index) => Relation -> Expr a -> Expr a -> Expr Bool
  Pairwise1 :: (Type a, Ord a, a ~ Integer) => Relation -> Expr (Set a) -> Expr (Set a) -> Expr Bool
  Pairwise2 :: (Type a, Ord a, a ~ Index) => Relation -> Expr (Set a) -> Expr (Set a) -> Expr Bool
  Ordered :: (Type a, Ord a, a ~ Integer) => Relation -> Expr (Array a) -> Expr (Array a) -> Expr Bool
  -- Arrays
  At :: a ~ Integer => Expr (Array a) -> Expr Index -> Expr a
  Update :: (Type a, Ord a) => Expr (Array a) -> Expr Index -> Expr a -> Expr (Array a)
  Length :: Expr (Array Integer) -> Expr Index
  Image :: (Type (Array a), Ord a) => Expr (Array a) -> Expr (Set a)
  Concat :: Expr (Array a) -> Expr (Array a) -> Expr (Array a)
  Restrict :: Expr (Array a) -> Expr (Set Index) -> Expr (Array a)
  -- Sets
  Interval :: Expr Index -> Expr Index -> Expr (Set Index)
  Union1 :: a ~ Integer => Expr (Set a) -> Expr (Set a) -> Expr (Set a)
  Union2 :: a ~ Index => Expr (Set a) -> Expr (Set a) -> Expr (Set a)
  Singleton1 :: (Type a, Ord a, a ~ Integer) => Expr a -> Expr (Set a)
  Singleton2 :: (Type a, Ord a, a ~ Index) => Expr a -> Expr (Set a)
  Null1 :: Expr (Set Integer) -> Expr Bool
  Null2 :: Expr (Set Index) -> Expr Bool
deriving instance Show (Expr a)

mapExpr :: (forall a. Expr a -> Expr a) -> Expr a -> Expr a
mapExpr f e = rec e
  where
    rec :: forall a. Expr a -> Expr a
    rec e = f (sub e)

    sub :: forall a. Expr a -> Expr a
    sub (Not e) = Not (rec e)
    sub (And e1 e2) = And (rec e1) (rec e2)
    sub (Or e1 e2) = Or (rec e1) (rec e2)
    sub (Plus1 e1 e2) = Plus1 (rec e1) (rec e2)
    sub (Plus2 e1 e2) = Plus2 (rec e1) (rec e2)
    sub (Minus1 e1 e2) = Minus1 (rec e1) (rec e2)
    sub (Minus2 e1 e2) = Minus2 (rec e1) (rec e2)
    sub (Div1 e1 e2) = Div1 (rec e1) (rec e2)
    sub (Div2 e1 e2) = Div2 (rec e1) (rec e2)
    sub (Rel1 r e1 e2) = Rel1 r (rec e1) (rec e2)
    sub (Rel2 r e1 e2) = Rel2 r (rec e1) (rec e2)
    sub (Pairwise1 r e1 e2) = Pairwise1 r (rec e1) (rec e2)
    sub (Pairwise2 r e1 e2) = Pairwise2 r (rec e1) (rec e2)
    sub (Ordered r e1 e2) = Ordered r (rec e1) (rec e2)
    sub (At e1 e2) = At (rec e1) (rec e2)
    sub (Update e1 e2 e3) = Update (rec e1) (rec e2) (rec e3)
    sub (Length e) = Length (rec e)
    sub (Image e) = Image (rec e)
    sub (Concat e1 e2) = Concat (rec e1) (rec e2)
    sub (Restrict e1 e2) = Restrict (rec e1) (rec e2)
    sub (Interval e1 e2) = Interval (rec e1) (rec e2)
    sub (Union1 e1 e2) = Union1 (rec e1) (rec e2)
    sub (Union2 e1 e2) = Union2 (rec e1) (rec e2)
    sub (Singleton1 e) = Singleton1 (rec e)
    sub (Singleton2 e) = Singleton2 (rec e)
    sub (Null1 e) = Null1 (rec e)
    sub (Null2 e) = Null2 (rec e)
    sub e = e

data Relation = Eq | Ne | Le | Lt | Ge | Gt deriving (Eq, Ord, Show)

infixr 4 `Then`
infix 5 :=

data Value =
  IndexVal Index | BoolVal Bool | IntegerVal Integer |
  SetIntegerVal (Set Integer) | SetIndexVal (Set Index) |
  ArrayVal (Array Integer)
  deriving (Eq, Ord, Show, Generic)
instance NFData Value

valueType :: Value -> Type
valueType (IndexVal _) = typeOf (undefined :: Index)
valueType (BoolVal _) = typeOf (undefined :: Bool)
valueType (IntegerVal _) = typeOf (undefined :: Integer)
valueType (SetIntegerVal _) = typeOf (undefined :: Set Integer)
valueType (SetIndexVal _) = typeOf (undefined :: Set Index)
valueType (Arrayal _) = typeOf (undefined :: Array Integer)

shrinkValue :: Value -> [Value]
shrinkValue (IndexVal x) = IndexVal <$> shrink x
shrinkValue (BoolVal x) = BoolVal <$> shrink x
shrinkValue (IntegerVal x) = IntegerVal <$> shrink x
shrinkValue (SetIntegerVal x) = SetIntegerVal <$> shrink x
shrinkValue (SetIndexVal x) = SetIndexVal <$> shrink x
shrinkValue (ArrayVal x) = ArrayVal <$> shrink x

data Array a =
  Array {
    arrayLength :: Index,
    arrayContents :: Map Index a }
  deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (Array a)

makeArray :: [a] -> Array a
makeArray xs =
  Array (fromIntegral (length xs)) (Map.fromList (zip [0..] xs))

instance (Ord a, Arbitrary a) => Arbitrary (Array a) where
  arbitrary = do
    permute <- elements [id, sort]
    contents <- permute <$> arbitrary
    return (makeArray contents)
  shrink arr =
    [Array n (Map.takeWhileAntitone (< n) (arrayContents arr)) | n <- shrink (arrayLength arr)] ++
    [Array (arrayLength arr) xs | xs <- shrink (arrayContents arr)]

newtype Index = Index Natural deriving (Eq, Ord, Show, Num, Enum, Integral, Real, Pretty, Arbitrary, Generic, NFData)

instance Enumerable Natural where
  enumerate = datatype [c1 (fromIntegral :: Word -> Natural)]

instance Pretty Natural where
  pPrint = text . show

instance Enumerable Index where
  enumerate = datatype [c1 Index]

instance (Ord a, Enumerable a) => Enumerable (Set a) where
  enumerate = datatype [c1 Set.fromList]

instance (Ord a, Enumerable a) => Enumerable (Array a) where
  enumerate = datatype [c1 makeArray]

data Var a = Var String deriving (Eq, Ord, Show)
data Unknown a = Skolem Integer deriving (Eq, Ord, Show)

newtype Env = Env (Map String Value)
  deriving (Eq, Ord, Show, NFData, Pretty)

class (Arbitrary a, Enumerable a, Typeable a) => Type a where
  toValue :: a -> Value
  fromValue :: Value -> Maybe a
  typeName :: a -> String
  hungarian :: a -> String

instance Type Index where
  toValue = IndexVal
  fromValue (IndexVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "index"
  hungarian _ = "I"

instance Type Bool where
  toValue = BoolVal
  fromValue (BoolVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "boolean"
  hungarian _ = "B"

instance Type Integer where
  toValue = IntegerVal
  fromValue (IntegerVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "integer"
  hungarian _ = "X"

instance Type (Set Integer) where
  toValue = SetIntegerVal
  fromValue (SetIntegerVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "set of integer"
  hungarian _ = "S"

instance Type (Set Index) where
  toValue = SetIndexVal
  fromValue (SetIndexVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "set of index"
  hungarian _ = "IS"

instance a ~ Integer => Type (Array a) where
  toValue = ArrayVal
  fromValue (ArrayVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "array of integer"
  hungarian _ = "A"

exec :: Env -> Expr Bool -> Stmt -> ([(Env, Expr Bool)], Env, Expr Bool)
exec (Env env) _ (Var x := e) =
  ([], Env (Map.insert x (toValue (eval (Env env) e)) env), true)
exec env pred Skip = ([], env, pred)
exec env pred (p `Then` q) =
  let
    (envs1, env1, pred1) = exec env pred p
    (envs2, env2, pred2) = exec env1 pred1 q
  in (envs1 ++ envs2, env2, pred2)
exec env pred (If e p1 p2) =
  if eval env e
  then exec env (pred &&& refine env e) p1
  else exec env (pred &&& refine env e) p2
exec env pred (While e1 e2 p) =
  if eval env e2 then
    if eval env e1
    then exec env (e2 &&& refine env e1) (p `Then` While e1 e2 p)
    else exec env (e2 &&& refine env e1) Skip
  else error "invariant false"
exec env pred (Assert e) =
  if eval env e
  then exec env (pred &&& e) Skip
  else error "assertion failed"
exec env pred Point =
  ([(env, pred)], env, pred)

refine :: Env -> Expr Bool -> Expr Bool
refine env e =
  foldr (&&&) true [ e' | e' <- cands, eval env e' ]
  where
    cands =
      nubBy ((==) `on` show)
        (subforms e ++ map nott (subforms e))

subst :: (forall a. Type a => Unknown a -> Expr a) -> Expr a -> Expr a
subst sub (Value x) = Value x
subst sub (Local x) = Local x
subst sub (Unknown x) = sub x
subst sub (Not e) = Not (subst sub e)
subst sub (And e1 e2) = And (subst sub e1) (subst sub e2)
subst sub (Or e1 e2) = Or (subst sub e1) (subst sub e2)
subst sub (Plus1 e1 e2) = Plus1 (subst sub e1) (subst sub e2)
subst sub (Plus2 e1 e2) = Plus2 (subst sub e1) (subst sub e2)
subst sub (Minus1 e1 e2) = Minus1 (subst sub e1) (subst sub e2)
subst sub (Minus2 e1 e2) = Minus2 (subst sub e1) (subst sub e2)
subst sub (Div1 e1 e2) = Div1 (subst sub e1) (subst sub e2)
subst sub (Div2 e1 e2) = Div2 (subst sub e1) (subst sub e2)
subst sub (Rel1 rel e1 e2) = Rel1 rel (subst sub e1) (subst sub e2)
subst sub (Rel2 rel e1 e2) = Rel2 rel (subst sub e1) (subst sub e2)
subst sub (Pairwise1 rel e1 e2) = Pairwise1 rel (subst sub e1) (subst sub e2)
subst sub (Pairwise2 rel e1 e2) = Pairwise2 rel (subst sub e1) (subst sub e2)
subst sub (Ordered rel e1 e2) = Ordered rel (subst sub e1) (subst sub e2)
subst sub (At e1 e2) = At (subst sub e1) (subst sub e2)
subst sub (Update e1 e2 e3) = Update (subst sub e1) (subst sub e2) (subst sub e3)
subst sub (Length e) = Length (subst sub e)
subst sub (Image e) = Image (subst sub e)
subst sub (Concat e1 e2) = Concat (subst sub e1) (subst sub e2)
subst sub (Restrict e1 e2) = Restrict (subst sub e1) (subst sub e2)
subst sub (Union1 e1 e2) = Union1 (subst sub e1) (subst sub e2)
subst sub (Union2 e1 e2) = Union2 (subst sub e1) (subst sub e2)
subst sub (Interval e1 e2) = Interval (subst sub e1) (subst sub e2)
subst sub (Singleton1 e) = Singleton1 (subst sub e)
subst sub (Singleton2 e) = Singleton2 (subst sub e)
subst sub (Null1 e) = Null1 (subst sub e)
subst sub (Null2 e) = Null2 (subst sub e)

eval :: Env -> Expr a -> a
eval _ (Value x) =
  fromMaybe (error $ "ill-typed expression: " ++ show x) (fromValue x)
eval (Env env) (Local (Var x)) =
  fromMaybe (error "ill-typed expression") $ fromValue $
  Map.findWithDefault (error ("variable " ++ x ++ " not bound")) x env
eval env (Not e) =
  not (eval env e)
eval env (And e1 e2) =
  eval env e1 && eval env e2
eval env (Or e1 e2) =
  eval env e1 || eval env e2
eval env (Plus1 e1 e2) =
  eval env e1 + eval env e2
eval env (Plus2 e1 e2) =
  eval env e1 + eval env e2
eval env (Minus1 e1 e2) =
  eval env e1 - eval env e2
eval env (Minus2 e1 e2) =
  eval env e1 `safeMinus` eval env e2
  where
    safeMinus x y = if x < y then 0 else x - y
eval env (Div1 e1 e2) =
  eval env e1 `safeDiv` eval env e2
eval env (Div2 e1 e2) =
  eval env e1 `safeDiv` eval env e2
eval env (Rel1 r e1 e2) =
  evalRel r (eval env e1) (eval env e2)
eval env (Rel2 r e1 e2) =
  evalRel r (eval env e1) (eval env e2)
eval env (Pairwise1 r e1 e2) =
  and [evalRel r x y | x <- xs, y <- ys]
  where
    !xs = Set.toList (eval env e1)
    !ys = Set.toList (eval env e2)
eval env (Pairwise2 r e1 e2) =
  and [evalRel r x y | x <- xs, y <- ys]
  where
    !xs = Set.toList (eval env e1)
    !ys = Set.toList (eval env e2)
eval env (Ordered r e1 e2) =
  and [evalRel r x y | (i, x) <- xs, (j, y) <- ys, i < j]
  where
    !xs = Map.toList (arrayContents (eval env e1))
    !ys = Map.toList (arrayContents (eval env e2))
eval env (At e1 e2) =
  index (eval env e2) (arrayContents (eval env e1))
  where
    index i arr =
      Map.findWithDefault (fromIntegral i * 37 * (if even i then 1 else -1) + 2) i arr
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
eval env (Union1 e1 e2) =
  Set.union (eval env e1) (eval env e2)
eval env (Union2 e1 e2) =
  Set.union (eval env e1) (eval env e2)
eval env (Interval e1 e2) =
  Set.fromList [eval env e1..eval env e2-1]
eval env (Singleton1 e) =
  Set.singleton $! eval env e
eval env (Singleton2 e) =
  Set.singleton $! eval env e
eval env (Null1 e) =
  Set.null (eval env e)
eval env (Null2 e) =
  Set.null (eval env e)

safeDiv :: Integral a => a -> a -> a
safeDiv _ 0 = 0
safeDiv x y = x `div` y

subforms :: Expr Bool -> [Expr Bool]
subforms e = e:properSubforms e
  where
    properSubforms :: Expr Bool -> [Expr Bool]
    properSubforms (Not e) = subforms e
    properSubforms (And e1 e2) = subforms e1 ++ subforms e2
    properSubforms (Or e1 e2) = subforms e1 ++ subforms e2
    properSubforms _ = []

evalRel :: Ord a => Relation -> a -> a -> Bool
evalRel Eq = (==)
evalRel Ne = (/=)
evalRel Lt = (<)
evalRel Le = (<=)
evalRel Gt = (>)
evalRel Ge = (>=)

genEnv :: Prog -> Gen Env
genEnv = go (Env Map.empty)
  where
    go (Env env) (Arg (Var x :: Var a) cond prog) = do
      env <-
        (do
           val <- arbitrary :: Gen a
           return (Env (Map.insert x (toValue val) env))) `suchThat`
        (\env -> eval env cond)
      go env prog
    go env (Body _) = return env

genPointFrom :: Prog -> Gen Env -> Gen Env
genPointFrom prog gen = do
  envs <- do { env <- gen; let (points, _, _) = exec env true (body prog) in return (map fst points) } `suchThat` (not . null)
  elements envs

genPoint :: Prog -> Gen Env
genPoint prog = genPointFrom prog (genEnv prog)

genPostFrom :: Prog -> Gen Env -> Gen Env
genPostFrom prog gen = do
  env <- gen
  let (_, env', _) = exec env true (body prog)
  return env'

genPost :: Prog -> Gen Env
genPost prog = genPostFrom prog (genEnv prog)

genVars :: Gen (QS.Var -> Value)
genVars =
  arbitraryFunction $ \(QS.V ty _) ->
    case () of
    _ | ty == QS.typeOf (undefined :: Integer) -> IntegerVal <$> arbitrary
      | ty == QS.typeOf (undefined :: Index) -> IndexVal <$> arbitrary
      | ty == QS.typeOf (undefined :: Bool) -> BoolVal <$> arbitrary
      | ty == QS.typeOf (undefined :: Set Index) -> SetIndexVal <$> arbitrary
      | ty == QS.typeOf (undefined :: Set Integer) -> SetIntegerVal <$> arbitrary
      | ty == QS.typeOf (undefined :: Array Integer) -> ArrayVal <$> arbitrary

shrinkEnv :: Prog -> Env -> [Env]
shrinkEnv prog (Env env) =
  filter (checkEnv prog) (map (Env . Map.fromList) (shr (Map.toList env)))
  where
    shr [] = []
    shr ((x,v):xs) =
      [(x,v'):xs | v' <- shrinkValue v] ++
      map ((x,v):) (shr xs)

checkEnv :: Prog -> Env -> Bool
checkEnv (Arg _ cond prog) env =
  eval env cond && checkEnv prog env
checkEnv (Body _) _ = True

enumEnv :: forall f. (Typeable f, Sized f) => Prog -> Shareable f Env
enumEnv (Body _) = c0 (Env Map.empty)
enumEnv (Arg (Var x :: Var a) _ prog) =
  ins <$> (access :: Shareable f a) <*> enumEnv prog
  where
    ins val (Env env) = Env (Map.insert x (toValue val) env)

newtype PP a = PP a
instance Enumerable a => Enumerable (PP a) where
  enumerate = datatype [c1 PP]
instance Pretty a => Show (PP a) where
  show (PP x) = show (pPrint x)

testProg :: Prog -> IO ()
testProg prog =
  give prog $
  testTime 30 $ \(PP env) ->
  not (checkEnv prog env) || isJust (spoon (result (exec env (preProg prog) (body prog))))
  where
    result (_, env, _) = env

testProgOn :: Prog -> Env -> Bool
testProgOn prog env =
  checkEnv prog env &&
  isJust (spoon (result (exec env true (body prog))))
  where
    result (_, env, _) = env

instance Given Prog => Arbitrary Env where
  arbitrary = genEnv given
  shrink = shrinkEnv given

instance Given Prog => Enumerable Env where
  enumerate = share (enumEnv given)

(|||), (&&&), (==>) :: Expr Bool -> Expr Bool -> Expr Bool
x ||| Value (BoolVal False) = x
Value (BoolVal False) ||| x = x
_ ||| Value (BoolVal True) = Value (BoolVal True)
Value (BoolVal True) ||| _ = Value (BoolVal True)
x ||| y = Or x y
x &&& Value (BoolVal True) = x
Value (BoolVal True) &&& x = x
_ &&& Value (BoolVal False) = Value (BoolVal False)
Value (BoolVal False) &&& _ = Value (BoolVal False)
x &&& y = And x y
Value (BoolVal True) ==> x = x
Value (BoolVal False) ==> x = Value (BoolVal True)
x ==> y = nott x ||| y

nott :: Expr Bool -> Expr Bool
nott (Value (BoolVal True)) = Value (BoolVal False)
nott (Value (BoolVal False)) = Value (BoolVal True)
nott (Not x) = x
nott x = Not x

true, false :: Expr Bool
true = Value (BoolVal True)
false = Value (BoolVal False)

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
    pre' (While _ e _) = (e, False)
    pre' (Assert e) = (e, True)
    pre' Point = (true, True)

post :: Stmt -> Expr Bool
post stmt = fst (post' stmt)
  where
    -- Boolean: was the statement side effect-free?
    post' (_ := _) = (true, False)
    post' Skip = (true, True)
    post' (p `Then` q) =
      case post' q of
        (e, False) -> (e, False)
        (e, True) ->
          let (e', b) = post' p in
          (e &&& e', b)
    post' (If cond p q) =
      case (post' p, post' q) of
        ((e1, True), (e2, True)) ->
          ((cond ==> e1) &&& (nott cond ==> e2), True)
        _ -> (true, False)
    post' (While e1 e2 _) = (nott e1 &&& e2, False)
    post' (Assert e) = (e, True)
    post' Point = (true, True)

instance Pretty Prog where
  pPrint prog =
    text "input" $$
    loop prog
    where
      loop (Arg (x :: Var a) cond prog) =
        nest 2 (pPrint x <+> text ":" <+> text (typeName (undefined :: a)) <+> ppCond cond <#> text ";") $$
        loop prog
      loop (Body stmt) =
        text "begin" $$
        nest 2 (pPrint stmt) $$
        text "end."
      ppCond (Value (BoolVal True)) = pPrintEmpty
      ppCond e =
        text "such that" <+> pPrint e

instance Pretty Stmt where
  pPrint (x := e) =
    hang (pPrint x <+> text ":=") 2 (pPrint e)
  pPrint Skip =
    text "skip"
  pPrint (p1 `Then` p2) =
    pPrint p1 <> text ";" $$
    pPrint p2
  pPrint (If e p1 p2) =
    text "if" <+> pPrint e <+> text "then" $$
    nest 2 (pPrint p1) $$
    chain p2 $$
    text "end"
    where
      chain Skip = pPrintEmpty
      chain (If e p1 p2) =
        text "elseif" <+> pPrint e <+> text "then" $$
        nest 2 (pPrint p1) $$
        chain p2
      chain p =
        text "else" $$
        nest 2 (pPrint p)
  pPrint (While e1 e2 p) =
    text "while" <+> pPrint e1 <+> text "invariant" <+> pPrint e2 <+> text "do" $$
    nest 2 (pPrint p) $$
    text "end"
  pPrint (Assert e) =
    text "assert" <#> parens (pPrint e)
  pPrint Point =
    text "{ ? }"

instance Pretty (Some Expr) where
  pPrintPrec l p (Some e) = pPrintPrec l p e

instance Pretty (Expr a) where
  pPrintPrec l p e = exp p e
    where
      parIf True x = parens x
      parIf False x = x

      oper :: Rational -> Rational -> String -> Expr b -> Expr c -> Doc
      oper p prec name e1 e2 =
        parIf (p > prec) $
         pPrintPrec l (prec+1) e1 <+> text name <+> pPrintPrec l (prec+1) e2

      -- Precedence levels:
      -- 0: and, or
      -- 1: relations
      -- 2: not
      -- 3: +, sorted
      -- 4: div
      -- 5: restrict
      -- 6: image
      exp :: forall b. Rational -> Expr b -> Doc
      exp _ (Value x) =
        pPrint x
      exp _ (Unknown (Skolem n)) =
        text (hungarian (undefined :: b) ++ show (n+1))
      exp _ (Local x) =
        pPrint x
      exp p (Not e) =
        parIf (p > 2) $
          text "not" <+> pPrintPrec l 3 e
      exp p (And e1 e2) =
        oper p 0 "and" e1 e2
      exp p (Or e1 e2) =
        oper p 0 "or" e1 e2
      exp p (Plus1 e1 e2) =
        oper p 3 "+" e1 e2
      exp p (Plus2 e1 e2) =
        oper p 3 "+" e1 e2
      exp p (Minus1 e1 e2) =
        oper p 3 "-" e1 e2
      exp p (Minus2 e1 e2) =
        oper p 3 "-" e1 e2
      exp p (Div1 e1 e2) =
        oper p 4 "div" e1 e2
      exp p (Div2 e1 e2) =
        oper p 4 "div" e1 e2
      exp p (Rel1 r e1 e2) =
        oper p 1 (rel r) e1 e2
      exp p (Rel2 r e1 e2) =
        oper p 1 (rel r) e1 e2
      exp p (Pairwise1 r e1 e2) =
        oper p 1 (rel r ++ "*") e1 e2
      exp p (Pairwise2 r e1 e2) =
        oper p 1 (rel r ++ "*") e1 e2
      exp p (Ordered r e1 e2) =
        oper p 1 (rel r ++ "O") e1 e2
      exp p (At e1 e2) =
        exp inf e1 <#> brackets (exp 0 e2)
      exp p (Update e1 e2 e3) =
        text "update" <#> parens (hsep (punctuate comma [exp inf e1, exp 0 e2 <+> text ":=" <+> exp 0 e3]))
      exp p (Length e) =
        text "length" <#> parens (exp 0 e)
      exp p (Image e) =
        parIf (p > 6) $
          text "image" <#> parens (exp 0 e)
      exp p (Concat e1 e2) =
        text "concat" <#> parens (hsep (punctuate comma [exp 0 e1, exp 0 e2]))
      exp p (Restrict e1 e2) =
        text "restrict" <#> parens (hsep (punctuate comma [exp 0 e1, exp 0 e2]))
      exp p (Union1 e1 e2) =
        text "union" <#> parens (hsep (punctuate comma [exp 0 e1, exp 0 e2]))
      exp p (Union2 e1 e2) =
        text "union" <#> parens (hsep (punctuate comma [exp 0 e1, exp 0 e2]))
      exp p (Interval e1 e2) =
        text "[" <#>
        cat [exp 0 e1 <#> text "..", exp 0 e2 <#> text ")"]
      exp p (Singleton1 e) =
        text "singleton" <#> parens (exp 0 e)
      exp p (Singleton2 e) =
        text "singleton" <#> parens (exp 0 e)
      exp p (Null1 e) =
        oper 2 1 "=" e (Value (SetIntegerVal Set.empty) :: Expr (Set Integer))
      exp p (Null2 e) =
        oper 2 1 "=" e (Value (SetIndexVal Set.empty) :: Expr (Set Index))
  
      rel :: Relation -> String
      rel Eq = "="
      rel Ne = "<>"
      rel Lt = "<"
      rel Le = "<="
      rel Gt = ">"
      rel Ge = ">="

      inf :: Rational
      inf = 100

instance Pretty Value where
  pPrint (IndexVal x) = pPrint x
  pPrint (BoolVal True) = text "true"
  pPrint (BoolVal False) = text "false"
  pPrint (IntegerVal x) = pPrint x
  pPrint (SetIntegerVal x) = pPrint x
  pPrint (SetIndexVal x) = pPrint x
  pPrint (ArrayVal arr) =
    pPrint (arrayContents arr)

instance Pretty (Var a) where
  pPrint (Var x) = text x

data Sym =
  SymValue Value | SymLocal String TypeRep |
  SymNot | SymAnd | SymOr | SymPlus1 | SymPlus2 | SymMinus1 | SymMinus2 | SymDiv1 | SymDiv2 |
  SymRel1 Relation | SymRel2 Relation | SymPairwise1 Relation | SymPairwise2 Relation | SymOrdered Relation |
  SymAt | SymUpdate | SymLength | SymImage | SymConcat |
  SymRestrict | SymUnion1 | SymUnion2 | SymInterval | SymSingleton1 | SymSingleton2 | SymNull1 | SymNull2
  deriving (Eq, Ord, Show)

toQSVar :: forall a. Type a => Unknown a -> QS.Var
toQSVar (Skolem x) = QS.V (QS.typeOf (undefined :: a)) (fromInteger x)

toQS :: forall a. Type a => Expr a -> Term Sym
toQS (Value x) = App (SymValue x) []
toQS (Local (Var x)) = App (SymLocal x (typeOf (undefined :: a))) []
toQS (Unknown x) = QS.Var (toQSVar x)
toQS (Not e) = App SymNot [toQS e]
toQS (And e1 e2) = App SymAnd [toQS e1, toQS e2]
toQS (Or e1 e2) = App SymOr [toQS e1, toQS e2]
toQS (Plus1 e1 e2) = App SymPlus1 [toQS e1, toQS e2]
toQS (Plus2 e1 e2) = App SymPlus2 [toQS e1, toQS e2]
toQS (Minus1 e1 e2) = App SymMinus1 [toQS e1, toQS e2]
toQS (Minus2 e1 e2) = App SymMinus2 [toQS e1, toQS e2]
toQS (Div1 e1 e2) = App SymDiv1 [toQS e1, toQS e2]
toQS (Div2 e1 e2) = App SymDiv2 [toQS e1, toQS e2]
toQS (Rel1 r e1 e2) = App (SymRel1 r) [toQS e1, toQS e2]
toQS (Rel2 r e1 e2) = App (SymRel2 r) [toQS e1, toQS e2]
toQS (Pairwise1 r e1 e2) = App (SymPairwise1 r) [toQS e1, toQS e2]
toQS (Pairwise2 r e1 e2) = App (SymPairwise2 r) [toQS e1, toQS e2]
toQS (Ordered r e1 e2) = App (SymOrdered r) [toQS e1, toQS e2]
toQS (At e1 e2) = App SymAt [toQS e1, toQS e2]
toQS (Update e1 e2 e3) = App SymUpdate [toQS e1, toQS e2, toQS e3]
toQS (Length e) = App SymLength [toQS e]
toQS (Image e) = App SymImage [toQS e]
toQS (Concat e1 e2) = App SymConcat [toQS e1, toQS e2]
toQS (Restrict e1 e2) = App SymRestrict [toQS e1, toQS e2]
toQS (Union1 e1 e2) = App SymUnion1 [toQS e1, toQS e2]
toQS (Union2 e1 e2) = App SymUnion2 [toQS e1, toQS e2]
toQS (Interval e1 e2) = App SymInterval [toQS e1, toQS e2]
toQS (Singleton1 e) = App SymSingleton1 [toQS e]
toQS (Singleton2 e) = App SymSingleton2 [toQS e]
toQS (Null1 e) = App SymNull1 [toQS e]
toQS (Null2 e) = App SymNull2 [toQS e]

op1 :: (Type a, Type b) => (Expr a -> Expr b) -> Term Sym -> Some Expr
op1 f t =
  case fromQS t of
    Some e ->
      case cast e of
        Just e -> Some (f e)

op2 :: (HasCallStack, Type a, Type b, Type c) => (Expr a -> Expr b -> Expr c) -> Term Sym -> Term Sym -> Some Expr
op2 f t u =
  case (fromQS t, fromQS u) of
    (Some e1, Some e2) ->
      case (cast e1, cast e2) of
        (Just e1, Just e2) -> Some (f e1 e2)
        _ -> error "oops"

op3 :: (Type a, Type b, Type c, Type d) => (Expr a -> Expr b -> Expr c -> Expr d) -> Term Sym -> Term Sym -> Term Sym -> Some Expr
op3 f t u v =
  case (fromQS t, fromQS u, fromQS v) of
    (Some e1, Some e2, Some e3) ->
      case (cast e1, cast e2, cast e3) of
        (Just e1, Just e2, Just e3) -> Some (f e1 e2 e3)

fromQS :: Term Sym -> Some Expr
fromQS (QS.Var (QS.V ty x))
  | ty == QS.typeOf (undefined :: Integer) =
    Some (Unknown (Skolem (fromIntegral x) :: Unknown Integer))
  | ty == QS.typeOf (undefined :: Index) =
    Some (Unknown (Skolem (fromIntegral x) :: Unknown Index))
  | ty == QS.typeOf (undefined :: Bool) =
    Some (Unknown (Skolem (fromIntegral x) :: Unknown Bool))
  | ty == QS.typeOf (undefined :: Set Index) =
    Some (Unknown (Skolem (fromIntegral x) :: Unknown (Set Index)))
  | ty == QS.typeOf (undefined :: Set Integer) =
    Some (Unknown (Skolem (fromIntegral x) :: Unknown (Set Integer)))
  | ty == QS.typeOf (undefined :: Array Integer) =
    Some (Unknown (Skolem (fromIntegral x) :: Unknown (Array Integer)))
fromQS (App (SymValue x) []) =
  case x of
    IntegerVal{} -> Some (Value x :: Expr Integer)
    IndexVal{} -> Some (Value x :: Expr Index)
    BoolVal{} -> Some (Value x :: Expr Bool)
    SetIndexVal{} -> Some (Value x :: Expr (Set Index))
    SetIntegerVal{} -> Some (Value x :: Expr (Set Integer))
    ArrayVal{} -> Some (Value x :: Expr (Array Integer))
fromQS (App (SymLocal x ty) [])
  | ty == typeOf (undefined :: Integer) =
    Some (Local (Var x :: Var Integer))
  | ty == typeOf (undefined :: Index) =
    Some (Local (Var x :: Var Index))
  | ty == typeOf (undefined :: Bool) =
    Some (Local (Var x :: Var Bool))
  | ty == typeOf (undefined :: Set Index) =
    Some (Local (Var x :: Var (Set Index)))
  | ty == typeOf (undefined :: Set Integer) =
    Some (Local (Var x :: Var (Set Integer)))
  | ty == typeOf (undefined :: Array Integer) =
    Some (Local (Var x :: Var (Array Integer)))
fromQS (App SymNot [e]) = op1 Not e
fromQS (App SymAnd [e1, e2]) = op2 And e1 e2
fromQS (App SymOr [e1, e2]) = op2 Or e1 e2
fromQS (App SymPlus1 [e1, e2]) = op2 Plus1 e1 e2
fromQS (App SymPlus2 [e1, e2]) = op2 Plus2 e1 e2
fromQS (App SymMinus1 [e1, e2]) = op2 Minus1 e1 e2
fromQS (App SymMinus2 [e1, e2]) = op2 Minus2 e1 e2
fromQS (App SymDiv1 [e1, e2]) = op2 Div1 e1 e2
fromQS (App SymDiv2 [e1, e2]) = op2 Div2 e1 e2
fromQS (App (SymRel1 r) [e1, e2]) = op2 (Rel1 r) e1 e2
fromQS (App (SymRel2 r) [e1, e2]) = op2 (Rel2 r) e1 e2
fromQS (App (SymPairwise1 r) [e1, e2]) = op2 (Pairwise1 r) e1 e2
fromQS (App (SymPairwise2 r) [e1, e2]) = op2 (Pairwise2 r) e1 e2
fromQS (App (SymOrdered r) [e1, e2]) = op2 (Ordered r) e1 e2
fromQS (App SymAt [e1, e2]) = op2 At e1 e2
fromQS (App SymUpdate [e1, e2, e3]) = op3 Update e1 e2 e3
fromQS (App SymLength [e]) = op1 Length e
fromQS (App SymImage [e]) = op1 Image e
fromQS (App SymConcat [e1, e2]) = op2 Concat e1 e2
fromQS (App SymRestrict [e1, e2]) = op2 Restrict e1 e2
fromQS (App SymUnion1 [e1, e2]) = op2 Union1 e1 e2
fromQS (App SymUnion2 [e1, e2]) = op2 Union2 e1 e2
fromQS (App SymInterval [e1, e2]) = op2 Interval e1 e2
fromQS (App SymSingleton1 [e]) = op1 Singleton1 e
fromQS (App SymSingleton2 [e]) = op1 Singleton2 e
fromQS (App SymNull1 [e]) = op1 Null1 e
fromQS (App SymNull2 [e]) = op1 Null2 e
fromQS e = error ("Ill-typed term: " ++ prettyShow e)

bsearch :: Prog
bsearch =
  Arg arr (Ordered Le (Local arr) (Local arr)) $
  Arg x (Value (BoolVal True)) $
  Body $
  lo := Value (IndexVal 0) `Then`
  hi := Length (Local arr) `Then`
  found := Value (BoolVal False) `Then`
  While (And (Not (Local found)) (Rel2 Lt (Local lo) (Local hi))) (Value (BoolVal True))
    (Point `Then`
     mid := Div2 (Plus2 (Local lo) (Local hi)) (Value (IndexVal 2)) `Then`
     If (Rel1 Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value (BoolVal True) `Then` idx := Local mid)
       (If (Rel1 Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         -- (hi := Minus (Local mid) (Value (IndexVal 1)))
         (lo := Plus2 (Local mid) (Value (IndexVal 1)))))
  -- If (Local found)
  --   (Assert (Rel Eq (At (Local arr) (Local idx)) (Local x)))
  --   (Assert (Pairwise Ne (Singleton (Local x)) (Image (Local arr))))

x :: Var Integer
x = Var "x"

lo, hi, mid, idx :: Var Index
lo = Var "lo"
hi = Var "hi"
mid = Var "mid"
idx = Var "idx"

arr :: Var (Array Integer)
arr = Var "arr"

found :: Var Bool
found = Var "found"

tests :: [Env]
tests = map env [
  (-123, [-123]),
  (-2, [-123,-6,-2,59,102]),
  (153, [-123,-6,-2,59]),
  (59, [-123,-6,-2,102]),
  (102, [-123,-6,-2,102])]
  where
    env (x, arr) =
      Env $ Map.fromList [("x", IntegerVal x), ("arr", ArrayVal (makeArray arr))]

instance QS.Sized Sym where
  size _ = 1

instance Apply (Term Sym) where
  tryApply t@(App f us) u = do
    tryApply (typ t) (typ u)
    return (App f (us ++ [u]))
  tryApply _ _ = Nothing

instance Typed Sym where
  typ (SymValue (IndexVal _)) = QS.typeOf (undefined :: Index)
  typ (SymValue (BoolVal _)) = QS.typeOf (undefined :: Bool)
  typ (SymValue (IntegerVal _)) = QS.typeOf (undefined :: Integer)
  typ (SymValue (SetIntegerVal _)) = QS.typeOf (undefined :: Set Integer)
  typ (SymValue (SetIndexVal _)) = QS.typeOf (undefined :: Set Index)
  typ (SymValue (ArrayVal _)) = QS.typeOf (undefined :: Array Integer)
  typ (SymLocal _ ty) = fromTypeRep ty
  typ SymNot = QS.typeOf not
  typ SymAnd = QS.typeOf (&&)
  typ SymOr = QS.typeOf (||)
  typ SymPlus1 = QS.typeOf ((+) @ Integer)
  typ SymPlus2 = QS.typeOf ((+) @ Index)
  typ SymMinus1 = QS.typeOf ((-) @ Integer)
  typ SymMinus2 = QS.typeOf ((-) @ Index)
  typ SymDiv1 = QS.typeOf (div @ Integer)
  typ SymDiv2 = QS.typeOf (div @ Index)
  typ (SymRel1 _) = QS.typeOf ((<) @ Integer)
  typ (SymRel2 _) = QS.typeOf ((<) @ Index)
  typ (SymPairwise1 _) = QS.typeOf (undefined :: Set Integer -> Set Integer -> Bool)
  typ (SymPairwise2 _) = QS.typeOf (undefined :: Set Index -> Set Index -> Bool)
  typ (SymOrdered _) = QS.typeOf (undefined :: Array Integer -> Array Integer -> Bool)
  typ SymAt = QS.typeOf (undefined :: Array Integer -> Index -> Integer)
  typ SymUpdate = QS.typeOf (undefined :: Array Integer -> Index -> Integer -> Array Integer)
  typ SymLength = QS.typeOf (undefined :: Array Integer -> Index)
  typ SymImage = QS.typeOf (undefined :: Array Integer -> Set Integer)
  typ SymConcat = QS.typeOf (undefined :: Array Integer -> Array Integer -> Array Integer)
  typ SymRestrict = QS.typeOf (undefined :: Array Integer -> Set Index -> Array Integer)
  typ SymUnion1 = QS.typeOf (undefined :: Set Integer -> Set Integer -> Set Integer)
  typ SymUnion2 = QS.typeOf (undefined :: Set Index -> Set Index -> Set Index)
  typ SymInterval = QS.typeOf (undefined :: Array Index -> Array Index -> Set Index)
  typ SymSingleton1 = QS.typeOf (undefined :: Integer -> Set Integer)
  typ SymSingleton2 = QS.typeOf (undefined :: Index -> Set Index)
  typ SymNull1 = QS.typeOf (undefined :: Set Integer -> Bool)
  typ SymNull2 = QS.typeOf (undefined :: Set Index -> Bool)
  typeSubst_ _ x = x

instance Background Sym

instance Pretty Sym where
  pPrint = text . show

instance PrettyTerm Sym where
  termStyle _ = uncurried

instance PrettyArity Sym

instance Predicate Sym where
--  classify (Le = Predicate [Le1, Le2] leTy (bool True)
--   classify Elem = Predicate [Elem1, Elem2] elemTy (bool True)
-- --  classify Le1 = Selector 0 Le leTy
-- --  classify Le2 = Selector 1 Le leTy
--   classify Elem1 = Selector 0 Elem elemTy
--   classify Elem2 = Selector 1 Elem elemTy
  classify _ = Function

evalLHS :: (Env, QS.Var -> Value) -> Equation (Term Sym) -> Bool
evalLHS env (t :=: u) = evalTerm env t == evalTerm env u

evalRHS :: (Env, QS.Var -> Value) -> Equation (Term Sym) -> Property
evalRHS env (t :=: u) = evalTerm env t Test.QuickCheck.=== evalTerm env u

evalTerm :: (Env, QS.Var -> Value) -> Term Sym -> Value
evalTerm (env, vars) t =
  case fromQS t of
    Some e ->
      toValue (eval env (subst (Value . vars . toQSVar) e))

instance Given Prog => Testable (Prop (Term Sym)) where
  property (lhs :=>: rhs) =
    forAllShrink (genEnv given) (shrinkEnv given) $ \env0 ->
      forAll (Blind <$> genVars) $ \(Blind vars) ->
      let (_, env, _) = exec env0 (Value (BoolVal True)) (body given) in
      counterexample (prettyShow env) $
      foldr (QC.==>) (evalRHS (env, vars) rhs) (map (evalLHS (env, vars)) lhs)

data Options =
  Options {
    options :: [Option],
    categories :: [Category],
    environment :: Environment }

data Option = Silent | QuickCheck deriving Eq
data Category = Vars | Arith | Arrays deriving Eq
data Environment = Background | Precondition | Postcondition | AtPoint | From [Env] | PostFrom [Env] | PointFrom [Env]

genFor :: Prog -> Environment -> Gen Env
genFor prog Background = return (Env Map.empty)
genFor prog Precondition = genEnv prog
genFor prog Postcondition = genPost prog
genFor prog AtPoint = genPoint prog
genFor prog (From envs) = elements envs
genFor prog (PostFrom envs) = genPostFrom prog (elements envs)
genFor prog (PointFrom envs) = genPointFrom prog (elements envs)

enumerator :: Options -> Prog -> [Some Local] -> Enumerator (Term Sym)
enumerator Options{..} prog =
  sortTerms measure $
  enumerateConstants (vars ++ locals ++ map (\x -> App x []) consts) `mappend` enumerateApplications
  where
    vars = [QS.Var (QS.V ty 0) | ty <- tys]
    -- XXXX add all vars
    locals = [toQS (Local x) | Some x <- args prog] ++ [toQS (Not (Local y)) | Some x <- args prog, Just y <- [cast x]]
    consts =
      [SymValue (BoolVal True),
       SymValue (BoolVal False),
       SymValue (IndexVal 0),
       SymValue (IntegerVal 0),
       SymValue (ArrayVal (Array 0 Map.empty)),
       SymValue (SetIntegerVal Set.empty),
       SymValue (SetIndexVal Set.empty)] ++
      concat [[{-SymNot, SymAnd, SymOr,-} SymPlus1, SymPlus2, SymMinus1, SymMinus2{-, SymDiv1, SymDiv2-}] | Arith `elem` categories] ++
      concat
      [map SymRel1 rels ++
       map SymRel2 rels
      | Arith `elem` categories] ++
      concat
      [map SymPairwise1 rels ++
       map SymPairwise2 rels ++
       map SymOrdered rels ++
       [SymAt, SymUpdate, SymLength, SymImage, {-SymConcat,-}
        SymRestrict, SymUnion1, SymUnion2, SymInterval, SymSingleton1, SymSingleton2, SymNull1, SymNull2]
      | Arrays `elem` categories]
    rels = [Le, Lt, Ne]
    tys = [QS.typeOf (undefined :: Integer), QS.typeOf (undefined :: Index), QS.typeOf (undefined :: Bool), QS.typeOf (undefined :: Set Index), QS.typeOf (undefined :: Set Integer), QS.typeOf (undefined :: Array Integer)]

n = 7

-- Just reimplement on top of normal QuickSpec? Program state variable
qs :: Options -> Prog -> StateT Int (Twee.Pruner (WithConstructor Sym) Terminal) ()
qs opts@Options{..} prog =
  (\g -> unGen g (mkQCGen 4321) 0) $
  QuickCheck.run (QuickCheck.Config 1000 20 Nothing) (liftM2 (,) (genFor prog environment) genVars) eval' $ do
    tests <- gets env_tests
    runConditionals [] $
      quickSpec present (flip eval') n univ (enumerator opts prog bound)
  where
    eval' (env, var) t
      | typeArity (typ t) > 0 = Right t
      | isTypeVar (typ t) = Right t
      | otherwise = Left (evalTerm (env, var) t)
    ground _ = True -- XXX
    present prop =
      {-when (ok prop && not (null (intersect [StmtVar found, StmtVar idx] (funs prop)))) $ -} do
        norm <- normaliser
        unless (Silent `elem` options || (Vars `notElem` categories && not (ground prop))) $ do
          n <- lift $ lift get
          lift $ lift $ put $! n+1
          putLine (printf "%3d. " n ++ (prettyShow . fmap fromQS $ canonicalise $ ac norm $ conditionalise prop))
        when (QuickCheck `elem` options) (give prog (liftIO (quickCheck (withMaxSuccess 100 prop))))
    -- ok (_ :=>: t :=: u) | typ t == boolTy, size u > 1 = False
    -- ok _ = True

    -- Transform x+(y+z) = y+(x+z) into associativity, if + is commutative
    ac norm (lhs :=>: App f [QS.Var x, App f1 [QS.Var y, QS.Var z]] :=: App f2 [QS.Var y1, App f3 [QS.Var x1, QS.Var z1]])
      | f == f1, f1 == f2, f2 == f3,
        x == x1, y == y1, z == z1,
        x /= y, y /= z, x /= z,
        norm (App f [QS.Var x, QS.Var y]) == norm (App f [QS.Var y, QS.Var x]) =
          lhs :=>: App f [App f [QS.Var x, QS.Var y], QS.Var z] :=: App f [QS.Var x, App f [QS.Var y, QS.Var z]]
    ac _ prop = prop

    tys = [QS.typeOf (undefined :: Integer), QS.typeOf (undefined :: Index), QS.typeOf (undefined :: Bool), QS.typeOf (undefined :: Set Index), QS.typeOf (undefined :: Set Integer), QS.typeOf (undefined :: Array Integer)]
    univ = conditionalsUniverse tys ([] :: [Sym])

main = do
  -- give bsearch (quickCheck (\env -> testProgOn bsearch env))
  -- quickCheck (forAll (elements tests) $ \env -> testProgOn bsearch env)
  withStdioTerminal $ Twee.run (Twee.Config n maxBound) $ flip evalStateT 0 $ do
    -- qs (Options [Silent] [Vars, Arith] Background) (Body Skip)
    putLine "== background =="
    qs (Options [Silent] [Vars, Arith] Background) (Body Skip)
    qs (Options [] [Vars, Arith, Arrays] Background) (Body Skip)
    putLine ""
    -- putLine "== precondition =="
    -- qs (Options [] [Arith, Arrays, Vars] Precondition) bsearch

    -- putLine "== postcondition =="
    -- qs (Options [] [Arith, Arrays, Vars] Postcondition) bsearch

    -- putLine "== point =="
    -- qs (Options [] [Arith, Arrays, Vars] AtPoint) bsearch

    putLine "== psychic =="
    qs (Options [Silent] [Arith, Arrays, Vars] Postcondition) bsearch
    qs (Options [] [Arith, Arrays, Vars] (PostFrom tests)) bsearch
