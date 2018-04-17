{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import qualified QuickSpec.Term as QS
import qualified QuickSpec.Pruning.Twee as Twee
import qualified QuickSpec.Testing.QuickCheck as QuickCheck
import QuickSpec.Terminal
import QuickSpec.Pruning.Background(Background)
import QuickSpec.Haskell(arbitraryFunction)
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import QuickSpec.Explore.Conditionals
import QuickSpec.Prop

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

data Val = Int Int | Value Value | Bool Bool | Array [Value] | LePair Value Value | ElemPair Value [Value]
  deriving (Eq, Ord, Show)

instance Typed Val where
  typ Int{} = intTy
  typ Value{} = valueTy
  typ Bool{} = boolTy
  typ Array{} = arrayTy
  typ LePair{} = leTy
  typ ElemPair{} = elemTy
  typeSubst_ _ x = x

instance Pretty Val where
  pPrint (Int x) = pPrint x
  pPrint (Value x) = pPrint x
  pPrint (Bool x) = pPrint x
  pPrint (Array xs) = pPrint xs

instance PrettyTerm Val

type Exp = Term Fun

data ProgVar = V Type String
  deriving (Eq, Ord, Show)

instance Pretty ProgVar where
  pPrint (V _ x) = text x

instance PrettyTerm ProgVar

instance Typed ProgVar where
  typ (V ty _) = ty
  typeSubst_ _ x = x

data Fun =
  Val Val | ProgVar ProgVar |
  Not | And | Eq Type | Le Type |
  Plus | Div |
  Index | Slice | Len | Elem |
  Le1 | Le2 | Elem1 | Elem2
  deriving (Eq, Ord, Show)

instance Arity Fun where
  arity = typeArity . typ

instance Background Fun where

instance Pretty Fun where
  pPrint (Val x) = pPrint x
  pPrint (ProgVar x) = pPrint x
  pPrint Not = text "~"
  pPrint And = text "&"
  pPrint (Eq _) = text "=="
  pPrint (Le _) = text "<="
  pPrint Plus = text "+"
  pPrint Div = text "/"
  pPrint Index = text "!"
  pPrint Slice = text "slice"
  pPrint Len = text "len"
  pPrint Elem = text "in"
  pPrint Le1 = text "le1"
  pPrint Le2 = text "le2"
  pPrint Elem1 = text "elem1"
  pPrint Elem2 = text "elem2"

instance PrettyTerm Fun where
  termStyle (Val x) = termStyle x
  termStyle (ProgVar x) = termStyle x
  termStyle Not = prefix
  termStyle And = infixStyle 5
  termStyle (Eq _) = infixStyle 5
  termStyle (Le _) = infixStyle 5
  termStyle Plus = infixStyle 5
  termStyle Div = infixStyle 5
  termStyle Index = infixStyle 5
  termStyle Elem = infixStyle 5
  termStyle _ = uncurried

instance Typed Fun where
  typ (Val x) = typ x
  typ (ProgVar x) = typ x
  typ Not = arrowType [boolTy] boolTy
  typ And = arrowType [boolTy, boolTy] boolTy
  typ (Eq ty) = arrowType [ty, ty] boolTy
  typ (Le ty) = arrowType [ty, ty] boolTy
  typ Plus = arrowType [intTy, intTy] intTy
  typ Div = arrowType [intTy, intTy] intTy
  typ Index = arrowType [arrayTy, intTy] valueTy
  typ Slice = arrowType [arrayTy, intTy, intTy] arrayTy
  typ Len = arrowType [arrayTy] intTy
  typ Elem = arrowType [valueTy, arrayTy] boolTy
  typ Le1 = arrowType [leTy] valueTy
  typ Le2 = arrowType [leTy] valueTy
  typ Elem1 = arrowType [elemTy] valueTy
  typ Elem2 = arrowType [elemTy] arrayTy
  typeSubst_ _ x = x

int :: Int -> Exp
int x = App (Val (Int x)) []

bool :: Bool -> Exp
bool x = App (Val (Bool x)) []

array :: [Value] -> Exp
array xs = App (Val (Array xs)) []

progVar :: ProgVar -> Exp
progVar x = App (ProgVar x) []

nott :: Exp -> Exp
nott e = App Not [e]

andd :: Exp -> Exp -> Exp
andd e1 e2 = App And [e1, e2]

eq :: Exp -> Exp -> Exp
eq e1 e2 = App (Eq (typ e1)) [e1, e2]

le :: Exp -> Exp -> Exp
le e1 e2 = App (Le (typ e1)) [e1, e2]

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
eval env (App (Eq _) [e1, e2]) =
  Bool (eval env e1 == eval env e2)
eval env (App (Le _) [e1, e2]) =
  let x = eval env e1
      y = eval env e2
  in Bool (x <= y)
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
  in if i >= 0 && i < length xs then Value (xs !! i) else Value (-1)
eval env (App Slice [e1, e2, e3]) =
  let Array xs = eval env e1
      Int i = eval env e2
      Int j = eval env e3
  in Array (drop i (take j xs))
eval env (App Elem [e1, e2]) =
  let Value x = eval env e1
      Array xs = eval env e2
  in Bool (x `elem` xs)
eval env (App Le1 [e]) =
  let LePair x _ = eval env e
  in Value x
eval env (App Le2 [e]) =
  let LePair _ y = eval env e
  in Value y
eval env (App Elem1 [e]) =
  let ElemPair x _ = eval env e
  in Value x
eval env (App Elem2 [e]) =
  let ElemPair _ y = eval env e
  in Array y

bsearch :: Prog
bsearch =
  lo := int 0 `Then`
  hi := len (progVar arr) `Then`
  found := bool False `Then`
  idx := int 0 `Then`
  While (andd (nott (progVar found)) (nott (le (progVar hi) (progVar lo))))
    (mid := divide (plus (progVar lo) (progVar hi)) (int 2) `Then`
     If (eq (progVar x) (index (progVar arr) (progVar mid)))
       (found := bool True `Then` idx := progVar mid)
       (If (le (progVar x) (index (progVar arr) (progVar mid)))
         (hi := plus (progVar mid) (int (-1)))
         (lo := plus (progVar mid) (int 1)))) `Then`
  Point

x, lo, hi, mid, idx, arr, found :: ProgVar
lo = V intTy "lo"
hi = V intTy "hi"
mid = V intTy "mid"
idx = V intTy "idx"
x = V valueTy "x"
arr = V arrayTy "arr"
found = V boolTy "found"

intTy, valueTy, boolTy, arrayTy, leTy, elemTy :: Type
intTy = typeOf (undefined :: Int)
valueTy = typeOf (undefined :: Value)
boolTy = typeOf (undefined :: Bool)
arrayTy = typeOf (undefined :: [Int])
leTy = typeOf (undefined :: LeTy)
elemTy = typeOf (undefined :: ElemTy)

newtype Value = MkValue Int deriving (Eq, Ord, Show, Arbitrary, Num, Pretty)

data LeTy
data ElemTy

bsearchEnv :: Value -> [Value] -> Int -> Int -> Bool -> Int -> Env
bsearchEnv vx varr vlo vhi vfound vidx =
  Map.fromList [(x, Value vx), (arr, Array varr), (lo, Int vlo), (hi, Int vhi), (found, Bool vfound), (idx, Int vidx)]

newtype SortedList a = SortedList [a] deriving (Eq, Ord, Show)

instance (Ord a, Arbitrary a) => Arbitrary (SortedList a) where
  arbitrary = SortedList . sort <$> arbitrary

genEnv :: Gen Env
genEnv = do
  x <- arbitrary
  SortedList xs <- arbitrary
  lo <- arbitrary
  hi <- arbitrary
  found <- arbitrary
  idx <- arbitrary
  return (bsearchEnv x xs lo hi found idx)

genTestCase :: Gen Env
genTestCase = do
  (x, xs) <- elements tests
  lo <- arbitrary
  hi <- arbitrary
  found <- arbitrary
  idx <- arbitrary
  return (bsearchEnv x xs lo hi found idx)

tests :: [(Value, [Value])]
tests = [
  (x1, [x1]),
  (x3, [x1,x2,x3,x4,x5]),
  (x6, [x1,x2,x3,x4]),
  (x4, [x1,x2,x3,x5]),
  (x5, [x1,x2,x3,x5])]
  where
    x1 = -123
    x2 = -6
    x3 = -2
    x4 = 59
    x5 = 102
    x6 = 109

genVars :: Gen (Var -> Val)
genVars =
  arbitraryFunction $ \(QS.V ty _) ->
    case () of
    _ | ty == intTy -> Int <$> arbitrary
      | ty == valueTy -> Value <$> arbitrary
      | ty == boolTy -> Bool <$> arbitrary
      | ty == arrayTy -> Array <$> arbitrary
      | ty == leTy -> do
          x <- arbitrary
          NonNegative k <- arbitrary
          return (LePair x (x+k))
      | ty == elemTy -> do
          xs <- arbitrary `suchThat` (not . null)
          x <- elements xs
          return (ElemPair x xs)

genPoint :: Gen Env -> Gen Env
genPoint gen =
  ((collect undefined bsearch <$> gen) `suchThat` (not . null)) >>= elements

prop_bsearch :: Value -> SortedList Value -> Bool
prop_bsearch x (SortedList xs) =
  found_ == (x `elem` xs) &&
  (not found_ || xs !! idx_ == x)
  where
    res = run undefined bsearch (bsearchEnv x xs undefined undefined undefined undefined)
    Bool found_ = Map.findWithDefault undefined found res
    Int idx_ = Map.findWithDefault undefined idx res

instance Sized Fun where
  size _ = 1

instance Apply (Term Fun) where
  tryApply t@(App f us) u = do
    tryApply (typ t) (typ u)
    return (App f (us ++ [u]))
  tryApply _ _ = Nothing

instance PrettyArity Fun

instance Predicate Fun where
--  classify (Le = Predicate [Le1, Le2] leTy (bool True)
  classify Elem = Predicate [Elem1, Elem2] elemTy (bool True)
--  classify Le1 = Selector 0 Le leTy
--  classify Le2 = Selector 1 Le leTy
  classify Elem1 = Selector 0 Elem elemTy
  classify Elem2 = Selector 1 Elem elemTy
  classify _ = Function

main = do
  quickCheck prop_bsearch
  quickCheck (forAll (elements tests) $ \(x, xs) -> prop_bsearch x (SortedList xs))
  let
    n = 7
    present prop =
      when (ok prop && not (null (intersect [ProgVar found, ProgVar idx] (funs prop)))) $
        putLine (prettyShow (prettyProp (const ["x","y","z"]) (conditionalise prop)))
    ok (_ :=>: t :=: u) | typ t == boolTy, size u > 1 = False
    ok _ = True
    univ = conditionalsUniverse [intTy, valueTy, boolTy, arrayTy] [Elem]
    eval' env t
      | typ t `elem` [intTy, valueTy, boolTy, arrayTy, leTy, elemTy] = Left (eval env t)
      | otherwise = Right t
    enum var =
      sortTerms measure $
      enumerateConstants atomic `mappend` enumerateApplications
      where
        atomic =
          [Var (QS.V typeVar 0) | var] ++
          [progVar x,
           -- progVar lo,
           -- progVar hi,
           -- progVar mid,
           progVar idx,
           progVar arr,
           progVar found,
           App (Val (Bool True)) [],
           App (Val (Array [])) [],
           App (Val (Int 0)) [],
           -- App Not [],
           -- App And [],
           -- App (Eq intTy) [],
           -- App (Eq boolTy) [],
           -- App (Eq arrayTy) [],
           App Elem [],
           App Elem1 [],
           App Elem2 [],
           App (Le intTy) [],
           App (Le valueTy) [],
           App Le1 [],
           App Le2 [],
           App Plus [],
           -- App Div [],
           App Len [],
           App Index [],
           App Slice []]

    qs :: Bool -> Gen Env -> Twee.Pruner (WithConstructor Fun) Terminal ()
    qs var arb =
      (\g -> unGen g (mkQCGen 1234) 0) $
      QuickCheck.run (QuickCheck.Config 1000 100 Nothing) (liftM2 (,) arb genVars) eval' $
      runConditionals [Elem, Le intTy, Le valueTy] $
      quickSpec present (flip eval') n univ (enum var)

  withStdioTerminal $ Twee.run (Twee.Config n maxBound) $ do
    putLine "== background =="
    let
      post env =
        Map.lookup found env == Just (Bool True) ||
        Map.lookup lo env >= Map.lookup hi env 
    qs True (genEnv `suchThat` post)
    putLine ""
    putLine "== foreground =="
    qs False (genPoint genEnv)
    putLine ""
    putLine "== psychic =="
    qs False (genPoint genTestCase)
    -- putLine ""
    -- putLine "== when found is true =="
    -- qs (genPoint genEnv `suchThat` (\env -> Map.lookup found env == Just (Bool True)))
    -- putLine ""
    -- putLine "== psychic when found is true =="
    -- qs (genPoint genTestCase `suchThat` (\env -> Map.lookup found env == Just (Bool True)))
