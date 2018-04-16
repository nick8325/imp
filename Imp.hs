{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

data Val = Int Int | Bool Bool | Array [Int] | LePair Int Int | ElemPair Int [Int]
  deriving (Eq, Ord, Show)

instance Typed Val where
  typ Int{} = intTy
  typ Bool{} = boolTy
  typ Array{} = arrayTy
  typ LePair{} = leTy
  typ ElemPair{} = elemTy
  typeSubst_ _ x = x

instance Pretty Val where
  pPrint (Int x) = pPrint x
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
  Not | And | Eq Type | Le |
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
  pPrint Le = text "<="
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
  termStyle Le = infixStyle 5
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
  typ Le = arrowType [intTy, intTy] boolTy
  typ Plus = arrowType [intTy, intTy] intTy
  typ Div = arrowType [intTy, intTy] intTy
  typ Index = arrowType [arrayTy, intTy] intTy
  typ Slice = arrowType [arrayTy, intTy, intTy] arrayTy
  typ Len = arrowType [arrayTy] intTy
  typ Elem = arrowType [intTy, arrayTy] boolTy
  typ Le1 = arrowType [leTy] intTy
  typ Le2 = arrowType [leTy] intTy
  typ Elem1 = arrowType [elemTy] intTy
  typ Elem2 = arrowType [elemTy] arrayTy
  typeSubst_ _ x = x

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
eq e1 e2 = App (Eq (typ e1)) [e1, e2]

le :: Exp -> Exp -> Exp
le e1 e2 = App Le [e1, e2]

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
eval env (App Le [e1, e2]) =
  let Int x = eval env e1
      Int y = eval env e2
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
  in if i >= 0 && i < length xs then Int (xs !! i) else Int (-1)
eval env (App Slice [e1, e2, e3]) =
  let Array xs = eval env e1
      Int i = eval env e2
      Int j = eval env e3
  in Array (drop i (take j xs))
eval env (App Elem [e1, e2]) =
  let Int x = eval env e1
      Array xs = eval env e2
  in Bool (x `elem` xs)
eval env (App Le1 [e]) =
  let LePair x _ = eval env e
  in Int x
eval env (App Le2 [e]) =
  let LePair _ y = eval env e
  in Int y
eval env (App Elem1 [e]) =
  let ElemPair x _ = eval env e
  in Int x
eval env (App Elem2 [e]) =
  let ElemPair _ y = eval env e
  in Array y

bsearch :: Prog
bsearch =
  lo := int 0 `Then`
  hi := len (progVar arr) `Then`
  found := bool False `Then`
  While (andd (nott (progVar found)) (nott (eq (progVar lo) (progVar hi))))
    (Point `Then`
     mid := divide (plus (progVar lo) (progVar hi)) (int 2) `Then`
     If (eq (progVar x) (index (progVar arr) (progVar mid)))
       (found := bool True `Then` idx := progVar mid)
       (If (le (progVar x) (index (progVar arr) (progVar mid)))
         (hi := progVar mid)
         (lo := plus (progVar mid) (int 1))))

x, lo, hi, mid, idx, arr, found :: ProgVar
lo = V intTy "lo"
hi = V intTy "hi"
mid = V intTy "mid"
idx = V intTy "idx"
x = V intTy "x"
arr = V arrayTy "arr"
found = V boolTy "found"

intTy, boolTy, arrayTy, leTy, elemTy :: Type
intTy = typeOf (undefined :: Int)
boolTy = typeOf (undefined :: Bool)
arrayTy = typeOf (undefined :: [Int])
leTy = typeOf (undefined :: LeTy)
elemTy = typeOf (undefined :: ElemTy)

data LeTy
data ElemTy

bsearchEnv :: Int -> [Int] -> Int -> Int -> Bool -> Env
bsearchEnv vx varr vlo vhi vfound =
  Map.fromList [(x, Int vx), (arr, Array varr), (lo, Int vlo), (hi, Int vhi), (found, Bool vfound)]

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
  return (bsearchEnv x xs lo hi found)

genVars :: Gen (Var -> Val)
genVars =
  arbitraryFunction $ \(QS.V ty _) ->
    case () of
    _ | ty == intTy -> Int <$> arbitrary
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

genPoint :: Gen Env
genPoint =
  ((collect undefined bsearch <$> genEnv) `suchThat` (not . null)) >>= elements

prop_bsearch :: Int -> SortedList Int -> Bool
prop_bsearch x (SortedList xs) =
  found_ == (x `elem` xs) &&
  (not found_ || xs !! mid_ == x)
  where
    res = run undefined bsearch (bsearchEnv x xs undefined undefined undefined)
    Bool found_ = Map.findWithDefault undefined found res
    Int mid_ = Map.findWithDefault undefined mid res

instance Sized Fun where
  size _ = 1

instance Apply (Term Fun) where
  tryApply t@(App f us) u = do
    tryApply (typ t) (typ u)
    return (App f (us ++ [u]))
  tryApply _ _ = Nothing

instance Predicate Fun where
  classify Le = Predicate [Le1, Le2] leTy (bool True)
  classify Elem = Predicate [Elem1, Elem2] elemTy (bool True)
  classify Le1 = Selector 0 Le leTy
  classify Le2 = Selector 1 Le leTy
  classify Elem1 = Selector 0 Elem elemTy
  classify Elem2 = Selector 1 Elem elemTy
  classify _ = Function

main = do
  let
    n = 7
    present prop = putLine (prettyShow (conditionalise prop))
    univ = conditionalsUniverse [intTy, boolTy, arrayTy] [Elem, Le]
    eval' env t
      | typ t `elem` [intTy, boolTy, arrayTy, leTy, elemTy] = Left (eval env t)
      | otherwise = Right t
    enum =
      sortTerms measure $
      enumerateConstants atomic `mappend` enumerateApplications
      where
        atomic =
          [Var (QS.V typeVar 0),
           progVar x,
           progVar lo,
           progVar hi,
           -- progVar mid,
           -- progVar idx,
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
           App Le [],
           App Le1 [],
           App Le2 [],
           App Plus [],
           -- App Div [],
           App Index [],
           App Slice [],
           App Len []]

    qs :: Gen Env -> Twee.Pruner (WithConstructor Fun) Terminal ()
    qs arb =
      (\g -> unGen g (mkQCGen 1234) 0) $
      QuickCheck.run (QuickCheck.Config 1000 10 Nothing) (liftM2 (,) arb genVars) eval' $
      runConditionals [Elem, Le] $
      quickSpec present (flip eval') n univ enum

  withStdioTerminal $ Twee.run (Twee.Config n maxBound) $ do
    putLine "== background =="
    qs genEnv
    putLine ""
    putLine "== foreground =="
    qs genPoint
