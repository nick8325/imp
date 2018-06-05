{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- import Prelude hiding (lookup)
-- import Control.Monad.Reader
-- import Control.Monad.State.Strict
-- import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Twee.Pretty
-- import Data.List hiding (lookup)
-- import Data.Maybe
-- import Data.Typeable(cast)
-- import Test.QuickCheck hiding (Fun, collect)
-- import QuickSpec.Explore
-- import QuickSpec.Explore.Polymorphic
-- import QuickSpec.Type hiding (Value, cast)
-- import QuickSpec.Term hiding (V, int)
-- import qualified QuickSpec.Term as QS
-- import qualified QuickSpec.Pruning.Twee as Twee
-- import qualified QuickSpec.Testing.QuickCheck as QuickCheck
-- import QuickSpec.Terminal
-- import QuickSpec.Pruning.Background(Background)
-- import QuickSpec.Haskell(arbitraryFunction)
-- import Test.QuickCheck.Gen
-- import Test.QuickCheck.Random
-- import QuickSpec.Explore.Conditionals
-- import QuickSpec.Prop
import Data.Typeable
import Data.Maybe

data Prog where
  (:=) :: Var a -> Expr a -> Prog
  Skip :: Prog
  Then :: Prog -> Prog -> Prog
  If :: Expr Bool -> Prog -> Prog -> Prog
  While :: Expr Bool -> Prog -> Prog
  Assert :: Expr Bool -> Prog
  Point :: Prog
deriving instance Show Prog

data Expr a where
  Value :: Typeable a => Value -> Expr a
  Local :: Typeable a => Var a -> Expr a
  -- Boolean expressions
  Not :: Expr Bool -> Expr Bool
  And :: Expr Bool -> Expr Bool -> Expr Bool
  Or  :: Expr Bool -> Expr Bool -> Expr Bool
  -- Arithmetic expressions
  Plus :: Num a => Expr a -> Expr a -> Expr a
  Minus :: Num a => Expr a -> Expr a -> Expr a
  Div  :: Integral a => Expr a -> Expr a -> Expr a
  -- Relations
  Rel :: Ord a => Relation -> Expr a -> Expr a -> Expr Bool
  Pairwise :: Ord a => Relation -> Expr (Set a) -> Expr (Set a) -> Expr Bool
  Ordered :: Ord a => Relation -> Expr (Array a) -> Expr (Array a) -> Expr Bool
  -- Arrays
  At :: Expr (Array a) -> Expr Index -> Expr a
  Update :: Ord a => Expr (Array a) -> Expr Index -> Expr a -> Expr (Array a)
  Lower :: Expr (Array a) -> Expr Index
  Upper :: Expr (Array a) -> Expr Index
  Image :: Ord a => Expr (Array a) -> Expr (Set a)
  Concat :: Expr Index -> Expr (Array a) -> Expr (Array a) -> Expr (Array a)
  Restrict :: Expr (Array a) -> Expr (Set Index) -> Expr (Array a)
  -- Sets
  Interval :: Expr Index -> Expr Index -> Expr (Set Index)
  Singleton :: Ord a => Expr a -> Expr (Set a)
deriving instance Show (Expr a)

data Relation = Eq | Ne | Le | Lt | Ge | Gt deriving (Eq, Ord, Show)

infixr 4 `Then`
infix 5 :=

data Value =
  IndexVal Index | BoolVal Bool | IntegerVal Integer |
  SetIntegerVal (Set Integer) | SetIndexVal (Set Index) |
  ArrayVal (Array Integer)
  deriving (Eq, Ord, Show)

data Array a =
  Array {
    arrayLower :: Index,
    arrayUpper :: Index,
    arrayContents :: Map Index a }
  deriving (Eq, Ord, Show)
newtype Index = Index Int deriving (Eq, Ord, Show, Num, Enum, Integral, Real, Pretty)

data Var a = Var String deriving (Eq, Ord, Show)

type Env = Map String Value

fromValue :: Typeable a => Value -> Maybe a
fromValue (IndexVal x) = cast x
fromValue (BoolVal x) = cast x
fromValue (IntegerVal x) = cast x
fromValue (SetIntegerVal x) = cast x
fromValue (SetIndexVal x) = cast x
fromValue (ArrayVal x) = cast x

eval :: Env -> Expr a -> a
eval _ (Value x) =
  fromMaybe (error "ill-typed expression") (fromValue x)
eval env (Local (Var x)) =
  fromMaybe (error "ill-typed expression") $
  fromValue $
  fromMaybe (error ("variable " ++ x ++ " not bound")) $
  Map.lookup x env
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
  eval env e1 `div` eval env e2
eval env (Rel r e1 e2) =
  evalRel r (eval env e1) (eval env e2)
eval env (Pairwise r e1 e2) =
  and [evalRel r x y
      | x <- Set.toList (eval env e1),
        y <- Set.toList (eval env e2)]
eval env (Ordered r e1 e2) =
  and [evalRel r x y
      | (i, x) <- Map.toList (arrayContents (eval env e1)),
        (j, y) <- Map.toList (arrayContents (eval env e2)),
        i < j ]
eval env (At e1 e2) =
  fromMaybe (error "out-of-bounds array access") $
  Map.lookup (eval env e2) (arrayContents (eval env e1))
eval env (Update e1 e2 e3) =
  arr {
    arrayContents =
      Map.insert idx val (arrayContents arr) }
  where
    arr = eval env e1
    idx = eval env e2
    val = eval env e3
eval env (Lower e) =
  arrayLower (eval env e)
eval env (Upper e) =
  arrayUpper (eval env e)
eval env (Image e) =
  Set.fromList (Map.elems (arrayContents (eval env e)))
eval env (Concat e1 e2 e3) =
  Array base (base + len1 + len2)
    (shift (base - lo1) xs1 `Map.union`
     shift (base + len1 - lo2) xs2)
  where
    base = eval env e1
    Array lo1 hi1 xs1 = eval env e2
    Array lo2 hi2 xs2 = eval env e3
    len1 = hi1 - lo1
    len2 = hi2 - lo2
    shift k = Map.mapKeys (+k)
eval env (Restrict e1 e2) =
  arr {
    arrayContents = Map.restrictKeys (arrayContents arr) (eval env e2) }
  where
    arr = eval env e1
eval env (Interval e1 e2) =
  Set.fromList [eval env e1..eval env e2-1]
eval env (Singleton e) =
  Set.singleton (eval env e)

evalRel :: Ord a => Relation -> a -> a -> Bool
evalRel Eq = (==)
evalRel Ne = (/=)
evalRel Lt = (<)
evalRel Le = (<=)
evalRel Gt = (>)
evalRel Ge = (>=)

instance Pretty Prog where
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
  pPrint (While e p) =
    text "while" <+> pPrint e <+> text "do" $$
    nest 2 (pPrint p) $$
    text "end"
  pPrint (Assert e) =
    text "{" <+> pPrint e <+> text "}"
  pPrint Point =
    text "{ ? }"

instance Pretty (Expr a) where
  pPrintPrec l p e = exp 0 e
    where
      parIf True x = parens x
      parIf False x = x

      oper :: Rational -> Rational -> String -> Expr b -> Expr c -> Doc
      oper p prec name e1 e2 =
        parIf (p > prec) $
          hang
            (pPrintPrec l (p+1) e1 <+> text name) 2
            (pPrintPrec l (p+1) e2)

      -- Precedence levels:
      -- 0: and, or
      -- 1: relations
      -- 2: not
      -- 3: +
      -- 4: div
      -- 5: restrict
      -- 6: image
      exp :: Rational -> Expr b -> Doc
      exp _ (Value x) =
        pPrint x
      exp _ (Local x) =
        pPrint x
      exp p (Not e) =
        parIf (p > 2) $
          text "not" <+> pPrintPrec l (p+1) e
      exp p (And e1 e2) =
        oper p 0 "and" e1 e2
      exp p (Or e1 e2) =
        oper p 0 "or" e1 e2
      exp p (Plus e1 e2) =
        oper p 3 "+" e1 e2
      exp p (Minus e1 e2) =
        oper p 3 "-" e1 e2
      exp p (Div e1 e2) =
        oper p 4 "div" e1 e2
      exp p (Rel r e1 e2) =
        oper p 1 (rel r) e1 e2
      exp p (Pairwise r e1 e2) =
        oper p 1 (rel r ++ "*") e1 e2
      exp p (Ordered r e1 e2) =
        oper p 1 (rel r ++ "O") e1 e2
      exp p (At e1 e2) =
        exp inf e1 <#> brackets (exp 0 e2)
      exp p (Update e1 e2 e3) =
        exp inf e1 <#> braces (exp 0 e2 <+> text "->" <#> exp 0 e3)
      exp p (Lower e) =
        text "lower" <+> exp inf e
      exp p (Upper e) =
        text "upper" <+> exp inf e
      exp p (Image e) =
        parIf (p > 6) $
          text "image" <+> exp 7 e
      exp p (Concat e1 e2 e3) =
        text "concat" <#> parens (fsep (punctuate (text ", ") [exp 0 e1, exp 0 e2, exp 0 e3]))
      exp p (Restrict e1 e2) =
        oper p 5 "/" e1 e2
      exp p (Interval e1 e2) =
        text "[" <#>
        cat [exp 0 e1 <#> text "..", exp 0 e2 <#> text ")"]
      exp p (Singleton e) =
        braces (exp 0 e)
  
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
    brackets (pPrint (arrayLower arr) <> text ".." <> pPrint (arrayUpper arr)) <>
    pPrint (arrayContents arr)

instance Pretty (Var a) where
  pPrint (Var x) = text x

-- blah
-- blah
  

-- run :: (Var -> Val) -> Prog -> Env -> Env
-- run var p env = runReader (execStateT (exec (return ()) p) env) var

-- collect :: (Var -> Val) -> Prog -> Env -> [Env]
-- collect var p env =
--   runReader (execWriterT (execStateT (exec (get >>= tell . return) p) env)) var

-- exec :: (MonadState Env m, MonadReader (Var -> Val) m) => m () -> Prog -> m ()
-- exec point (If e p1 p2) = do
--   Bool x <- evalM e
--   if x then exec point p1 else exec point p2
-- exec point (While e p) = do
--   Bool x <- evalM e
--   when x $ do { exec point p; exec point (While e p) }
-- exec point (p1 `Then` p2) = do
--   exec point p1
--   exec point p2
-- exec _ Skip = return ()
-- exec point Point = point
-- exec _ (x := e) = do
--   y <- evalM e
--   modify (Map.insert x y)

-- evalM :: (MonadState Env m, MonadReader (Var -> Val) m) => Exp -> m Val
-- evalM exp = do
--   env <- get
--   var <- ask
--   return (eval (env, var) exp)

-- instance Arbitrary Val where
--   shrink (Int x) = Int <$> shrink x
--   shrink (Value x) = Value <$> shrink x
--   shrink (Bool x) = Bool <$> shrink x
--   shrink (Array xs) = Array <$> sort <$> shrink xs
--   shrink _ = []

-- instance Typed Val where
--   typ Int{} = intTy
--   typ Value{} = valueTy
--   typ Bool{} = boolTy
--   typ Array{} = arrayTy
--   typ LePair{} = leTy
--   typ ElemPair{} = elemTy
--   typeSubst_ _ x = x

-- instance Pretty Val where
--   pPrint (Int x) = pPrint x
--   pPrint (Value x) = pPrint x
--   pPrint (Bool x) = pPrint x
--   pPrint (Array xs) = pPrint xs

-- instance PrettyTerm Val

-- instance Pretty ProgVar where
--   pPrint (V _ x) = text x

-- instance PrettyTerm ProgVar

-- instance Typed ProgVar where
--   typ (V ty _) = ty
--   typeSubst_ _ x = x

-- instance Arity Fun where
--   arity = typeArity . typ

-- instance Background Fun where

-- instance Pretty Fun where
--   pPrint (Val x) = pPrint x
--   pPrint (ProgVar x) = pPrint x
--   pPrint Not = text "~"
--   pPrint And = text "&"
--   pPrint (Eq _) = text "=="
--   pPrint (Le _) = text "<="
--   pPrint Plus = text "+"
--   pPrint Div = text "/"
--   pPrint Index = text "!"
--   pPrint Slice = text "slice"
--   pPrint Len = text "len"
--   pPrint Elem = text "in"
--   pPrint Le1 = text "le1"
--   pPrint Le2 = text "le2"
--   pPrint Elem1 = text "elem1"
--   pPrint Elem2 = text "elem2"

-- instance PrettyTerm Fun where
--   termStyle (Val x) = termStyle x
--   termStyle (ProgVar x) = termStyle x
--   termStyle Not = prefix
--   termStyle And = infixStyle 5
--   termStyle (Eq _) = infixStyle 5
--   termStyle (Le _) = infixStyle 5
--   termStyle Plus = infixStyle 5
--   termStyle Div = infixStyle 5
--   termStyle Index = infixStyle 5
--   termStyle Elem = infixStyle 5
--   termStyle _ = uncurried

-- instance Typed Fun where
--   typ (Val x) = typ x
--   typ (ProgVar x) = typ x
--   typ Not = arrowType [boolTy] boolTy
--   typ And = arrowType [boolTy, boolTy] boolTy
--   typ (Eq ty) = arrowType [ty, ty] boolTy
--   typ (Le ty) = arrowType [ty, ty] boolTy
--   typ Plus = arrowType [intTy, intTy] intTy
--   typ Div = arrowType [intTy, intTy] intTy
--   typ Index = arrowType [arrayTy, intTy] valueTy
--   typ Slice = arrowType [arrayTy, intTy, intTy] arrayTy
--   typ Len = arrowType [arrayTy] intTy
--   typ Elem = arrowType [valueTy, arrayTy] boolTy
--   typ Le1 = arrowType [leTy] valueTy
--   typ Le2 = arrowType [leTy] valueTy
--   typ Elem1 = arrowType [elemTy] valueTy
--   typ Elem2 = arrowType [elemTy] arrayTy
--   typeSubst_ _ x = x

-- evalLHS :: (Env, Var -> Val) -> Equation (Term Fun) -> Bool
-- evalLHS env (t :=: u) = eval env t == eval env u

-- evalRHS :: (Env, Var -> Val) -> Equation (Term Fun) -> Property
-- evalRHS env (t :=: u) = eval env t Test.QuickCheck.=== eval env u

-- eval :: (Env, Var -> Val) -> Term Fun -> Val
-- eval _ (App (Val x) []) = x
-- eval (_, env) (Var x) = env x
-- eval (env, _) (App (ProgVar x) []) =
--   Map.findWithDefault undefined x env
-- eval env (App Len [e]) =
--   let Array xs = eval env e in
--   Int (length xs)
-- eval env (App Not [e]) =
--   let Bool x = eval env e in
--   Bool (not x)
-- eval env (App And [e1, e2]) =
--   let Bool x = eval env e1
--       Bool y = eval env e2
--   in Bool (x && y)
-- eval env (App (Eq _) [e1, e2]) =
--   Bool (eval env e1 == eval env e2)
-- eval env (App (Le _) [e1, e2]) =
--   let x = eval env e1
--       y = eval env e2
--   in Bool (x <= y)
-- eval env (App Plus [e1, e2]) =
--   let Int x = eval env e1
--       Int y = eval env e2
--   in Int (x + y)
-- eval env (App Div [e1, e2]) =
--   let Int x = eval env e1
--       Int y = eval env e2
--   in Int (x `div` y)
-- eval env (App Index [e1, e2]) =
--   let Array xs = eval env e1
--       Int i = eval env e2
--   in if i >= 0 && i < length xs then Value (xs !! i) else Value (-1)
-- eval env (App Slice [e1, e2, e3]) =
--   let Array xs = eval env e1
--       Int i = eval env e2
--       Int j = eval env e3
--   in Array (drop i (take j xs))
-- eval env (App Elem [e1, e2]) =
--   let Value x = eval env e1
--       Array xs = eval env e2
--   in Bool (x `elem` xs)
-- eval env (App Le1 [e]) =
--   let LePair x _ = eval env e
--   in Value x
-- eval env (App Le2 [e]) =
--   let LePair _ y = eval env e
--   in Value y
-- eval env (App Elem1 [e]) =
--   let ElemPair x _ = eval env e
--   in Value x
-- eval env (App Elem2 [e]) =
--   let ElemPair _ y = eval env e
--   in Array y

bsearch :: Prog
bsearch =
  lo := Lower (Local arr) `Then`
  hi := Upper (Local arr) `Then`
  found := Value (BoolVal False) `Then`
  While (And (Not (Local found)) (Rel Lt (Local lo) (Local hi)))
    (Assert (Not (Local found)) `Then`
     Assert (Pairwise Ne (Singleton (Local x)) (Image (Restrict (Local arr) (Interval (Lower (Local arr)) (Local lo))))) `Then`
     mid := Div (Plus (Local lo) (Local hi)) (Value (IndexVal 2)) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value (BoolVal True) `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         (hi := Minus (Local mid) (Value (IndexVal 1)))
         (lo := Plus (Local mid) (Value (IndexVal 1))))) `Then`
  Point

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

-- intTy, valueTy, boolTy, arrayTy, leTy, elemTy :: Type
-- intTy = typeOf (undefined :: Int)
-- valueTy = typeOf (undefined :: Value)
-- boolTy = typeOf (undefined :: Bool)
-- arrayTy = typeOf (undefined :: [Int])
-- leTy = typeOf (undefined :: LeTy)
-- elemTy = typeOf (undefined :: ElemTy)

-- newtype Value = MkValue Int deriving (Eq, Ord, Show, Arbitrary, Num, Pretty)

-- data LeTy
-- data ElemTy

-- bsearchEnv :: Value -> [Value] -> Int -> Int -> Bool -> Int -> Env
-- bsearchEnv vx varr vlo vhi vfound vidx =
--   Map.fromList [(x, Value vx), (arr, Array varr), (lo, Int vlo), (hi, Int vhi), (found, Bool vfound), (idx, Int vidx)]

-- newtype SortedList a = SortedList [a] deriving (Eq, Ord, Show)

-- instance (Ord a, Arbitrary a) => Arbitrary (SortedList a) where
--   arbitrary = SortedList . sort <$> arbitrary

-- genEnv :: Gen Env
-- genEnv = do
--   x <- arbitrary
--   SortedList xs <- arbitrary
--   lo <- arbitrary
--   hi <- arbitrary
--   found <- arbitrary
--   idx <- arbitrary
--   return (bsearchEnv x xs lo hi found idx)

-- genTestCase :: Gen Env
-- genTestCase = do
--   (x, xs) <- elements tests
--   lo <- arbitrary
--   hi <- arbitrary
--   found <- arbitrary
--   idx <- arbitrary
--   return (bsearchEnv x xs lo hi found idx)

-- tests :: [(Value, [Value])]
-- tests = [
--   (x1, [x1]),
--   (x3, [x1,x2,x3,x4,x5]),
--   (x6, [x1,x2,x3,x4]),
--   (x4, [x1,x2,x3,x5]),
--   (x5, [x1,x2,x3,x5])]
--   where
--     x1 = -123
--     x2 = -6
--     x3 = -2
--     x4 = 59
--     x5 = 102
--     x6 = 109

-- genVars :: Gen (Var -> Val)
-- genVars =
--   arbitraryFunction $ \(QS.V ty _) ->
--     case () of
--     _ | ty == intTy -> Int <$> arbitrary
--       | ty == valueTy -> Value <$> arbitrary
--       | ty == boolTy -> Bool <$> arbitrary
--       | ty == arrayTy -> Array <$> arbitrary
--       | ty == leTy -> do
--           x <- arbitrary
--           NonNegative k <- arbitrary
--           return (LePair x (x+k))
--       | ty == elemTy -> do
--           xs <- arbitrary `suchThat` (not . null)
--           x <- elements xs
--           return (ElemPair x xs)

-- genPoint :: Gen Env -> Gen Env
-- genPoint gen =
--   ((collect undefined bsearch <$> gen) `suchThat` (not . null)) >>= elements

-- prop_bsearch :: Value -> SortedList Value -> Bool
-- prop_bsearch x (SortedList xs) =
--   found_ == (x `elem` xs) &&
--   (not found_ || xs !! idx_ == x)
--   where
--     res = run undefined bsearch (bsearchEnv x xs undefined undefined undefined undefined)
--     Bool found_ = Map.findWithDefault undefined found res
--     Int idx_ = Map.findWithDefault undefined idx res

-- instance Sized Fun where
--   size _ = 1

-- instance Apply (Term Fun) where
--   tryApply t@(App f us) u = do
--     tryApply (typ t) (typ u)
--     return (App f (us ++ [u]))
--   tryApply _ _ = Nothing

-- instance PrettyArity Fun

-- instance Predicate Fun where
-- --  classify (Le = Predicate [Le1, Le2] leTy (bool True)
--   classify Elem = Predicate [Elem1, Elem2] elemTy (bool True)
-- --  classify Le1 = Selector 0 Le leTy
-- --  classify Le2 = Selector 1 Le leTy
--   classify Elem1 = Selector 0 Elem elemTy
--   classify Elem2 = Selector 1 Elem elemTy
--   classify _ = Function

-- instance Testable (Prop (Term Fun)) where
--   property (lhs :=>: rhs) =
--     forAllShrink genEnv (map Map.fromList . shrinkElements . Map.toList) $ \env0 ->
--       let env = run undefined bsearch env0 in
--       counterexample ("arr = " ++ show (Map.findWithDefault undefined arr env)) $
--       counterexample ("x = " ++ show (Map.findWithDefault undefined x env)) $
--       foldr (==>) (evalRHS (env, undefined) rhs) (map (evalLHS (env, undefined)) lhs)
--     where
--       shrinkElements [] = []
--       shrinkElements ((k,x):xs) = [(k,y):xs | y<- shrink x] ++ [(k,x):ys | ys <- shrinkElements xs]

-- main = do
--   quickCheck prop_bsearch
--   quickCheck (forAll (elements tests) $ \(x, xs) -> prop_bsearch x (SortedList xs))
--   let
--     n = 7
--     present qc prop =
--       when (ok prop && not (null (intersect [ProgVar found, ProgVar idx] (funs prop)))) $ do
--         putLine (prettyShow (prettyProp (const ["x","y","z"]) (conditionalise prop)))
--         when qc (liftIO (quickCheck prop))
--     ok (_ :=>: t :=: u) | typ t == boolTy, size u > 1 = False
--     ok _ = True
--     univ = conditionalsUniverse [intTy, valueTy, boolTy, arrayTy] [Elem]
--     eval' env t
--       | typ t `elem` [intTy, valueTy, boolTy, arrayTy, leTy, elemTy] = Left (eval env t)
--       | otherwise = Right t
--     enum var =
--       sortTerms measure $
--       enumerateConstants atomic `mappend` enumerateApplications
--       where
--         atomic =
--           [Var (QS.V typeVar 0) | var] ++
--           [progVar x,
--            -- progVar lo,
--            -- progVar hi,
--            -- progVar mid,
--            progVar idx,
--            progVar arr,
--            progVar found,
--            App (Val (Bool True)) [],
--            App (Val (Array [])) [],
--            App (Val (Int 0)) [],
--            -- App Not [],
--            -- App And [],
--            -- App (Eq intTy) [],
--            -- App (Eq boolTy) [],
--            -- App (Eq arrayTy) [],
--            App Elem [],
--            App Elem1 [],
--            App Elem2 [],
--            App (Le intTy) [],
--            App (Le valueTy) [],
--            App Le1 [],
--            App Le2 [],
--            App Plus [],
--            -- App Div [],
--            App Len [],
--            App Index [],
--            App Slice []]

--     qs :: Bool -> Bool -> Gen Env -> Twee.Pruner (WithConstructor Fun) Terminal ()
--     qs qc var arb =
--       (\g -> unGen g (mkQCGen 1234) 0) $
--       QuickCheck.run (QuickCheck.Config 1000 100 Nothing) (liftM2 (,) arb genVars) eval' $
--       runConditionals [Elem, Le intTy, Le valueTy] $
--       quickSpec (present qc) (flip eval') n univ (enum var)

--   withStdioTerminal $ Twee.run (Twee.Config n maxBound) $ do
--     putLine "== background =="
--     let
--       post env =
--         Map.lookup found env == Just (Bool True) ||
--         Map.lookup lo env >= Map.lookup hi env 
--     qs False True (genEnv `suchThat` post)
--     putLine ""
--     putLine "== foreground =="
--     qs False False (genPoint genEnv)
--     putLine ""
--     putLine "== psychic =="
--     qs True False (genPoint genTestCase)
--     -- putLine ""
--     -- putLine "== when found is true =="
--     -- qs (genPoint genEnv `suchThat` (\env -> Map.lookup found env == Just (Bool True)))
--     -- putLine ""
--     -- putLine "== psychic when found is true =="
--     -- qs (genPoint genTestCase `suchThat` (\env -> Map.lookup found env == Just (Bool True)))
