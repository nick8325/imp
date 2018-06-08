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
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Twee.Pretty
import Control.Monad
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
import Data.Maybe
import Data.List
import Test.QuickCheck hiding (Ordered)
import Control.Enumerable
import Data.Reflection
import Control.Search hiding (Not, And)
import Control.Spoon
import Control.DeepSeq
import GHC.Generics

data Prog where
  Arg  :: Type a => Var a -> Expr Bool -> Prog -> Prog
  Body :: Stmt -> Prog

body :: Prog -> Stmt
body (Arg _ _ prog) = body prog
body (Body stmt) = stmt

data Stmt where
  (:=) :: Type a => Var a -> Expr a -> Stmt
  Skip :: Stmt
  Then :: Stmt -> Stmt -> Stmt
  If :: Expr Bool -> Stmt -> Stmt -> Stmt
  While :: Expr Bool -> Stmt -> Stmt
  Assert :: Expr Bool -> Stmt
  Point :: Stmt
deriving instance Show Stmt

data Expr a where
  Value :: Type a => Value -> Expr a
  Local :: Type a => Var a -> Expr a
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
  Sorted :: Ord a => Expr (Array a) -> Expr Bool
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
  deriving (Eq, Ord, Show, Generic)
instance NFData Value

shrinkValue :: Value -> [Value]
shrinkValue (IndexVal x) = IndexVal <$> shrink x
shrinkValue (BoolVal x) = BoolVal <$> shrink x
shrinkValue (IntegerVal x) = IntegerVal <$> shrink x
shrinkValue (SetIntegerVal x) = SetIntegerVal <$> shrink x
shrinkValue (SetIndexVal x) = SetIndexVal <$> shrink x
shrinkValue (ArrayVal x) = ArrayVal <$> shrink x

data Array a =
  Array {
    arrayLower :: Index,
    arrayUpper :: Index,
    arrayContents :: Map Index a }
  deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (Array a)

instance Arbitrary a => Arbitrary (Array a) where
  arbitrary = do
    (m, n) <- arbitrary
    let
      lower = min m n
      upper = max m n
    contents <- Map.fromList <$> zip [lower..upper-1] <$> infiniteList
    return (Array lower upper contents)
  shrink arr =
    [shift (l-arrayLower arr) arr | l <- shrink (arrayLower arr)] ++
    [cut n arr | n <- shrink (arrayUpper arr-arrayLower arr), n >= 0]
    where
      shift k arr =
        Array (arrayLower arr+k) (arrayUpper arr+k)
          (Map.mapKeys (+k) (arrayContents arr))
      cut n arr =
        let
          l = arrayLower arr
          u = arrayLower arr + n
        in
          Array l u
            (Map.filterWithKey (\k _ -> k >= l && k < u) (arrayContents arr))

newtype Index = Index Int deriving (Eq, Ord, Show, Num, Enum, Integral, Real, Pretty, Arbitrary, Generic, NFData)

instance Enumerable Index where
  enumerate = datatype [c1 Index]

instance (Ord a, Enumerable a) => Enumerable (Set a) where
  enumerate = datatype [c1 Set.fromList]

instance (Ord a, Enumerable a) => Enumerable (Array a) where
  enumerate = datatype [c2 arr]
    where
      arr base contents =
        Array base (base + fromIntegral (length contents))
          (Map.fromList (zip [base..] contents))

data Var a = Var String deriving (Eq, Ord, Show)

type Env = Map String Value

class (Arbitrary a, Enumerable a) => Type a where
  toValue :: a -> Value
  fromValue :: Value -> Maybe a
  typeName :: a -> String

instance Type Index where
  toValue = IndexVal
  fromValue (IndexVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "index"

instance Type Bool where
  toValue = BoolVal
  fromValue (BoolVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "boolean"

instance Type Integer where
  toValue = IntegerVal
  fromValue (IntegerVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "integer"

instance Type (Set Integer) where
  toValue = SetIntegerVal
  fromValue (SetIntegerVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "set of integer"

instance Type (Set Index) where
  toValue = SetIndexVal
  fromValue (SetIndexVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "set of index"

instance Type (Array Integer) where
  toValue = ArrayVal
  fromValue (ArrayVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "array of integer"

exec :: Env -> Stmt -> ([Env], Env)
exec env (Var x := e) =
  ([], Map.insert x (toValue (eval env e)) env)
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
exec env (While e p) =
  if eval env e
  then exec env (p `Then` While e p)
  else exec env Skip
exec env (Assert e) =
  if eval env e
  then exec env Skip
  else error "assertion failed"
exec env Point =
  ([env], env)

eval :: Env -> Expr a -> a
eval _ (Value x) =
  fromMaybe (error "ill-typed expression") (fromValue x)
eval env (Local (Var x)) =
  fromMaybe (error "ill-typed expression") $ fromValue $
  Map.findWithDefault (error ("variable " ++ x ++ " not bound")) x env
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
eval env (Sorted e) =
  sorted contents
  where
    contents = Map.elems (arrayContents (eval env e))
    sorted [] = True
    sorted [_] = True
    sorted (x:y:xs) = x <= y && sorted (y:xs)
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

genEnv :: Prog -> Gen Env
genEnv = go Map.empty
  where
    go env (Arg (Var x :: Var a) cond prog) = do
      env <-
        (do
           val <- arbitrary :: Gen a
           return (Map.insert x (toValue val) env)) `suchThat`
        (\env -> eval env cond)
      go env prog
    go env (Body _) = return env

shrinkEnv :: Prog -> Env -> [Env]
shrinkEnv prog env =
  filter (checkEnv prog) (map Map.fromList (shr (Map.toList env)))
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
enumEnv (Body _) = c0 Map.empty
enumEnv (Arg (Var x :: Var a) _ prog) =
  ins <$> (access :: Shareable f a) <*> enumEnv prog
  where
    ins val env = Map.insert x (toValue val) env

testProg :: Prog -> IO ()
testProg prog =
  give prog $
  testTime 30 $ \env ->
  not (checkEnv prog env) || isJust (spoon (exec env (body prog)))

instance Given Prog => Enumerable Env where
  enumerate = share (enumEnv given)

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
  pPrint (While e p) =
    text "while" <+> pPrint e <+> text "do" $$
    nest 2 (pPrint p) $$
    text "end"
  pPrint (Assert e) =
    text "assert" <#> parens (pPrint e)
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
            (pPrintPrec l (prec+1) e1 <+> text name) 2
            (pPrintPrec l (prec+1) e2)

      -- Precedence levels:
      -- 0: and, or
      -- 1: relations
      -- 2: not
      -- 3: +, sorted
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
          text "not" <+> pPrintPrec l 3 e
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
        text "lower" <#> parens (exp 0 e)
      exp p (Upper e) =
        text "upper" <#> parens (exp 0 e)
      exp p (Image e) =
        parIf (p > 6) $
          text "image" <#> parens (exp 0 e)
      exp p (Sorted e) =
        parIf (p > 3) $
          text "sorted" <#> parens (exp 0 e)
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

-- evalLHS :: (Env, Var -> Val) -> Equation (Term Fun) -> Bool
-- evalLHS env (t :=: u) = eval env t == eval env u

-- evalRHS :: (Env, Var -> Val) -> Equation (Term Fun) -> Property
-- evalRHS env (t :=: u) = eval env t Test.QuickCheck.=== eval env u

bsearch :: Prog
bsearch =
  Arg arr (Sorted (Local arr)) $
  Arg x (Value (BoolVal True)) $
  Body $
  lo := Lower (Local arr) `Then`
  hi := Upper (Local arr) `Then`
  found := Value (BoolVal False) `Then`
  While (And (Not (Local found)) (Rel Lt (Local lo) (Local hi)))
    (mid := Div (Plus (Local lo) (Local hi)) (Value (IndexVal 2)) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value (BoolVal True) `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         -- (hi := Minus (Local mid) (Value (IndexVal 1)))
         (lo := Plus (Local mid) (Value (IndexVal 1))))) `Then`
  If (Local found)
    (Assert (Rel Eq (At (Local arr) (Local idx)) (Local x)))
    (Assert (Pairwise Ne (Singleton (Local x)) (Image (Local arr))))

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
--       when (ok prop && not (null (intersect [StmtVar found, StmtVar idx] (funs prop)))) $ do
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
