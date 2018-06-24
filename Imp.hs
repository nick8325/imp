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
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Twee.Pretty
import Control.Monad
import QuickSpec.Term hiding (Var, Sized)
import qualified QuickSpec.Term as QS
import Data.Typeable
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
import Test.QuickCheck hiding (Ordered, (==>))
import Control.Enumerable
import Data.Reflection
import Control.Search hiding (Not, And, (|||), (&&&), (==>), nott, true, false)
import Control.Spoon
import Control.DeepSeq
import GHC.Generics
import Data.Function

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
  Lower :: Expr (Array Integer) -> Expr Index
  Upper :: Expr (Array Integer) -> Expr Index
  Image :: (Type (Array a), Ord a) => Expr (Array a) -> Expr (Set a)
  Concat :: Expr Index -> Expr (Array a) -> Expr (Array a) -> Expr (Array a)
  Restrict :: Expr (Array a) -> Expr (Set Index) -> Expr (Array a)
  Sorted :: (Type (Array a), Ord a) => Expr (Array a) -> Expr Bool
  -- Sets
  Interval :: Expr Index -> Expr Index -> Expr (Set Index)
  Singleton1 :: (Type a, Ord a, a ~ Integer) => Expr a -> Expr (Set a)
  Singleton2 :: (Type a, Ord a, a ~ Index) => Expr a -> Expr (Set a)
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
    sub (Lower e) = Lower (rec e)
    sub (Upper e) = Upper (rec e)
    sub (Image e) = Image (rec e)
    sub (Concat e1 e2 e3) = Concat (rec e1) (rec e2) (rec e3)
    sub (Restrict e1 e2) = Restrict (rec e1) (rec e2)
    sub (Sorted e) = Sorted (rec e)
    sub (Interval e1 e2) = Interval (rec e1) (rec e2)
    sub (Singleton1 e) = Singleton1 (rec e)
    sub (Singleton2 e) = Singleton2 (rec e)
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

instance (Ord a, Arbitrary a) => Arbitrary (Array a) where
  arbitrary = do
    (m, n) <- arbitrary
    let
      lower = min m n
      upper = max m n
    permute <- elements [id, sort]
    contents <- Map.fromList <$> zip [lower..] <$> permute <$> vector (fromIntegral (upper-lower))
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
data Unknown a = Skolem Integer deriving (Eq, Ord, Show)

newtype Env = Env (Map String Value)
  deriving (Eq, Ord, Show, NFData, Pretty)

class (Arbitrary a, Enumerable a, Typeable a) => Type a where
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

instance a ~ Integer => Type (Array a) where
  toValue = ArrayVal
  fromValue (ArrayVal x) = Just x
  fromValue _ = Nothing
  typeName _ = "array of integer"

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

eval :: Env -> Expr a -> a
eval _ (Value x) =
  fromMaybe (error "ill-typed expression") (fromValue x)
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
  eval env e1 - eval env e2
eval env (Div1 e1 e2) =
  eval env e1 `div` eval env e2
eval env (Div2 e1 e2) =
  eval env e1 `div` eval env e2
eval env (Rel1 r e1 e2) =
  evalRel r (eval env e1) (eval env e2)
eval env (Rel2 r e1 e2) =
  evalRel r (eval env e1) (eval env e2)
eval env (Pairwise1 r e1 e2) =
  and [evalRel r x y
      | x <- Set.toList (eval env e1),
        y <- Set.toList (eval env e2)]
eval env (Pairwise2 r e1 e2) =
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
eval env (Singleton1 e) =
  Set.singleton (eval env e)
eval env (Singleton2 e) =
  Set.singleton (eval env e)

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

instance Pretty (Expr a) where
  pPrintPrec l p e = exp p e
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
      exp p (Singleton1 e) =
        braces (exp 0 e)
      exp p (Singleton2 e) =
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
    pPrint (arrayContents arr)

instance Pretty (Var a) where
  pPrint (Var x) = text x

data Sym =
  SymValue Value | SymLocal String TypeRep | SymUnknown Integer TypeRep |
  SymNot | SymAnd | SymOr | SymPlus1 | SymPlus2 | SymMinus1 | SymMinus2 | SymDiv1 | SymDiv2 |
  SymRel1 Relation | SymRel2 Relation | SymPairwise1 Relation | SymPairwise2 Relation | SymOrdered Relation |
  SymAt | SymUpdate | SymLower | SymUpper | SymImage | SymConcat |
  SymRestrict | SymSorted | SymInterval | SymSingleton1 | SymSingleton2

toQS :: forall a. Type a => Expr a -> Term Sym
toQS (Value x) = App (SymValue x) []
toQS (Local (Var x)) = App (SymLocal x (typeOf (undefined :: a))) []
toQS (Unknown (Skolem x)) = App (SymUnknown x (typeOf (undefined :: a))) []
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
toQS (Lower e) = App SymLower [toQS e]
toQS (Upper e) = App SymUpper [toQS e]
toQS (Image e) = App SymImage [toQS e]
toQS (Concat e1 e2 e3) = App SymConcat [toQS e1, toQS e2, toQS e3]
toQS (Restrict e1 e2) = App SymRestrict [toQS e1, toQS e2]
toQS (Sorted e) = App SymSorted [toQS e]
toQS (Interval e1 e2) = App SymInterval [toQS e1, toQS e2]
toQS (Singleton1 e) = App SymSingleton1 [toQS e]
toQS (Singleton2 e) = App SymSingleton2 [toQS e]

fromQS :: forall a. Type a => Term Sym -> Maybe (Expr a)
fromQS (App (SymValue x) []) = Just (Value x)
fromQS (App (SymLocal x ty) [])
  | typeOf (undefined :: a) == ty = Just (Local (Var x))
  | otherwise = Nothing
fromQS (App (SymUnknown x ty) [])
  | typeOf (undefined :: a) == ty = Just (Unknown (Skolem x))
  | otherwise = Nothing
fromQS (App SymNot [e]) = (Not <$> fromQS e) >>= cast
fromQS (App SymAnd [e1, e2]) = (And <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymOr [e1, e2]) = (Or <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymPlus1 [e1, e2]) = (Plus1 <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymPlus2 [e1, e2]) = (Plus2 <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymMinus1 [e1, e2]) = (Minus1 <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymMinus2 [e1, e2]) = (Minus2 <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymDiv1 [e1, e2]) = (Div1 <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymDiv2 [e1, e2]) = (Div2 <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App (SymRel1 r) [e1, e2]) = (Rel1 r <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App (SymRel2 r) [e1, e2]) = (Rel2 r <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App (SymPairwise1 r) [e1, e2]) = (Pairwise1 r <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App (SymPairwise2 r) [e1, e2]) = (Pairwise2 r <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App (SymOrdered r) [e1, e2]) = (Ordered r <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymAt [e1, e2]) = (At <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymUpdate [e1, e2, e3]) = (Update <$> fromQS e1 <*> fromQS e2 <*> fromQS e3) >>= cast
fromQS (App SymLower [e]) = (Lower <$> fromQS e) >>= cast
fromQS (App SymUpper [e]) = (Upper <$> fromQS e) >>= cast
fromQS (App SymImage [e]) = (Image <$> fromQS e) >>= cast
fromQS (App SymConcat [e1, e2, e3]) = (Concat <$> fromQS e1 <*> fromQS e2 <*> fromQS e3) >>= cast
fromQS (App SymRestrict [e1, e2]) = (Restrict <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymSorted [e]) = (Sorted <$> fromQS e) >>= cast
fromQS (App SymInterval [e1, e2]) = (Interval <$> fromQS e1 <*> fromQS e2) >>= cast
fromQS (App SymSingleton1 [e]) = (Singleton1 <$> fromQS e) >>= cast
fromQS (App SymSingleton2 [e]) = (Singleton2 <$> fromQS e) >>= cast

bsearch :: Prog
bsearch =
  Arg arr (Sorted (Local arr)) $
  Arg x (Value (BoolVal True)) $
  Body $
  lo := Lower (Local arr) `Then`
  hi := Upper (Local arr) `Then`
  found := Value (BoolVal False) `Then`
  While (And (Not (Local found)) (Rel2 Lt (Local lo) (Local hi))) (Value (BoolVal True))
    (-- Point `Then`
     mid := Div2 (Plus2 (Local lo) (Local hi)) (Value (IndexVal 2)) `Then`
     If (Rel1 Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value (BoolVal True) `Then` idx := Local mid)
       (If (Rel1 Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         -- (hi := Minus (Local mid) (Value (IndexVal 1)))
         (lo := Plus2 (Local mid) (Value (IndexVal 1))))) `Then`
  Point
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
      Env $ Map.fromList [("x", IntegerVal x), ("arr", ArrayVal (Array 0 (Index (length arr)) (Map.fromList (zip [0..] arr))))]

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

main = do
  give bsearch (quickCheck (\env -> testProgOn bsearch env))
  quickCheck (forAll (elements tests) $ \env -> testProgOn bsearch env)
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
