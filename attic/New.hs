{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
module New(module New, module QuickSpec, pPrint, quickCheck) where
import Twee.Pretty
import Test.QuickCheck hiding (Ordered, (==>))
import QuickSpec.Internal.Type(typ, typeOf)
import qualified QuickSpec.Internal.Haskell as Haskell
import qualified QuickSpec.Internal.Term as Term
import Control.DeepSeq
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import Data.Monoid
import qualified Data.Map.Strict as Map
import Data.Reflection
import Data.Typeable hiding (typeOf)
import Data.Functor.Identity
import GHC.Generics
import Data.List
import Data.Function
import Data.Maybe
import Data.Functor.Classes
import QuickSpec.Internal hiding (arith)
import QuickSpec hiding (arith)
import qualified QuickSpec.Internal.Haskell as QSH
import Data.Constraint()
import Test.QuickCheck.Random
import Test.QuickCheck.Gen
import Numeric.Natural
import Debug.Trace
import Psychic

data Prog where
  Arg  :: Type a => Var a -> Expr Bool -> Prog -> Prog
  Body :: Stmt -> Prog

instance Show Prog where
  show = prettyShow

data Stmt where
  (:=) :: Type a => Var a -> Expr a -> Stmt
  Skip :: Stmt
  Then :: Stmt -> Stmt -> Stmt
  If :: Expr Bool -> Stmt -> Stmt -> Stmt
  While :: Expr Bool -> Expr Bool -> Stmt -> Stmt
  Assert :: Expr Bool -> Stmt
  Point :: Stmt
deriving instance Show Stmt

infixr 4 `Then`
infix 5 :=

data Expr a where
  Value   :: Type a => a -> Expr a
  Local   :: Type a => Var a -> Expr a
  -- Boolean expressions
  Not :: Expr Bool -> Expr Bool
  And :: Expr Bool -> Expr Bool -> Expr Bool
  Or  :: Expr Bool -> Expr Bool -> Expr Bool
  -- Arithmetic expressions
  Plus :: (Type a, Num a) => Expr a -> Expr a -> Expr a
  Minus :: (Type a, Num a) => Expr a -> Expr a -> Expr a
  Div  :: (Type a, Integral a) => Expr a -> Expr a -> Expr a
  -- Relations
  Rel :: (Type a, Ord a, Num a) => Relation -> Expr a -> Expr a -> Expr Bool
  Pairwise :: (Type a, Ord a, Num a) => Relation -> Expr (Set a) -> Expr (Set a) -> Expr Bool
  Ordered :: (Type a, Ord a, Num a) => Relation -> Expr (Array a) -> Expr Bool
  -- Arrays
  At :: Num a => Expr (Array a) -> Expr Index -> Expr a
  Update :: (Type a, Ord a) => Expr (Array a) -> Expr Index -> Expr a -> Expr (Array a)
  Length :: Expr (Array Integer) -> Expr Index
  Image :: (Type (Array a), Ord a) => Expr (Array a) -> Expr (Set a)
  Concat :: Expr (Array a) -> Expr (Array a) -> Expr (Array a)
  Restrict :: Expr (Array a) -> Expr (Set Index) -> Expr (Array a)
  -- Sets
  Interval :: Expr Index -> Expr Index -> Expr (Set Index)
  Union :: (Type a, Ord a) => Expr (Set a) -> Expr (Set a) -> Expr (Set a)
  Singleton :: (Type a, Ord a) => Expr a -> Expr (Set a)
  Null :: Expr (Set a) -> Expr Bool
deriving instance Show (Expr a)

data Relation = Eq | Ne | Le | Lt | Ge | Gt deriving (Eq, Ord, Show)

instance Arbitrary Relation where
  arbitrary = elements [Eq, Ne, Le, Lt, Ge, Gt]

data Some f where
  Some :: Type a => f a -> Some f

args :: Prog -> [Some Var]
args (Arg x _ prog) = Some x:args prog
args (Body _) = []

body :: Prog -> Stmt
body (Arg _ _ prog) = body prog
body (Body stmt) = stmt

data Array a =
  Array {
    arrayLength :: Index,
    arrayContents :: Map Index a }
  deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (Array a)

instance Pretty a => Pretty (Array a) where
  pPrintPrec l p = pPrintPrec l p . Map.elems . arrayContents

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
    [Array (arrayLength arr) (Map.fromList xs) | xs <- shrinkVector shrinkSecond (Map.toList (arrayContents arr))]
    where
      shrinkSecond (x, y) = [(x, y') | y' <- shrink y]

shrinkVector :: (a -> [a]) -> [a] -> [[a]]
shrinkVector _ [] = []
shrinkVector shr (x:xs) =
  [ y:xs | y <- shr x ] ++
  [ x:ys | ys <- shrinkVector shr xs ]

newtype Index = Index Integer deriving (Eq, Ord, Show, Enum, Integral, Real, Pretty, Generic, NFData)

instance Num Index where
  fromInteger = Index
  Index x + Index y = Index (x+y)
  Index x * Index y = Index (x*y)
  Index x - Index y = Index (max 0 (x-y))
  abs (Index x) = Index (abs x)
  signum (Index x) = Index (signum x)

instance Arbitrary Index where
  arbitrary = Index <$> fromIntegral <$> (arbitrary :: Gen Natural)
  shrink = genericShrink

data Var a = Var { varName :: String } deriving (Eq, Ord, Show)

newtype Env = Env { unEnv :: Map String (Some Identity) }
  deriving (NFData, Pretty)
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

class (Arbitrary a, Typeable a, Show a, Pretty a, NFData a) => Type a where
  typeName :: a -> String

shrinkSome :: Arbitrary1 f => Some f -> [Some f]
shrinkSome (Some x) = map Some (shrink1 x)

instance Pretty1 f => Pretty (Some f) where
  pPrintPrec l p (Some x) = pPrintPrec1 l p x

instance NFData1 f => NFData (Some f) where
  rnf (Some x) = rnf1 x

instance Show1 f => Show (Some f) where
  showsPrec p (Some x) = showsPrec1 p x

class Pretty1 f where
  pPrintPrec1 :: Pretty a => PrettyLevel -> Rational -> f a -> Doc

instance Pretty1 Identity where
  pPrintPrec1 l p (Identity x) = pPrintPrec l p x

instance Type Index where
  typeName _ = "index"

instance Type Bool where
  typeName _ = "boolean"

instance Type Integer where
  typeName _ = "integer"

instance Type (Set Integer) where
  typeName _ = "set of integer"

instance Type (Set Index) where
  typeName _ = "set of index"

instance a ~ Integer => Type (Array a) where
  typeName _ = "array of integer"

exec :: Env -> Expr Bool -> Stmt -> ([(Env, Expr Bool)], Env, Expr Bool)
exec env _ (x := e) =
  ([], insertEnv x (eval env e) env, true)
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
  let (points, env', pred') =
        if eval env e2 then
          if eval env e1
          then exec env (e2 &&& refine env e1) (p `Then` While e1 e2 p)
          else exec env (e2 &&& refine env e1) Skip
        else error "invariant false"
  in (points, env', pred')
exec env pred (Assert e) =
  if eval env e
  then exec env (pred &&& e) Skip
  else error "assertion failed"
exec env pred Point =
  --([], env, pred)
  ([(env, pred)], env, pred)

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
      -- Map.findWithDefault (fromIntegral (arrayLength arr+1) * fromIntegral (Map.size (arrayContents arr)+1) * fromIntegral i * 37 * (if even i then 1 else -1) + 2) i (arrayContents arr)
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

refine :: Env -> Expr Bool -> Expr Bool
refine env e =
  foldr (&&&) true [ e' | e' <- cands, eval env e' ]
  where
    cands =
      nubBy ((==) `on` show)
        (subforms e ++ map nott (subforms e))

subforms :: Expr Bool -> [Expr Bool]
subforms e = e:properSubforms e
  where
    properSubforms :: Expr Bool -> [Expr Bool]
    properSubforms (Not e) = subforms e
    properSubforms (And e1 e2) = subforms e1 ++ subforms e2
    properSubforms (Or e1 e2) = subforms e1 ++ subforms e2
    properSubforms _ = []

evalRel :: (Ord a, Num a) => Relation -> a -> a -> Bool
evalRel Eq = (==)
evalRel Ne = (/=)
evalRel Lt = (<)
evalRel Le = (<=)
evalRel Gt = (>)
evalRel Ge = (>=)

genEnv :: [Some Var] -> Gen Env
genEnv [] = return (Env Map.empty)
genEnv (Some x:xs) = do
  v <- arbitrary
  env <- genEnv xs
  return (insertEnv x v env)

genPre :: Prog -> Gen Env
genPre = go (Env Map.empty)
  where
    go (Env env) (Arg (Var x :: Var a) cond prog) = do
      env <-
        (do
           val <- arbitrary :: Gen a
           return (Env (Map.insert x (Some (Identity val)) env))) `suchThat`
        (\env -> eval env cond)
      go env prog
    go env (Body _) = return env

genPointFrom :: Prog -> Gen Env -> Gen Env
genPointFrom prog gen = do
  envs <- do { env <- gen; let (points, _, _) = exec env true (body prog) in return (map fst points) } `suchThat` (not . null)
  elements envs

genPoint :: Prog -> Gen Env
genPoint prog = genPointFrom prog (genPre prog)

postOf :: Prog -> Env -> Env
postOf prog env =
  let (_, env', _) = exec env true (body prog)
  in env'

genPostFrom :: Prog -> Gen Env -> Gen Env
genPostFrom prog gen = do
  env <- gen
  let (_, env', _) = exec env true (body prog)
  return env'

genPost :: Prog -> Gen Env
genPost prog = genPostFrom prog (genPre prog)

shrinkEnv :: Prog -> Env -> [Env]
shrinkEnv prog (Env env) =
  filter (checkEnv prog) (map (Env . Map.fromList) (shr (Map.toList env)))
  where
    shr [] = []
    shr ((x,v):xs) =
      [(x,v'):xs | v' <- shrinkSome v] ++
      map ((x,v):) (shr xs)

checkEnv :: Prog -> Env -> Bool
checkEnv (Arg _ cond prog) env =
  eval env cond && checkEnv prog env
checkEnv (Body _) _ = True

(|||), (&&&), (==>) :: Expr Bool -> Expr Bool -> Expr Bool
x ||| Value False = x
Value False ||| x = x
_ ||| Value True = Value True
Value True ||| _ = Value True
x ||| y = Or x y
x &&& Value True = x
Value True &&& x = x
_ &&& Value False = Value False
Value False &&& _ = Value False
x &&& y = And x y
Value True ==> x = x
Value False ==> x = Value True
x ==> y = nott x ||| y

nott :: Expr Bool -> Expr Bool
nott (Value True) = Value False
nott (Value False) = Value True
nott (Not x) = x
nott x = Not x

true, false :: Expr Bool
true = Value True
false = Value False

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

-- post :: Stmt -> Expr Bool
-- post stmt = fst (post' stmt)
--   where
--     -- Boolean: was the statement side effect-free?
--     post' (_ := _) = (true, False)
--     post' Skip = (true, True)
--     post' (p `Then` q) =
--       case post' q of
--         (e, False) -> (e, False)
--         (e, True) ->
--           let (e', b) = post' p in
--           (e &&& e', b)
--     post' (If cond p q) =
--       case (post' p, post' q) of
--         ((e1, True), (e2, True)) ->
--           ((cond ==> e1) &&& (nott cond ==> e2), True)
--         _ -> (true, False)
--     post' (While e1 e2 _) = (nott e1 &&& e2, False)
--     post' (Assert e) = (e, True)
--     post' Point = (true, True)

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
      ppCond (Value True) = pPrintEmpty
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
  pPrint (While e1 (Value True) p) =
    text "while" <+> pPrint e1 <+> text "do" $$
    nest 2 (pPrint p) $$
    text "end"
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
      exp p (Ordered r e) =
        text ("ord" ++ rel r) <#> parens (exp 0 e)
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
      exp p (Union e1 e2) =
        text "union" <#> parens (hsep (punctuate comma [exp 0 e1, exp 0 e2]))
      exp p (Interval e1 e2) =
        text "[" <#>
        cat [exp 0 e1 <#> text "..", exp 0 e2 <#> text ")"]
      exp p (Singleton e) =
        text "singleton" <#> parens (exp 0 e)
      exp p (Null e) =
        oper 2 1 "=" e (Value Set.empty :: Expr (Set Integer))
  
      rel :: Relation -> String
      rel Eq = "="
      rel Ne = "<>"
      rel Lt = "<"
      rel Le = "<="
      rel Gt = ">"
      rel Ge = ">="

      inf :: Rational
      inf = 100

instance Pretty (Var a) where
  pPrint (Var x) = text x

bsearch :: Prog
bsearch =
  Arg arr (Ordered Le (Local arr)) $
  Arg x (Value True) $
  Body $
  lo := Value 0 `Then`
  hi := Length (Local arr) `Then`
  found := Value False `Then`
  While (And (Not (Local found)) (Rel Lt (Local lo) (Local hi))) (Value True)
    (mid := Div (Plus (Local lo) (Local hi)) (Value 2) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value True `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         --(hi := Minus (Local mid) (Value 1))
         (lo := Plus (Local mid) (Value 1))))
  -- If (Local found)
  --   (Assert (Rel Eq (At (Local arr) (Local idx)) (Local x)))
  --   (Assert (Pairwise Ne (Singleton (Local x)) (Image (Local arr))))

bsearchPoint :: Prog
bsearchPoint =
  Arg arr (Ordered Le (Local arr)) $
  Arg x (Value True) $
  Body $
  lo := Value 0 `Then`
  hi := Length (Local arr) `Then`
  found := Value False `Then`
  While (And (Not (Local found)) (Rel Lt (Local lo) (Local hi))) (Value True)
    (Point `Then`
     mid := Div (Plus (Local lo) (Local hi)) (Value 2) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value True `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         --(hi := Minus (Local mid) (Value 1))
         (lo := Plus (Local mid) (Value 1)))) `Then`
  Point
  -- If (Local found)
  --   (Assert (Rel Eq (At (Local arr) (Local idx)) (Local x)))
  --   (Assert (Pairwise Ne (Singleton (Local x)) (Image (Local arr))))

bsearchBug :: Prog
bsearchBug =
  Arg arr (Ordered Le (Local arr)) $
  Arg x (Value True) $
  Body $
  lo := Value 0 `Then`
  hi := Length (Local arr) `Then`
  found := Value False `Then`
  While (And (Not (Local found)) (Rel Lt (Local lo) (Local hi))) (Value True)
    (-- Point `Then`
     mid := Div (Plus (Local lo) (Local hi)) (Value 2) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value True `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         -- (hi := Local mid)
         (hi := Minus (Local mid) (Value 1))
         (lo := Plus (Local mid) (Value 1))))
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

arr0 :: Var (Array Integer)
arr0 = Var "arr0"

found :: Var Bool
found = Var "found"

dutchFlag :: Prog
dutchFlag =
  Arg arr (Value True) $
  Arg md (Value True) $
  Body $
  i := Value 0 `Then`
  j := Value 0 `Then`
  n := Length (Local arr) `Then`
  While (Rel Lt (Local j) (Local n)) (Value True) (
    Point `Then`
    If (Rel Lt (At (Local arr) (Local j)) (Local md)) (
      swap arr (Local i) (Local j) `Then`
      i := Local i `Plus` Value 1 `Then`
      j := Local j `Plus` Value 1
    ){-else-}(
      If (Rel Gt (At (Local arr) (Local j)) (Local md)) (
        swap arr (Local j) (Minus (Local n) (Value 1)) `Then`
        n := Local n `Minus` Value 1
      ){-else-}(
        j := Local j `Plus` Value 1
      )
    )
  )
tests :: [Env]
tests = map env [
  (0, []),
  (0, [0]),
  (123, [456]),
  (123, [123]),
  (-2, [-123,-6,-2,59,102]),
  (153, [-123,-6,-2,59]),
  (59, [-123,-6,-2,102]),
  (102, [-123,-6,-2,102])]
  where
    env :: (Integer, [Integer]) -> Env
    env (xv, arrv) =
      insertEnv x xv (insertEnv arr (makeArray arrv) (Env Map.empty))

buggyTest :: Env
buggyTest = env (0, [0,1])
  where
    env :: (Integer, [Integer]) -> Env
    env (xv, arrv) =
      insertEnv x xv (insertEnv arr (makeArray arrv) (Env Map.empty))

data Options =
  Options {
    options :: [Option],
    categories :: [Category],
    progvars :: [Some Var],
    environment :: Environment }

data Option = Silent | QuickCheck deriving Eq
data Category = Vars | Arith | Arrays deriving Eq
data Environment = Background | Precondition | Postcondition | AtPoint | From [Env] | PostFrom [Env] | PointFrom [Env]

genFor :: Prog -> Environment -> Gen Env
genFor prog Background = return (Env Map.empty)
genFor prog Precondition = genPre prog
genFor prog Postcondition = genPost prog
genFor prog AtPoint = genPoint prog
genFor prog (From envs) = elements envs
genFor prog (PostFrom envs) = genPostFrom prog (elements envs)
genFor prog (PointFrom envs) = genPointFrom prog (elements envs)

op0 :: Expr a -> a
op0 op = eval undefined op

op1 :: Type a => (Expr a -> Expr b) -> a -> b
op1 op x = eval undefined (op (Value x))
  
op2 :: (Type a, Type b) => (Expr a -> Expr b -> Expr c) -> a -> b -> c
op2 op x y = eval undefined (op (Value x) (Value y))

op3 :: (Type a, Type b, Type c) => (Expr a -> Expr b -> Expr c -> Expr d) -> a -> b -> c -> d
op3 op x y z = eval undefined (op (Value x) (Value y) (Value z))

local :: forall a. Type a => Var a -> Sig
local x@(Var name) =
  -- customConstant (twiddle (QSH.con ("{" ++ name ++ "}") (Set.singleton . lookupEnv x :: Env -> Set a))) `mappend`
  case cast x of
    Nothing ->
      customConstant (twiddle (QSH.con name (lookupEnv x :: Env -> a)))
    Just x ->
      --let (insts1, con1) = QSH.predicate name (lookupEnv x :: Env -> Bool)
          --(insts2, con2) = QSH.predicate ("not " ++ name) (not . lookupEnv x :: Env -> Bool)
      --in mconcat [customConstant (twiddle con1), customConstant (twiddle con2), addInstances insts1, addInstances insts2]
      customConstant (twiddle (Haskell.con name (lookupEnv x :: Env -> Bool)))
  where
    twiddle con =
      con { QSH.con_style = implicitArguments 1 uncurried,
            QSH.con_size = 0 }

local' :: forall a. Type a => Var a -> Sig
local' x@(Var name) =
  -- customConstant (twiddle (QSH.con ("{" ++ name ++ "}") (Set.singleton . lookupEnv x :: Env -> Set a))) `mappend`
  case cast x of
    Nothing ->
      customConstant (twiddle (QSH.con name (lookupEnv x :: Env -> a)))
    Just x ->
      --let (insts1, con1) = QSH.predicate name (lookupEnv x :: Env -> Bool)
          --(insts2, con2) = QSH.predicate ("not " ++ name) (not . lookupEnv x :: Env -> Bool)
      --in mconcat [customConstant (twiddle con1), customConstant (twiddle con2), addInstances insts1, addInstances insts2]
      customConstant (twiddle (Haskell.con name (lookupEnv x :: Env -> Bool)))
  where
    twiddle con =
      con { QSH.con_style = uncurried, QSH.con_size = 0 }

styled :: Typeable a => String -> a -> TermStyle -> Int -> Sig
styled name val style size =
  customConstant (QSH.con name val){QSH.con_style = style, QSH.con_size = size}

styledPred :: (Typeable a, QSH.Predicateable a, Typeable (QSH.PredicateTestCase a)) => String -> a -> TermStyle -> Int -> Sig
styledPred name val style size =
  let (insts, con) = QSH.predicate name val in
  customConstant con{QSH.con_style = style, QSH.con_size = size} `mappend` addInstances insts

base = [
  instFun (QSH.SingleUse :: QSH.SingleUse Env),
  instFun (QSH.Names ["s"] :: QSH.Names Env),
  con "true" True,
  con "false" False,
  con "not" not,
  con "0" (0 :: Index),
  styled "{}" (makeArray [] :: Array A) curried 1,
  styled "{}" (Set.empty :: Set A) curried 1,
  monoTypeWithVars ["R"] (Proxy :: Proxy Relation),
  monoType (Proxy :: Proxy Index),
  instanceOf @(Num Index),
  instanceOf @(Num Integer),
  instanceOf @(Integral Integer),
  instanceOf @(Integral Index),
  instanceOf @(Type Bool),
  instanceOf @(Type Index),
  instanceOf @(Type Integer),
  instanceOf @(Type (Set Index)),
  instanceOf @(Type (Set Integer)),
  instanceOf @(Type (Array Integer)),
  defaultTo (Proxy :: Proxy Integer),
  inst (Sub Dict :: (Ord A, Arbitrary A) :- Arbitrary (Array A)),
  inst (Sub Dict :: (Ord A, Arbitrary A) :- Arbitrary (Set A)),
  inst (Sub Dict :: Ord A :- Ord (Array A)),
  inst (Sub Dict :: Ord A :- Ord (Set A)),
  instFun (QSH.NoWarnings :: QSH.NoWarnings Env)]

scalar = [
  {-not, and, or-}
  con "+" ((+) :: Index -> Index -> Index), --Num A ==> (A -> A -> A)),
  -- con "-" (liftC (-) :: Num A ==> (A -> A -> A)),
  --con "*" (liftC (*) :: Num A ==> (A -> A -> A)),
  --styled "div" (liftC div :: Integral A ==> (A -> A -> A)) (infixStyle 5),
  -- con "not" not,
  styled "rel" (evalRel :: (Relation -> Integer -> Integer -> Bool)) (relStyle "") 0,
  styled "rel" (evalRel :: (Relation -> Index -> Index -> Bool)) (relStyle "") 0,
  styled "<=" Le uncurried 1,
  styled "<" Lt uncurried 1,
  styled "/=" Ne uncurried 1]

relStyle tag =
  fixedArity 3 $
  TermStyle $ \l p _ [rel, x, y] ->
  parIf (p > 1) $
  pPrintPrec l 10 x <+> pPrintPrec l 10 rel <#> text tag <+> pPrintPrec l 10 y
  where
    parIf True x = parens x
    parIf False x = x

ordStyle =
  fixedArity 2 $
  TermStyle $ \l p _ [rel, x] ->
  text "ord" <#> brackets (pPrintPrec l 0 rel) <#> parens (pPrintPrec l 0 x)

atStyle =
  fixedArity 2 $
  TermStyle $ \l p _ [x, y] ->
  pPrintPrec l 10 x <#> brackets (pPrintPrec l 0 y)

updateStyle =
  fixedArity 3 $
  TermStyle $ \l p _ [x, y, z] ->
  -- text "update" <#> parens (hsep (punctuate comma [pPrintPrec l 100 x, pPrintPrec l 0 y <+> text ":=" <+> pPrintPrec l 0 z]))
  pPrintPrec l 10 x <#> brackets (pPrintPrec l 0 y <+> text ":=" <+> pPrintPrec l 0 z)

intervalStyle =
  fixedArity 2 $
  TermStyle $ \l p _ [x, y] ->
  text "[" <#> cat [pPrintPrec l 0 x <#> text "..", pPrintPrec l 0 y <#> text ")"]

singletonStyle =
  fixedArity 1 $
  TermStyle $ \l p _ [x] ->
  braces (pPrintPrec l 0 x)

arrays = [
  styled "ord" (\rel -> op1 (Ordered rel) :: Array Integer -> Bool) ordStyle 1,
  styled "at" (op2 At) atStyle 1,
  styled "interval" (op2 Interval) intervalStyle 1,
  styled "|" (op2 Restrict) (infixStyle 5) 1,
  styled "image" (op1 Image) uncurried 1]
  --styled "restrict" (op3 (\arr x y -> Restrict arr (Interval x y))) uncurried 1]

-- Reynolds
demo1 = quickSpec sig1
sig1 = [
  background [base, scalar],
  signature arrays,
  background (con "-" (liftC (-) :: Num A ==> (A -> A -> A))),
  styled "∪" (liftC (op2 Union) :: (Type A, Type (Set A), Ord A) ==> (Set A -> Set A -> Set A)) (infixStyle 5) 1,
  styledPred "pairwise" (\rel -> op2 (Pairwise rel) :: (Set Index -> Set Index -> Bool)) (relStyle "*") 1,
  styledPred "pairwise" (\rel -> op2 (Pairwise rel) :: (Set Integer -> Set Integer -> Bool)) (relStyle "*") 1,
  styled "singleton" (liftC (op1 Singleton) :: (Type A, Ord A) ==> (A -> Set A)) singletonStyle 1]
  --styled "update" (op3 Update) updateStyle 1,
  -- styled "length" (op1 Length) uncurried 1,
  --styledPred "inBounds" ((\n arr -> n >= 0 && n < arrayLength arr) :: Index -> Array Integer -> Bool) uncurried 1,
  --styled "concat" (op2 Concat) uncurried 1]
reynoldsSig = [
  styled "∪" (liftC (op2 Union) :: (Type A, Type (Set A), Ord A) ==> (Set A -> Set A -> Set A)) (infixStyle 5) 1,
  styled "pairwise" (\rel -> op2 (Pairwise rel) :: (Set Index -> Set Index -> Bool)) (relStyle "*") 1,
  styled "pairwise" (\rel -> op2 (Pairwise rel) :: (Set Integer -> Set Integer -> Bool)) (relStyle "*") 1,
  styled "singleton" (op1 Singleton :: (Index -> Set Index)) singletonStyle 1,
  styled "singleton" (op1 Singleton :: (Integer -> Set Integer)) singletonStyle 1]
  -- styled "update" (op3 Update) updateStyle 1,
  --styled "length" (op1 Length) uncurried 1,
  --styledPred "inBounds" ((\n arr -> n >= 0 && n < arrayLength arr) :: Index -> Array Integer -> Bool) uncurried 1 ]
  --styled "concat" (op2 Concat) uncurried 1]

onlyGround = withPrintFilter (\prop -> and [ typ x == typeOf (undefined :: Env) | x <- Term.vars prop ])

-- Postcondition
demo2 = quickSpec [background [base, scalar, arrays], local x, local arr, local found, local idx, withEnv (genPost bsearch), background memberSig, withMaxTermSize 7, onlyGround]
demo2b = quickSpec [background [base, scalar, arrays], local x, local arr, local found, local idx, withEnv (genPost bsearch `suchThat` lookupEnv found), background memberSig, withMaxTermSize 7, onlyGround]
demo2c = quickSpec [background [base, scalar, arrays], local x, local arr, local found, local idx, withEnv (genPost bsearch `suchThat` (not . lookupEnv found)), background memberSig, withMaxTermSize 7, onlyGround]

-- Invariant
demo3part1 = quickSpec [background [base, scalar, arrays], local x, local arr, local lo, local hi, local mid, local found, local idx, withEnv part1, background memberSig, withMaxTermSize 7, onlyGround]
demo3part2 = do
  res <- quickSpecResult [signature [base, scalar, arrays], local x, local arr, local lo, local hi, local mid, local found, local idx, withEnv part2, memberSig, withMaxTermSize 7]
  quickSpec [background [base, scalar, arrays], local x, local arr, local lo, local hi, local mid, local found, local idx, withEnv (genPoint bsearch), background memberSig, withMaxTermSize 7, addBackground res, onlyGround]
demo3part3 = do
  res <- quickSpecResult [signature [base, scalar, arrays], local x, local arr, local lo, local hi, local mid, local found, local idx, withEnv part3, memberSig, withMaxTermSize 7]
  quickSpec [background [base, scalar, arrays], local x, local arr, local lo, local hi, local mid, local found, local idx, withEnv (genPoint bsearch), background memberSig, withMaxTermSize 7, addBackground res, onlyGround]
demo3part4 = do
  res <- quickSpecResult [signature [base, scalar, arrays], local x, local arr, local lo, local hi, local mid, local found, local idx, withEnv part4, memberSig, withMaxTermSize 7]
  quickSpec [background [base, scalar, arrays], local x, local arr, local lo, local hi, local mid, local found, local idx, withEnv (genPoint bsearch), background memberSig, withMaxTermSize 7, addBackground res, onlyGround]

-- Psychic
bsearch1 = do
  quickSpecResult [background [base, scalar, arrays, reynoldsSig, [memberSig]], local' x, local' arr, local' found, local' idx, withEnv (genPost bsearch), withMaxTermSize 7, withMaxTests 1000, onlyGround]
bsearch2 = do
  quickSpecResult [background [base, scalar, arrays, reynoldsSig, [memberSig]], local x, local arr, local found, local idx, withEnv (genPost bsearch), withMaxTermSize 7, withMaxTests 1000, onlyGround]
bsearch3 = do
  quickSpecResult [background [base, scalar, arrays, reynoldsSig, [memberSig]], local x, local arr, local found, local idx, local lo, local hi, withEnv (genPoint bsearchPoint), withMaxTermSize 7, withMaxTests 1000, onlyGround]
bsearch4 = do
--  res <- quickSpecResult [background [base, scalar, arrays, reynoldsSig], local x, local arr, local found, local idx, withEnv (genPost bsearchBug), withMaxTermSize 7, withMaxTests 10000]
  psychic (map (postOf bsearchBug) tests) shr [background [base, scalar, arrays, reynoldsSig], local x, local arr, local found, local idx, withMaxTermSize 7, onlyGround, withMaxTests 1000, withEnv (genPost bsearchBug)]
  where
    shr tc =
      filter ok (map (postOf bsearchBug) (shrinkEnv bsearchBug (Env (Map.filterWithKey p (unEnv tc)))))
    p x _ = x `elem` [ varName x | Some x <- args bsearchBug ]
    ok tc = eval tc (preProg bsearchBug)
bsearch5 val = do
--  res <- quickSpecResult [background [base, scalar, arrays, reynoldsSig], local x, local arr, local found, local idx, withEnv (genPost bsearchBug), withMaxTermSize 7, withMaxTests 10000]
  psychic (filter (found `is` val) (map (postOf bsearchBug) tests)) shr [background [base, scalar, arrays, reynoldsSig], local x, local arr, local found, local idx, withMaxTermSize 7, onlyGround, withMaxTests 1000, withEnv (genPost bsearchBug `suchThat` (found `is` val))]
  where
    shr tc =
      filter ok (map (postOf bsearchBug) (shrinkEnv bsearchBug (Env (Map.filterWithKey p (unEnv tc)))))
    p x _ = x `elem` [ varName x | Some x <- args bsearchBug ]
    ok tc = eval tc (preProg bsearchBug) && is found val tc
    is x v env =
      lookupEnv x env == v
 
part1 = genPoint bsearch
part2 =
  genEnv [Some x, Some arr, Some lo, Some hi, Some mid, Some found, Some idx] `suchThat`
  (\env ->
   (lookupEnv found env || lookupEnv lo env >= lookupEnv hi env) &&
   not (post env))
part3 =
  genEnv [Some x, Some arr, Some lo, Some hi, Some mid, Some found, Some idx] `suchThat`
  (\env ->
   (lookupEnv lo env <= lookupEnv hi env) &&
   (lookupEnv found env || lookupEnv lo env >= lookupEnv hi env) &&
   not (post env))
part4 =
  genEnv [Some x, Some arr, Some lo, Some hi, Some mid, Some found, Some idx] `suchThat`
  (\env ->
   eval undefined (Ordered Le (Value (lookupEnv arr env))) &&
   (lookupEnv lo env <= lookupEnv hi env) &&
   (lookupEnv found env || lookupEnv lo env >= lookupEnv hi env) &&
   not (post env))

post env =
  lookupEnv found env == (lookupEnv x env `elem` Map.elems (arrayContents (lookupEnv arr env))) &&
  if lookupEnv found env then Map.lookup (lookupEnv idx env) (arrayContents (lookupEnv arr env)) == Just (lookupEnv x env) else True

arrays2 = [
  styled "concat" (op2 Concat) uncurried 1]

memberSig = styled "member" ((\x arr -> x `elem` Map.elems (arrayContents arr)) :: Integer -> Array Integer -> Bool) uncurried 1

withEnv :: Gen Env -> Sig
withEnv gen = instFun gen'
  where
    envs = unGen (vectorOf 1000 gen) (mkQCGen 1234) 30
    envsMap = Map.fromList (zip [1..] envs)
    gen' = do
      n <- choose (1, 1000 :: Int)
      return (Map.findWithDefault undefined n envsMap)

prop_found :: Property
prop_found =
  forAllShrink (genPre bsearchBug) (shrinkEnv bsearchBug) $ \env0 ->
  let (_, env, _) = exec env0 true (body bsearchBug) in
  counterexample (show env) $
  lookupEnv found env === (lookupEnv x env `elem` Map.elems (arrayContents (lookupEnv arr env)))

-- -- Just reimplement on top of normal QuickSpec? Program state variable
-- qs :: Options -> Prog -> StateT Int (Twee.Pruner (WithConstructor Sym) Terminal) ()
-- qs opts@Options{..} prog =
--   (\g -> unGen g (mkQCGen 4321) 0) $
--   QuickCheck.run (QuickCheck.Config 1000 20 Nothing) (liftM2 (,) (genFor prog environment) genVars) eval' $ do
--     tests <- gets env_tests
--     runConditionals [] $
--     quickSpec present (flip eval') n univ (enumerator opts prog bound)
--   where
--     eval' (env, var) t
--       | typeArity (typ t) > 0 = Right t
--       | isTypeVar (typ t) = Right t
--       | otherwise = Left (evalTerm (env, var) t)
--     ground _ = True -- XXX
--     present prop =
--       {-when (ok prop && not (null (intersect [StmtVar found, StmtVar idx] (funs prop)))) $ -} do
--         norm <- normaliser
--         unless (Silent `elem` options || (Vars `notElem` categories && not (ground prop))) $ do
--           n <- lift $ lift get
--           lift $ lift $ put $! n+1
--           putLine (printf "%3d. " n ++ (prettyShow . fmap fromQS $ canonicalise $ ac norm $ conditionalise prop))
--         when (QuickCheck `elem` options) (give prog (liftIO (quickCheck (withMaxSuccess 100 prop))))
--     -- ok (_ :=>: t :=: u) | typ t == boolTy, size u > 1 = False
--     -- ok _ = True

--     -- Transform x+(y+z) = y+(x+z) into associativity, if + is commutative
--     ac norm (lhs :=>: App f [QS.Var x, App f1 [QS.Var y, QS.Var z]] :=: App f2 [QS.Var y1, App f3 [QS.Var x1, QS.Var z1]])
--       | f == f1, f1 == f2, f2 == f3,
--         x == x1, y == y1, z == z1,
--         x /= y, y /= z, x /= z,
--         norm (App f [QS.Var x, QS.Var y]) == norm (App f [QS.Var y, QS.Var x]) =
--           lhs :=>: App f [App f [QS.Var x, QS.Var y], QS.Var z] :=: App f [QS.Var x, App f [QS.Var y, QS.Var z]]
--     ac _ prop = prop

--     tys = [QS.typeOf (undefined :: Integer), QS.typeOf (undefined :: Index), QS.typeOf (undefined :: Bool), QS.typeOf (undefined :: Set Index), QS.typeOf (undefined :: Set Integer), QS.typeOf (undefined :: Array Integer)]
--     univ = conditionalsUniverse tys ([] :: [Sym])

-- main = do
--   -- give bsearch (quickCheck (\env -> testProgOn bsearch env))
--   -- quickCheck (forAll (elements tests) $ \env -> testProgOn bsearch env)
--   withStdioTerminal $ Twee.run (Twee.Config n maxBound) $ flip evalStateT 0 $ do
--     -- qs (Options [Silent] [Vars, Arith] Background) (Body Skip)
--     putLine "== background =="
--     qs (Options [Silent] [Vars, Arith] Background) (Body Skip)
--     qs (Options [] [Vars, Arith, Arrays] Background) (Body Skip)
--     putLine ""
--     -- putLine "== precondition =="
--     -- qs (Options [] [Arith, Arrays, Vars] Precondition) bsearch

--     -- putLine "== postcondition =="
--     -- qs (Options [] [Arith, Arrays, Vars] Postcondition) bsearch

--     -- putLine "== point =="
--     -- qs (Options [] [Arith, Arrays, Vars] AtPoint) bsearch

--     putLine "== psychic =="
--     qs (Options [Silent] [Arith, Arrays, Vars] Postcondition) bsearch
--     qs (Options [] [Arith, Arrays, Vars] (PostFrom tests)) bsearch

a, b, k, l, i, j, n, stride :: Var Index
a = Var "a"
b = Var "b"
k = Var "k"
l = Var "l"
stride = Var "K"
i = Var "i"
j = Var "j"
n = Var "n"

md :: Var Integer
md = Var "md"

swap arr x y =
  arr := Update
         (Update (Local arr) x (Local arr `At` y))
                             y (Local arr `At` x)

rotate :: Prog
rotate =
 Arg arr true $
 Arg stride (Rel Ge (Local stride) (Value 0) &&& Rel Lt (Local stride) (Length (Local arr))) $
 Body $
   a := Value 0 `Then`
   b := Length (Local arr) `Then`
   k := Minus (Length (Local arr)) (Local stride) `Then`
   l := Local stride `Then`
   While (Rel Ne (Local k) (Value 0) &&& Rel Ne (Local l) (Value 0)) true
     (Point `Then`
      If (Rel Ge (Local k) (Local l))
       (n := Minus (Local b) (Local l) `Then`
        While (Rel Ne (Local n) (Local b)) true (swap arr (Local n) (Minus (Local n) (Local l)) `Then` n := Plus (Local n) (Value 1)) `Then` k := Minus (Local k) (Local l) `Then` b := Minus (Local b) (Local l))
       (n := Local a `Then`
        While (Rel Ne (Local n) (Plus (Local a) (Local k))) true (swap arr (Local n) (Plus (Local n) (Local k)) `Then` n := Plus (Local n) (Value 1)) `Then` l := Minus (Local l) (Local k) `Then` a := Plus (Local a) (Local k)))

invariant :: Prog -> [Some Var] -> IO ()
invariant prog xs = do
  quickSpec $ [withMaxTests 1000, background [base, scalar, arrays, sig1, [memberSig]], withEnv (genPoint prog), withMaxTermSize 7] ++ [ local x | Some x <- xs ]

dutchInvariant = invariant dutchFlag [Some arr, Some md, Some i, Some j, Some n]
dutchTests :: [Env]
dutchTests = map env [
  (0, [0]),
  (-123, [-123]),
  (-2, [-123,-6,-2,59,102]),
  (153, [-123,-6,-2,59]),
  (59, [-123,-6,-2,102]),
  (102, [-123,-6,-2,102])]
  where
    env :: (Integer, [Integer]) -> Env
    env (xv, arrv) =
      insertEnv md xv (insertEnv arr (makeArray arrv) (insertEnv arr0 (makeArray arrv) (Env Map.empty)))

demo4d = do
  psychic (map (postOf dutchFlag) tests) shr [background [base, scalar, arrays, reynoldsSig], local md, local arr0, local arr, withMaxTermSize 7, onlyGround, withMaxTests 1000, withEnv (genPost dutchFlag)]
  where
    shr tc =
      filter ok (map (postOf dutchFlag) (shrinkEnv dutchFlag (Env (Map.filterWithKey p (unEnv tc)))))
    p x _ = x `elem` [ varName x | Some x <- args dutchFlag ]
    ok tc = eval tc (preProg dutchFlag)

main = dutchInvariant

prog = bsearchBug
