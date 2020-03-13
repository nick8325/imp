{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module New where
import Twee.Pretty
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import Data.Monoid
import qualified Data.Map.Strict as Map

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

data Array a =
  Array {
    arrayLength :: Index,
    arrayContents :: Map Index a }
  deriving (Eq, Ord, Show)

instance Pretty a => Pretty (Array a) where
  pPrintPrec l p = pPrintPrec l p . Map.elems . arrayContents

newtype Index = Index Integer deriving (Eq, Ord, Show, Enum, Integral, Real, Pretty)

instance Num Index where
  fromInteger = Index
  Index x + Index y = Index (x+y)
  Index x * Index y = Index (x*y)
  Index x - Index y = Index (max 0 (x-y))
  abs (Index x) = Index (abs x)
  signum (Index x) = Index (signum x)

data Var a = Var String deriving (Eq, Ord, Show)

class (Show a, Pretty a) => Type a where
  typeName :: a -> String

class Pretty1 f where
  pPrintPrec1 :: Pretty a => PrettyLevel -> Rational -> f a -> Doc

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
    (-- Point `Then`
     mid := Div (Plus (Local lo) (Local hi)) (Value 2) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value True `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         --(hi := Minus (Local mid) (Value 1))
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

found :: Var Bool
found = Var "found"

dutchFlag :: Prog
dutchFlag =
  Arg arr (Value True) $
  Arg md (Value True) $
  Body $
  i := Value 0 `Then`
  j := Value 0 `Then`
  n := Length (Local arr) `Minus` Value 1 `Then`
  While (Rel Le (Local j) (Local n)) (Value True) (
    If (Rel Lt (At (Local arr) (Local j)) (Local md)) (
      swap arr (Local i) (Local j) `Then`
      i := Local i `Plus` Value 1 `Then`
      j := Local j `Plus` Value 1
    ){-else-}(
      If (Rel Gt (At (Local arr) (Local j)) (Local md)) (
        swap arr (Local j) (Local n) `Then`
        n := Local n `Minus` Value 1
      ){-else-}(
        j := Local j `Plus` Value 1
      )
    )
  )

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
     (If (Rel Ge (Local k) (Local l))
       (n := Minus (Local b) (Local l) `Then`
        While (Rel Ne (Local n) (Local b)) true (swap arr (Local n) (Minus (Local n) (Local l)) `Then` n := Plus (Local n) (Value 1)) `Then` k := Minus (Local k) (Local l) `Then` b := Minus (Local b) (Local l))
       (n := Local a `Then`
        While (Rel Ne (Local n) (Plus (Local a) (Local k))) true (swap arr (Local n) (Plus (Local n) (Local k)) `Then` n := Plus (Local n) (Value 1)) `Then` l := Minus (Local l) (Local k) `Then` a := Plus (Local a) (Local k)))