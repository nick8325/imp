{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Prog where
import Twee.Pretty
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import Data.Monoid
import qualified Data.Map.Strict as Map
import Data.Functor.Identity
import Data.Typeable
import Test.QuickCheck hiding ((==>), Ordered)
import Data.List
import Data.Functor.Classes

class Pretty1 f where
  pPrintPrec1 :: Pretty a => PrettyLevel -> Rational -> f a -> Doc

instance Pretty1 Identity where
  pPrintPrec1 l p (Identity x) = pPrintPrec l p x

instance Pretty1 f => Pretty (Some f) where
  pPrintPrec l p (Some x) = pPrintPrec1 l p x

instance Show1 f => Show (Some f) where
  showsPrec p (Some x) = showsPrec1 p x

data Some f where
  Some :: Type a => f a -> Some f

newtype Env = Env { unEnv :: Map String (Some Identity) }
  deriving Pretty
instance Show Env where show = prettyShow

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
  Point :: String -> Stmt
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
  Ordered :: Relation -> Expr (Array Integer) -> Expr Bool
  -- Arrays
  At :: Expr (Array Integer) -> Expr Index -> Expr Integer
  Update :: Expr (Array Integer) -> Expr Index -> Expr Integer -> Expr (Array Integer)
  Length :: Expr (Array Integer) -> Expr Index
  Image :: Expr (Array Integer) -> Expr (Set Integer)
  Concat :: Expr (Array Integer) -> Expr (Array Integer) -> Expr (Array Integer)
  Restrict :: Expr (Array Integer) -> Expr (Set Index) -> Expr (Array Integer)
  -- Sets
  Interval :: Expr Index -> Expr Index -> Expr (Set Index)
  Union :: (Type a, Ord a) => Expr (Set a) -> Expr (Set a) -> Expr (Set a)
  Singleton :: (Type a, Ord a) => Expr a -> Expr (Set a)
  Null :: Expr (Set a) -> Expr Bool
  -- Internal
  GetEnv :: Expr Env
deriving instance Show (Expr a)

data Relation = Eq | Ne | Le | Lt | Ge | Gt deriving (Eq, Ord, Show)

newtype Array a =
  Array {
    arrayContents :: Map Index a }
  deriving (Eq, Ord, Show)

toArray :: [a] -> Array a
toArray xs =
  Array {
    arrayContents = Map.fromList (zip [0..] xs) }

fromArray :: Array a -> [a]
fromArray = Map.elems . arrayContents

instance Pretty a => Pretty (Array a) where
  pPrintPrec l p = pPrintPrec l p . Map.elems . arrayContents

newtype Index = Index Integer deriving (Eq, Ord, Show, Enum, Integral, Real, Pretty)

instance Num Index where
  fromInteger = Index
  Index x + Index y = Index (x+y)
  Index x * Index y = Index (x*y)
  Index x - Index y = Index (x-y)
  abs (Index x) = Index (abs x)
  signum (Index x) = Index (signum x)

data Var a = Var {varName :: String} deriving (Eq, Ord, Show)

class (Show a, Pretty a, Typeable a, Arbitrary a) => Type a where
  typeName :: a -> String

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
  pPrint (Point msg) =
    text ("{ " ++ msg ++ " }")

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

instance Arbitrary Relation where
  arbitrary = elements [Eq, Ne, Le, Lt, Ge, Gt]

instance Arbitrary Index where
  arbitrary = Index <$> arbitrary `suchThat` (>= 0)
  shrink (Index i) = Index <$> filter (>= 0) (shrink i)

instance (Ord a, Arbitrary a) => Arbitrary (Array a) where
  arbitrary = do
    permute <- elements [id, sort]
    contents <- permute <$> arbitrary
    return (toArray contents)
  shrink arr = map toArray (shrink (Map.elems (arrayContents arr)))

instance (Type a, Arbitrary a) => Arbitrary (Expr a) where
  arbitrary = Value <$> arbitrary
