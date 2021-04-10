{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, TypeOperators, TypeApplications, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TypeFamilies #-}
module ImpSpec where

import Prog
import Eval
import QuickSpec
import QuickSpec.Internal
import qualified QuickSpec.Internal.Haskell as QSH
import Twee.Pretty
import Test.QuickCheck hiding (Ordered)
import qualified Data.Map.Strict as Map
import Data.Functor.Identity
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Reflection

genInput :: Prog -> Gen Env
genInput = go (Env Map.empty)
  where
    go (Env env) (Arg (Var x :: Var a) cond prog) = do
      env <-
        (do
           val <- arbitrary :: Gen a
           return (Env (Map.insert x (Some (Identity val)) env))) `suchThat`
        (\env -> eval env cond)
      go env prog
    go env (Body _) = return env

genPoints :: Prog -> String -> Gen [Env]
genPoints prog msg =
  points <$> genInput prog
  where
    points env =
      [pt | (msg', pt) <- fst (exec env (body prog)), msg == msg']

genPoint :: Prog -> String -> Gen Env
genPoint prog msg =
  (genPoints prog msg `suchThat` (not . null)) >>= elements

shrinkEnv :: Prog -> Env -> [Env]
shrinkEnv prog (Env env) =
  filter (checkEnv prog) (map (Env . Map.fromList) (shr (Map.toList env)))
  where
    shr [] = []
    shr ((x,v):xs) =
      [(x,v'):xs | v' <- shrinkSome v] ++
      map ((x,v):) (shr xs)

shrinkSome :: Arbitrary1 f => Some f -> [Some f]
shrinkSome (Some x) = map Some (shrink1 x)

styled :: Typeable a => String -> a -> TermStyle -> Int -> Sig
styled name val style size =
  customConstant (QSH.con name val){QSH.con_style = style, QSH.con_size = size}

instance QSH.Predicateable (Expr Bool) where
  type PredicateTestCase (Expr Bool) = ()
  type PredicateResult (Expr Bool) = Expr Bool
  uncrry = const
  true _ = QSH.con "true" true

styledPred :: (Typeable a, Typeable b, QSH.Predicateable a, Typeable (QSH.PredicateTestCase a)) => String -> a -> (b -> Gen (QSH.PredicateTestCase a)) -> TermStyle -> Int -> Sig
styledPred name val gen style size =
  let (insts, con) = QSH.predicateGen name val gen in
  customConstant con{QSH.con_style = style, QSH.con_size = size} `mappend` addInstances insts

instance Given (Gen Env) => Arbitrary Env where
  arbitrary = given

instance (Given (Gen Env), Ord a) => Observe Env a (Expr a) where
  observe = eval

base :: Given (Gen Env) => [Sig]
base = [
  con "true" true,
  con "false" false,
  con "not" nott,
  con "0" (Value 0 :: Expr Index),
  styled "{}" (Value (toArray [] :: Array Integer)) curried 1,
  styled "{}" (Value (Set.empty :: Set Integer)) curried 1,
  styled "{}" (Value (Set.empty :: Set Index)) curried 1,
  --styledPred "nonempty" (\e -> Rel Gt (Length e) (Value 0)) genNonEmpty uncurried 1,
  monoTypeWithVars ["R"] (Proxy :: Proxy Relation),
  monoTypeObserve (Proxy :: Proxy (Expr Bool)),
  monoTypeObserve (Proxy :: Proxy (Expr Index)),
  monoTypeObserve (Proxy :: Proxy (Expr Integer)),
  monoTypeObserve (Proxy :: Proxy (Expr (Array Integer))),
  monoTypeObserve (Proxy :: Proxy (Expr (Set Integer))),
  monoTypeObserve (Proxy :: Proxy (Expr (Set Index))),
  defaultTo (Proxy :: Proxy Integer)]

scalar = [
  {-not, and, or-}
  con "+" (Plus :: Expr Index -> Expr Index -> Expr Index),
  styled "rel" (Rel :: (Relation -> Expr Integer -> Expr Integer -> Expr Bool)) (relStyle "") 0,
  styled "rel" (Rel :: (Relation -> Expr Index -> Expr Index -> Expr Bool)) (relStyle "") 0,
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
  styledPred "ord" (\rel -> Ordered rel :: Expr (Array Integer) -> Expr Bool) genOrd ordStyle 1,
  styledPred "ord<" (Ordered Lt :: Expr (Array Integer) -> Expr Bool) (genOrdOf Lt) uncurried 1,
  styledPred "ord<=" (Ordered Le :: Expr (Array Integer) -> Expr Bool) (genOrdOf Le) uncurried 1,
  styled "at" At atStyle 1,
  styled "interval" Interval intervalStyle 1,
  styled "|" Restrict (infixStyle 5) 1,
  styled "image" Image uncurried 1]
  --styled "restrict" (op3 (\arr x y -> Restrict arr (Interval x y))) uncurried 1]

-- Reynolds
demo1 = give (undefined :: Gen Env) (quickSpec sig1)

genPairwise :: (Type a, Type (Set a), Ord a, Num a, Arbitrary a) => () -> Gen (Relation, (Expr (Set a), (Expr (Set a), ())))
genPairwise () = do
  rel <- arbitrary
  (s1, s2) <- arbitrary `suchThat` (\(s1, s2) -> eval undefined (Pairwise rel (Value s1) (Value s2)))
  return (rel, (Value s1, (Value s2, ())))

genOrd :: () -> Gen (Relation, (Expr (Array Integer), ()))
genOrd () = do
  rel <- arbitrary
  s <- arbitrary `suchThat` (\s -> eval undefined (Ordered rel (Value s)))
  return (rel, (Value s, ()))

genOrdOf :: Relation -> () -> Gen (Expr (Array Integer), ())
genOrdOf rel () = do
  s <- arbitrary `suchThat` (\s -> eval undefined (Ordered rel (Value s)))
  return (Value s, ())

genNonEmpty :: () -> Gen (Expr (Array Integer), ())
genNonEmpty () = do
  s <- arbitrary `suchThat` (\s -> not (null (fromArray s)))
  return (Value s, ())

sig1 :: Given (Gen Env) => [Sig]
sig1 = [
  background [base, scalar],
  signature arrays,
  styled "∪" (Union :: Expr (Set Index) -> Expr (Set Index) -> Expr (Set Index)) (infixStyle 5) 1,
  styled "∪" (Union :: Expr (Set Integer) -> Expr (Set Integer) -> Expr (Set Integer)) (infixStyle 5) 1,
  styledPred "pairwise" (\rel -> Pairwise rel :: Expr (Set Index) -> Expr (Set Index) -> Expr Bool) genPairwise (relStyle "*") 1,
  styledPred "pairwise" (\rel -> Pairwise rel :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool) genPairwise (relStyle "*") 1,
  styled "singleton" (Singleton :: Expr Integer -> Expr (Set Integer)) singletonStyle 1,
  styled "update" Update updateStyle 1,
  styled "length" Length uncurried 1,
  --styledPred "inBounds" ((\n arr -> n >= 0 && n < arrayLength arr) :: Index -> Array Integer -> Bool) genInBounds uncurried 1,
  styled "concat" Concat uncurried 1]
