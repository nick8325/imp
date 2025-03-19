{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, TypeOperators, TypeApplications, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TypeFamilies, RankNTypes #-}
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
import qualified QuickSpec.Internal.Term as Term
import QuickSpec.Internal.Type(typeOf, typ)
import Data.List
import Psychic

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

genChaos :: Prog -> Gen Env
genChaos p = genInput p >>= go (body p)
  where
    go ((x :: Var a) := _) env | not (x `memberEnv` env) = do
      val <- arbitrary :: Gen a
      return (insertEnv x val env)
    go (s1 `Then` s2) env = go s1 env >>= go s2
    go (If _ s1 s2) env = go s1 env >>= go s2
    go (While _ _ s) env = go s env
    go _ env = return env

genAny :: [Some Var] -> Gen Env
genAny [] = return (Env Map.empty)
genAny (Some (Var x :: Var a):xs) = do
  v <- arbitrary :: Gen a
  Env m <- genAny xs
  return (Env (Map.insert x (Some (Identity v)) m))

genPointsFrom :: Gen Env -> Prog -> String -> Gen [Env]
genPointsFrom genInp prog msg =
  points <$> genInp
  where
    points env =
      [pt | (msg', pt) <- fst (exec env (body prog)), msg == msg']

genPoints :: Prog -> String -> Gen [Env]
genPoints prog = genPointsFrom (genInput prog) prog

genPointFrom :: Gen Env -> Prog -> String -> Gen Env
genPointFrom genInp prog msg =
  (genPointsFrom genInp prog msg `suchThat` (not . null)) >>= elements

genPoint :: Prog -> String -> Gen Env
genPoint prog msg =
  genPointFrom (genInput prog) prog msg

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

instance Given (Gen Env) => Arbitrary Env where
  arbitrary = given

instance (Given (Gen Env), Ord a) => Observe Env a (Expr a) where
  observe = eval

instance Eq Env where (==) = error "oops"
instance Ord Env where compare = error "oops"

base :: Given (Gen Env) => [Sig]
base = [
  signature instances,
  con "true" true,
  con "false" false,
  --con "not" nott,
  con "0" (Value 0 :: Expr Index),
  --con "1" (Value 0 :: Expr Index),
  styled "{}" (Value (toArray [] :: Array Integer)) curried 1
  ]
  {-styled "{}" (Value (Set.empty :: Set Integer)) curried 1,
  styled "{}" (Value (Set.empty :: Set Index)) curried 1 ]-}

instances :: Given (Gen Env) => [Sig]
instances = [
  inst (Sub Dict :: () :- Observe Env Env (Expr Env)),
  monoTypeObserve (Proxy :: Proxy (Expr Bool)),
  monoTypeObserve (Proxy :: Proxy (Expr Index)),
  monoTypeObserve (Proxy :: Proxy (Expr Integer)),
  monoTypeObserve (Proxy :: Proxy (Expr (Array Integer))),
  monoTypeObserve (Proxy :: Proxy (Expr (Set Integer))),
  monoTypeObserve (Proxy :: Proxy (Expr (Set Index))),
  defaultTo (Proxy :: Proxy Integer)]

scalar = [
  {-not, and, or-}
  --con "+" (Plus :: Expr Index -> Expr Index -> Expr Index),
  --con "-" (Minus :: Expr Index -> Expr Index -> Expr Index),
  --con "succ" (Plus (Value 1) :: Expr Index -> Expr Index),
  --con "pred" (Plus (Value (-1)) :: Expr Index -> Expr Index),
  binPred "<=" (Rel Le :: Expr Integer -> Expr Integer -> Expr Bool) arbitrary,
--  con "<"  (Rel Lt :: Expr Integer -> Expr Integer -> Expr Bool),
--  con "/=" (Rel Ne :: Expr Integer -> Expr Integer -> Expr Bool),
  binPred "<=" (Rel Le :: Expr Index -> Expr Index -> Expr Bool) arbitrary]
--  con "<"  (Rel Lt :: Expr Index -> Expr Index -> Expr Bool),
--  con "/=" (Rel Ne :: Expr Index -> Expr Index -> Expr Bool)]

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

sliceStyle =
  fixedArity 3 $
  TermStyle $ \l p _ [arr, x, y] ->
  pPrintPrec l 10 arr <> (text "[" <#> cat [pPrintPrec l 0 x <#> text "..", pPrintPrec l 0 y <#> text ")"])

arrays = [
  --unaryPred "ord<" (Ordered Lt :: Expr (Array Integer) -> Expr Bool),
  --unaryPred "ord<=" (Ordered Le :: Expr (Array Integer) -> Expr Bool) (toArray <$> sort <$> arbitrary),
  styled "at" At atStyle 1,
  styled "interval" Interval intervalStyle 1,
  styled "|" Restrict (infixStyle 5) 1,
  styled "image" Image uncurried 1,
  styled "sorted" (Ordered Le) uncurried 1]
  --styled "restrict" (\arr x y -> Restrict arr (Interval x y)) uncurried 1]

singletonArray :: Expr Integer -> Expr (Array Integer)
singletonArray e = Update (Value (toArray [undefined])) (Value 0) e

sets :: Given (Gen Env) => [Sig]
sets =
 [{-con "∪" (Union :: Expr (Set Index) -> Expr (Set Index) -> Expr (Set Index)),
  con "∪" (Union :: Expr (Set Integer) -> Expr (Set Integer) -> Expr (Set Integer)),-}
  binPred "<=" (Pairwise Le :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool) arbitrary,
  binPred "<" (Pairwise Lt :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool) arbitrary,
  binPred "=S" (Pairwise Eq :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool) arbitrary,
  --con "<" (Pairwise Lt :: Expr (Set Index) -> Expr (Set Index) -> Expr Bool),
  --con "/=S" (Pairwise Ne :: Expr (Set Index) -> Expr (Set Index) -> Expr Bool),
  --binPred "<=" (Pairwise Le :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool) arbitrary,
  --con "<" (Pairwise Lt :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool),
  --con "/=S" (Pairwise Ne :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool),
  styled "singleton" (Singleton :: Expr Integer -> Expr (Set Integer)) singletonStyle 1]
  --con "length" Length]
  --styled "concat" Concat uncurried 1]

-- Reynolds
demo1 = give (undefined :: Gen Env) (quickSpec sig1)

genPairwise :: (Type a, Type (Set a), Ord a, Num a, Arbitrary a) => () -> Gen (Relation, (Expr (Set a), (Expr (Set a), ())))
genPairwise () = do
  rel <- arbitrary
  (s1, s2) <- arbitrary `suchThat` (\(s1, s2) -> eval undefined (Pairwise rel (Value s1) (Value s2)))
  return (rel, (Value s1, (Value s2, ())))

unaryPred :: (Type a, Arbitrary a) => String -> (Expr a -> Expr Bool) -> Gen a -> Sig
unaryPred name f gen = con name f -- predicateGen name f gen'
  where
    gen' = Value <$> gen `suchThat` (\x -> eval undefined (f (Value x)))

binPred :: (Type a, Type b, Arbitrary a, Arbitrary b) => String -> (Expr a -> Expr b -> Expr Bool) -> Gen (a, b) -> Sig
binPred name f gen = con name f -- predicateGen name f gen'
  where
    gen' = do
      (x, y) <- gen `suchThat` (\(x, y) -> eval undefined (f (Value x) (Value y)))
      return (Value x, Value y)

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
sig1 =
 [background [base, scalar],
  signature arrays,
  styled "∪" (Union :: Expr (Set Index) -> Expr (Set Index) -> Expr (Set Index)) (infixStyle 5) 1,
  styled "∪" (Union :: Expr (Set Integer) -> Expr (Set Integer) -> Expr (Set Integer)) (infixStyle 5) 1,
  con "<=" (Pairwise Le :: Expr (Set Index) -> Expr (Set Index) -> Expr Bool),
  con "<" (Pairwise Lt :: Expr (Set Index) -> Expr (Set Index) -> Expr Bool),
  con "/=S" (Pairwise Ne :: Expr (Set Index) -> Expr (Set Index) -> Expr Bool),
  con "<=" (Pairwise Le :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool),
  con "<" (Pairwise Lt :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool),
  con "/=S" (Pairwise Ne :: Expr (Set Integer) -> Expr (Set Integer) -> Expr Bool),
  styled "singleton" (Singleton :: Expr Integer -> Expr (Set Integer)) singletonStyle 1,
  styled "update" Update updateStyle 1,
  styled "length" Length uncurried 1,
  --styledPred "inBounds" ((\n arr -> n >= 0 && n < arrayLength arr) :: Index -> Array Integer -> Bool) genInBounds uncurried 1,
  styled "concat" Concat uncurried 1]

onlyGround = withPrintFilter (\prop -> and [ typ x == typeOf (undefined :: Env) | x <- Term.vars prop ])

impSpec :: (Signature sig1, Signature sig2) => Maybe (Gen Env) -> Gen Env -> (Gen Env -> sig1) -> (Gen Env -> sig2) -> IO ()
impSpec e1 e2 sig1 sig2 = do
  thy1 <- give (undefined :: Gen Env) (quickSpecResult [background (sig1 undefined), withMaxTermSize 7])
  thy2 <- 
    case e1 of
      Nothing -> return []
      Just e1 ->
        give e1 (quickSpecResult [
          withMaxTermSize 7,
          signature instances,
          variableUse (UpTo 0) (Proxy :: Proxy A),
          addBackground thy1,
          background (sig1 e1),
          background (sig2 e1) ])
  give e2 (quickSpec [
    withMaxTermSize 7,
    signature instances,
    variableUse (UpTo 0) (Proxy :: Proxy A),
    addBackground thy1,
    addBackground thy2,
    background (sig1 e2),
    signature (sig2 e2) ])

psychicImpSpec :: (Signature sig1, Signature sig2) => Prog -> Gen Env -> Gen Env -> Gen Env -> (Gen Env -> sig1) -> (Gen Env -> sig2) -> IO ()
psychicImpSpec prog chaos tests e sig1 sig2 = do
  thy <- quickSpecResult (background (sig chaos))
  psychic prog tests shr e $ \e -> signature [signature (sig e), addBackground thy]
  where
      shr tc = filter ok (map (postOf prog) (shrinkEnv prog (Env (Map.filterWithKey p (unEnv tc)))))
      p x _ = x `elem` [ varName x | Some x <- args prog ]
      ok tc = eval tc (preProg prog)
      sig e = [
        withMaxTermSize 7,
        signature (give e instances),
        variableUse (UpTo 0) (Proxy :: Proxy A),
        signature (sig1 e),
        signature (sig2 e) ]

