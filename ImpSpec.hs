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
  styled "{}" (Value (makeArray [] :: Array Integer)) curried 1,
  styled "{}" (Value (Set.empty :: Set Integer)) curried 1,
  styled "{}" (Value (Set.empty :: Set Index)) curried 1,
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
  styled "ord" (\rel -> Ordered rel :: Expr (Array Integer) -> Expr Bool) ordStyle 1,
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
{-
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
-}
{-
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
-}
