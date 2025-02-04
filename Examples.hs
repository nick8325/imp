{-# LANGUAGE FlexibleContexts, RankNTypes #-}
module Examples where

import Prog
import ImpSpec
import Data.Reflection
import Eval
import QuickSpec
import Test.QuickCheck hiding ((==>), Ordered)
import Twee.Pretty
import Psychic
import qualified Data.Map.Strict as Map

bsearch :: Prog
bsearch =
  Arg arr (Ordered Le (Local arr)) $
  Arg x (Value True) $
  Body $
  lo := Value 0 `Then`
  hi := Length (Local arr) `Then`
  found := Value False `Then`
  While (And (Not (Local found)) (Rel Lt (Local lo) (Local hi))) (Value True)
    (Point "invariant" `Then`
     mid := Div (Plus (Local lo) (Local hi)) (Value 2) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value True `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         --(hi := Minus (Local mid) (Value 1))
         (lo := Plus (Local mid) (Value 1)))) `Then`
  Point "post"
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
         (lo := Plus (Local mid) (Value 1)))) `Then`
  Point "post"
  -- If (Local found)
  --   (Assert (Rel Eq (At (Local arr) (Local idx)) (Local x)))
  --   (Assert (Pairwise Ne (Singleton (Local x)) (Image (Local arr))))

merge :: Prog
merge =
  Arg arr1 (Ordered Le (Local arr1)) $
  Arg arr2 (Ordered Le (Local arr2)) $
  Arg arr (Rel Eq (Length (Local arr1) `Plus` Length (Local arr2)) (Length (Local arr))) $
  Body $
  i := Value 0 `Then`
  j := Value 0 `Then`
  k := Value 0 `Then`
  While (And (Rel Lt (Local i) (Length (Local arr1))) (Rel Lt (Local j) (Length (Local arr2)))) (Value True)
    (Point "invariant" `Then`
     If (Rel Lt (At (Local arr1) (Local i)) (At (Local arr2) (Local j)))
       (arr := Update (Local arr) (Local k) (At (Local arr1) (Local i)) `Then` i := Plus (Local i) (Value 1) `Then` k := Plus (Local k) (Value 1))
       (arr := Update (Local arr) (Local k) (At (Local arr2) (Local j)) `Then` j := Plus (Local j) (Value 1) `Then` k := Plus (Local k) (Value 1))) `Then`
  While (Rel Lt (Local i) (Length (Local arr1))) (Value True)
    (arr := Update (Local arr) (Local k) (At (Local arr1) (Local i)) `Then` i := Plus (Local i) (Value 1) `Then` k := Plus (Local k) (Value 1)) `Then`
  While (Rel Lt (Local j) (Length (Local arr2))) (Value True)
    (arr := Update (Local arr) (Local k) (At (Local arr2) (Local j)) `Then` j := Plus (Local j) (Value 1) `Then` k := Plus (Local k) (Value 1)) `Then`
  Point "post"
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

arr, arr1, arr2 :: Var (Array Integer)
arr = Var "arr"
arr1 = Var "arr1"
arr2 = Var "arr2"

arr0 :: Var (Array Integer)
arr0 = Var "arr0"

found :: Var Bool
found = Var "found"

dutchFlag :: Prog
dutchFlag =
  Arg arr0 (Value True) $
  Arg md (Value True) $
  Body $
  arr := Local arr0 `Then`
  i := Value 0 `Then`
  j := Value 0 `Then`
  n := Length (Local arr) `Then`
  -- Invariant: a[0..i)<md, arr[i..j)==md, arr[n..N]>md
  While (Rel Lt (Local j) (Local n)) (Value True) (
    Point "invariant" `Then`
    If (Rel Lt (At (Local arr) (Local j)) (Local md)) (
      swap arr (Local i) (Local j) `Then`
      i := Local i `Plus` Value 1 `Then`
      j := Local j `Plus` Value 1
    ){-else-}(
      If (Rel Gt (At (Local arr) (Local j)) (Local md)) (
        n := Local n `Minus` Value 1 `Then`
        swap arr (Local j) (Local n)
      ){-else-}(
        j := Local j `Plus` Value 1
      )
    )
  ) `Then`
  Point "post"

partitioning :: Prog
partitioning =
  Arg arr0 (Value True) $
  Body $
  arr := Local arr0 `Then`
  i := Value 1 `Then`
  j := Value 1 `Then`
  n := Length (Local arr) `Then`
  md := At (Local arr) (Value 0) `Then`
  let pivot = Local md in
  -- Invariant: a[0..i)<md, arr[i..j)==md, arr[n..N]>md
  While (Rel Lt (Local j) (Local n)) (Value True) (
    Point "invariant" `Then`
    If (Rel Lt (At (Local arr) (Local j)) pivot) (
      swap arr (Local i) (Local j) `Then`
      i := Local i `Plus` Value 1 `Then`
      j := Local j `Plus` Value 1
    ){-else-}(
      If (Rel Gt (At (Local arr) (Local j)) pivot) (
        n := Local n `Minus` Value 1 `Then`
        swap arr (Local j) (Local n)
      ){-else-}(
        j := Local j `Plus` Value 1
      )
    )
  ) `Then`
  swap arr (Minus (Local i) (Value 1)) (Value 0) `Then`
  -- Post: a[0..i-1)<md, arr[i-1..j)==md, arr[j..N]>md
  Point "post"

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

-- Postcondition
memberSig = [styled "member" (\x arr -> Not (Pairwise Ne (Singleton x) (Image arr))) uncurried 1]

sig2 :: Given (Gen Env) => (Sig, Sig)
sig2 =
  (signature [base, scalar, {-arrays,-} memberSig],
   series [
     [con "x" (Local x),
      con "arr" (Local arr), -- (\i j -> Local arr `Restrict` Interval i j),
      con "N" (Length (Local arr))],
     [con "found" (Local found),
      con "idx" (Local idx)]])
sig3 :: Given (Gen Env) => (Sig, Sig)
sig3 =
  (fst sig2,
   signature [
     snd sig2,
     series [
       [],
       [con "lo" (Local lo),
        con "hi" (Local hi)]]])
sig4 :: Given (Gen Env) => (Sig, Sig)
sig4 =
  (signature [base, scalar, arrays, sets],
   series [
     [{-con "arr0" (Local arr0),-}
      con "N" (Length (Local arr0))],
     [con "arr" (Local arr),
      con "i" (Local i),
      con "pred_i" (Minus (Local i) (Value 1)),
      con "j" (Local j),
      con "n" (Local n),
      con "md" (Local md)]])
sig5 :: Given (Gen Env) => (Sig, Sig)
sig5 =
  (mempty,
   signature [
     [con "i" (Local i),
      con "j" (Local j),
      con "k" (Local k),
      con "arr" (Local arr),
      con "arr1" (Local arr1),
      con "arr2" (Local arr2),
      con "len" Length]])
unc :: (Given (Gen Env) => (Sig, Sig)) -> (Gen Env -> Sig, Gen Env -> Sig)
unc x = (\e -> give e (fst x), \e -> give e (snd x))

demo2 = uncurry (impSpec Nothing (genPoint bsearch "post")) (unc sig2)
demo2b = uncurry (impSpec Nothing (genPoint bsearch "post" `suchThat` lookupEnv found)) (unc sig2)
demo2c = uncurry (impSpec Nothing (genPoint bsearch "post" `suchThat` (not . lookupEnv found))) (unc sig2)
demo3 = uncurry (impSpec Nothing (genPoint bsearch "invariant")) (unc sig3)
demo4 = uncurry (impSpec Nothing (genPoint dutchFlag "post")) (unc sig4)
demo5 = uncurry (impSpec Nothing (genPoint dutchFlag "invariant")) (unc sig4)
demo6 = uncurry (impSpec (Just gen) (genPoint partitioning "post")) (unc sig4)
  where gen = genAny [Some arr, Some i, Some j, Some n, Some md]
demo7 = uncurry (impSpec Nothing (genPoint partitioning "invariant")) (unc sig4)

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
      let e0 = insertEnv x xv (insertEnv arr (toArray arrv) (Env Map.empty))
          foundv = lookupEnv found (postOf bsearchBug e0)
      in insertEnv found foundv e0

demo8 = uncurry (impSpec (Just (genChaos bsearchBug)) (genPoint bsearchBug "post")) (unc sig3)
demo9 = uncurry (impSpec (Just (genChaos bsearchBug)) (genPointFrom (elements tests) bsearchBug "post")) (unc sig3)
demo10 = uncurry (impSpec (Just (genChaos bsearch)) (genPoint bsearch "post")) (unc sig3)

demo11 = uncurry (psychicImpSpec bsearchBug (genPointFrom (elements tests) bsearchBug "post") (genPoint bsearchBug "post")) (unc sig3)
demo12 = uncurry (impSpec (Just (genChaos merge)) (genPoint merge "post")) (unc sig5)
{-
bsearch4 = do
--  res <- quickSpecResult [background [base, scalar, arrays, reynoldsSig], local x, local arr, local found, local idx, withEnv (genPost bsearchBug), withMaxTermSize 7, withMaxTests 10000]
  psychic (map (postOf bsearchBug) tests) shr [background [base, scalar, arrays, reynoldsSig], local x, local arr, local found, local idx, withMaxTermSize 7, onlyGround, withMaxTests 1000, withEnv (genPost bsearchBug)]
  where
    shr tc =
      filter ok (map (postOf bsearchBug) (shrinkEnv bsearchBug (Env (Map.filterWithKey p (unEnv tc)))))
    p x _ = x `elem` [ varName x | Some x <- args bsearchBug ]
    ok tc = eval tc (preProg bsearchBug)
-}
--demo2b = quickSpec [background [base, scalar, arrays], local x, local arr, local found, local idx, withEnv (genPost bsearch `suchThat` lookupEnv found), background memberSig, withMaxTermSize 7, onlyGround]
--demo2c = quickSpec [background [base, scalar, arrays], local x, local arr, local found, local idx, withEnv (genPost bsearch `suchThat` (not . lookupEnv found)), background memberSig, withMaxTermSize 7, onlyGround]
{-
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
