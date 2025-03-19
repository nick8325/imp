{-# LANGUAGE FlexibleContexts, RankNTypes #-}
module Demo where

import Prog
import ImpSpec
import Data.Reflection
import Eval hiding (pre)
import QuickSpec
import Test.QuickCheck hiding ((==>), Ordered)
import Twee.Pretty
import Psychic
import qualified Data.Map.Strict as Map
import Data.List(genericLength)

bsearch1 :: Prog
bsearch1 =
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
         -- (hi := Local mid)
         (hi := Minus (Local mid) (Value 1))
         (lo := Plus (Local mid) (Value 1)))) `Then`
  Point "post"

bsearch2 :: Prog
bsearch2 =
  Arg arr (Ordered Le (Local arr)) $
  Arg x (Value True) $
  Body $
  lo := Value 0 `Then`
  hi := Length (Local arr) `Then`
  found := Value False `Then`
  While (And (Not (Local found)) (Rel Lt (Local lo) (Local hi))) (Rel Le (Value 0) (Local lo) `And` (Rel Le (Local lo) (Local hi)) `And` (Rel Le (Local hi) (Length (Local arr))))
    (Point "invariant" `Then`
     mid := Div (Plus (Local lo) (Local hi)) (Value 2) `Then`
     If (Rel Eq (Local x) (At (Local arr) (Local mid)))
       (found := Value True `Then` idx := Local mid)
       (If (Rel Le (Local x) (At (Local arr) (Local mid)))
         (hi := Local mid)
         --(hi := Minus (Local mid) (Value 1))
         (lo := Plus (Local mid) (Value 1)))) `Then`
  Point "post"

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

memberSig = [styled "member" (\x arr -> Not (Pairwise Ne (Singleton x) (Image arr))) uncurried 1]

pre :: Given (Gen Env) => Sig
pre =
  signature [
    con "x" (Local x),
    con "arr" (Local arr),
    con "len" Length,
    styled "slice" (\arr i j -> Restrict arr (Interval i j)) sliceStyle 1,
    con "N" (Length (Local arr)),
    signature [base, {-scalar,-} memberSig]]

post :: Given (Gen Env) => Sig
post =
  signature [
    pre,
    con "found" (Local found),
    con "idx" (Local idx)]

inv :: Given (Gen Env) => Sig
inv =
  signature [
    post,
    con "lo" (Local lo),
    con "hi" (Local hi)]

tests :: [Env]
tests = map env [
  (0, []),
  (0, [0]),
  (123, [456]),
  (123, [123]),
  (-2, [-123,-6,-2,59,102]),
  (153, [-123,-6,-2,59]),
  (59, [-123,-6,-2,102]),
  (102, [-123,-6,-2,102]),
  (-100, [1, 2, 3, 4])]
  where
    env :: (Integer, [Integer]) -> Env
    env (xv, arrv) =
      let e0 = insertEnv x xv (insertEnv arr (toArray arrv) (Env Map.empty))
          foundv = lookupEnv found (postOf bsearch1 e0)
      in insertEnv found foundv e0

printTests = mapM_ print tests

unc :: (Given (Gen Env) => Sig) -> (Gen Env -> Sig, Gen Env -> Sig)
unc x = (\e -> mempty, \e -> give e x)

findSpec :: Prog -> String -> (Given (Gen Env) => Sig) -> IO ()
findSpec prog phase sig = uncurry (impSpec (Just chaos) (genPoint prog phase)) (unc sig)
  where
    chaos = do
      env <- genChaos prog
      let n = eval env (Length (Local arr))
      vlo <- Index <$> choose (0, fromIntegral n)
      vhi <- Index <$> choose (fromIntegral vlo, fromIntegral n)
      return (insertEnv lo vlo (insertEnv hi vhi env))

findSpecTests :: Prog -> [Env] -> String -> (Given (Gen Env) => Sig) -> IO ()
findSpecTests prog tests phase sig = uncurry (impSpec (Just chaos) (genPointFrom (elements tests) prog phase)) (unc sig)
  where
    chaos = do
      env <- genChaos prog
      let n = eval env (Length (Local arr))
      vlo <- Index <$> choose (0, fromIntegral n)
      vhi <- Index <$> choose (fromIntegral vlo, fromIntegral n)
      return (insertEnv lo vlo (insertEnv hi vhi env))

findPost :: Prog -> IO ()
findPost prog = findSpec prog "post" post

findInv :: Prog -> IO ()
findInv prog = findSpec prog "invariant" inv

findPsychic :: Prog -> [Env] -> IO ()
findPsychic prog tests =
  uncurry (psychicImpSpec prog (genChaos prog) (genPointFrom (elements tests) prog "post") (genPoint prog "post")) (unc post)

findInvPsychic :: Prog -> [Env] -> IO ()
findInvPsychic prog tests =
  uncurry (psychicImpSpec prog (genChaos prog) (genPointFrom (elements tests) prog "invariant") (genPoint prog "invariant")) (unc inv)

demo1 = findPsychic bsearch1 tests
demo2 = findPost bsearch2
demo3 = findPost bsearch1
demo4 = findInv bsearch2
{-
demo2 = uncurry (impSpec Nothing (genPoint bsearch "post")) (unc sig2)
demo2b = uncurry (impSpec Nothing (genPoint bsearch "post" `suchThat` lookupEnv found)) (unc sig2)
demo2c = uncurry (impSpec Nothing (genPoint bsearch "post" `suchThat` (not . lookupEnv found))) (unc sig2)
demo3 = uncurry (impSpec Nothing (genPoint bsearch "invariant")) (unc sig3)
demo4 = uncurry (impSpec Nothing (genPoint dutchFlag "post")) (unc sig4)
demo5 = uncurry (impSpec Nothing (genPoint dutchFlag "invariant")) (unc sig4)
demo6 = uncurry (impSpec (Just gen) (genPoint partitioning "post")) (unc sig4)
  where gen = genAny [Some arr, Some i, Some j, Some n, Some md]
demo7 = uncurry (impSpec Nothing (genPoint partitioning "invariant")) (unc sig4)

demo8 = uncurry (impSpec (Just (genChaos bsearchBug)) (genPoint bsearchBug "post")) (unc sig3)
demo9 = uncurry (impSpec (Just (genChaos bsearchBug)) (genPointFrom (elements tests) bsearchBug "post")) (unc sig3)
demo10 = uncurry (impSpec (Just (genChaos bsearch)) (genPoint bsearch "post")) (unc sig3)

demo11 = uncurry (psychicImpSpec bsearchBug (genPointFrom (elements tests) bsearchBug "post") (genPoint bsearchBug "post")) (unc sig3)
-}
