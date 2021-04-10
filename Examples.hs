{-# LANGUAGE FlexibleContexts #-}
module Examples where

import Prog
import ImpSpec
import Data.Reflection
import Eval
import QuickSpec
import Test.QuickCheck hiding ((==>), Ordered)
import Twee.Pretty

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

-- Postcondition
memberSig = [styled "member" (\x arr -> Not (Pairwise Ne (Singleton x) (Image arr))) uncurried 1]

sig2 :: Given (Gen Env) => [Sig]
sig2 = [
  background [base, scalar, arrays, memberSig],
  series [
    [con "x" (Local x),
     con "arr" (Local arr)],
    [con "found" (Local found),
     con "idx" (Local idx) ]]]
demo2 pt = give (genPoint bsearch pt) (quickSpec sig2)
demo2b pt = give (genPoint bsearch pt `suchThat` lookupEnv found) (quickSpec sig2)
demo2c pt = give (genPoint bsearch pt `suchThat` (not . lookupEnv found)) (quickSpec sig2)
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
