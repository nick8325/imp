{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}

import Test.QuickCheck hiding (output)
import Test.QuickCheck.Poly( A )
import Test.QuickCheck.All
import Control.Monad
import QuickSpec hiding (vars)
import QuickSpec.Internal hiding (vars)
import QuickSpec.Internal.Haskell(SingleUse(..))
import Psychic

--------------------------------------------------------------------------------

type Name = Int

data Expr
  = Expr :+: Expr
  | Expr :*: Expr
  | Num Integer
  | Var Name
 deriving ( Show, Ord, Eq )

eval :: Expr -> [Integer] -> Integer
eval (a :+: b) xs = eval a xs + eval b xs
eval (a :*: b) xs = eval a xs * eval b xs
eval (Num n)   xs = n
eval (Var i)   xs = (xs ++ repeat 0)!!i

vars :: Expr -> Int
vars (a :+: b) = vars a `max` vars b
vars (a :*: b) = vars a `max` vars b
vars (Num _)   = 0
vars (Var i)   = i+1

--------------------------------------------------------------------------------

data Instr
  = Add | Mul | Push Integer | Copy Int
 deriving ( Show, Ord, Eq )

instance Arbitrary Instr where
  arbitrary = oneof [return Add, return Mul, Push <$> arbitrary, fmap (Copy . getNonNegative) arbitrary]

compile :: Expr -> [Instr]
compile e = comp 0 e
 where
  -- ASK: any of these right-hand sides
  comp off (a :+: b) =
    comp off a ++ comp (off+1) b ++ [Add]

  comp off (a :*: b) =
    comp off a ++ comp off b ++ [Mul]

  comp off (Num n) =
    [Push n]

  comp off (Var i) =
    [Copy (i+off)]

exec :: Instr -> [Integer] -> [Integer]
exec Add      (a:b:st) = (a+b)  :st
exec Mul      (a:b:st) = (a*b)  :st
exec (Push n) st       = n      :st
exec (Copy j) st       = ((st ++ repeat 0)!!j):st

run :: [Instr] -> [Integer] -> [Integer]
run []     st = st
run (i:is) st = run is (exec i st)

--------------------------------------------------------------------------------

prop_Correct e =
  forAll arbitrary {-(vector (vars e))-} $ \xs ->
    run (compile e) xs == eval e xs : xs

wellScoped :: Expr -> [Integer] -> Bool
wellScoped e xs = length xs >= vars e

genWellScopedC :: Gen (Compile, ([Integer], ()))
genWellScopedC = do
  c <- arbitrary
  xs <- vector (vars (input c))
  ys <- arbitrary
  return (c, (xs ++ ys, ()))

genWellScoped :: Gen (Expr, ([Integer], ()))
genWellScoped = do
  (c, (xs, ())) <- genWellScopedC
  return (input c, (xs, ()))

data Compile = Compile { input :: Expr, output :: [Instr] }
  deriving (Eq, Ord, Show)

toCompile :: Expr -> Compile
toCompile e = Compile e (compile e)

instance Arbitrary Compile where
  --arbitrary = toCompile <$> arbitrary
  --shrink c = map toCompile (shrink (input c))
  arbitrary = elements tests

main = quickSpec [
--main = psychic tests shrink [
  monoTypeWithVars ["e"] (Proxy :: Proxy Expr),
  monoTypeWithVars ["C"] (Proxy :: Proxy Compile),
  instFun (SingleUse :: SingleUse Compile),
  monoTypeWithVars ["instr"] (Proxy :: Proxy Instr),
  con "eval" eval,
  con "run" run,
  con "compile" compile,
  con "input" input,
  --con "output" output,
  --predicateGen "wellScoped" wellScoped (\() -> genWellScoped),
  --predicateGen "wellScopedC" (wellScoped . input) (\() -> genWellScopedC),
  lists ]

tests :: [Compile]
tests =
  map toCompile $
    [Var 0 :+: Var 1,
     Var 0,
     Num 3,
     Num 3 :+: (Num 5 :*: Num 5),
     Var 2 :*: Num 2]

--------------------------------------------------------------------------------

instance Arbitrary Expr where
  arbitrary = sized arb
   where
    arb n = frequency 
      [ (1, Num `fmap` arbitrary)
      , (1, Var `fmap` choose (0,10))
      , (n, liftM2 (:+:) arb2 arb2)
      , (n, liftM2 (:*:) arb2 arb2)
      ]
     where
      arb2 = arb (n `div` 2)

  shrink (a :+: b) = [a, b]
                  ++ [a' :+: b | a' <- shrink a]
                  ++ [a :+: b' | b' <- shrink b]
  shrink (a :*: b) = [a, b]
                  ++ [a' :*: b | a' <- shrink a]
                  ++ [a :*: b' | b' <- shrink b]
  shrink (Num n)   = [Num n' | n' <- shrink n, n' > 0]
  shrink (Var i)   = [Var i' | i' <- shrink i]

return []
testAll = $(quickCheckAll)

