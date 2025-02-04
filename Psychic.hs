{-# LANGUAGE ScopedTypeVariables #-}
module Psychic where

import QuickSpec.Internal as QS hiding (quickSpec)
import QuickSpec.Internal.Haskell hiding (con)
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Type hiding (In)
import QuickSpec.Internal.Utils
import qualified QuickSpec.Internal.Term as QuickSpec.Internal
import qualified QuickSpec.Internal.Testing.QuickCheck as QuickCheck
import Twee.Base(Term)
import Test.QuickCheck
import Test.QuickCheck.Poly
import Data.Maybe
import Data.List
import Control.Monad
import Data.Functor.Identity
import Twee.Pretty
import Debug.Trace
import Data.IORef
import Eval
import Prog
import Debug.Trace

getVars :: Prog -> TestCase -> Env
getVars prog tc =
  let Just val = tc_test_result tc (toValue (Identity GetEnv))
  in traceShow val $ let Just (Ordy env) = fromValue val in env

psychic :: forall t sig. (Show t, Typeable t, Signature sig) => Prog -> Gen t -> (t -> [t]) -> Gen t -> (Gen t -> sig) -> IO ()
psychic prog tests shr gen sig = do
  thy <- quickSpec cfg
  loop [] thy
  where
    loop _ [] = return ()
    loop tcs (prop:props) = do
      mtc <- consider tcs prop
      case mtc of
        Nothing -> loop tcs props
        Just tc -> loop (tc:tcs) props

    cfgFrom gen =
      unSig (signature (sig gen))
        (Context 1 []) defaultConfig
    cfg = cfgFrom tests
    cfg' = cfgFrom gen

    instsFrom gen = cfg_instances (cfgFrom gen) `mappend` baseInstances
    insts = cfg_instances cfg `mappend` baseInstances
    insts' = cfg_instances cfg' `mappend` baseInstances

    test tcs prop =
      case foldr testAnd TestPassed [QuickCheck.quickCheckTest (QuickCheck.Environment (cfg_quickCheck cfg') tcs eval) prop tc | tc <- tcs] of
        TestPassed -> True
        _ -> False

    consider tcs prop
      -- | not (test tcs prop) = return Nothing
      | otherwise = do
        ref <- newIORef Nothing
        quickCheckWith stdArgs { maxSuccess = QuickCheck.cfg_num_tests (cfg_quickCheck cfg'), maxSize = QuickCheck.cfg_max_test_size (cfg_quickCheck cfg') } $
          counterexample (prettyShow (prettyProp (names insts') prop)) $
          forAllShrinkShow gen shr show $ \tc ->
            whenFail (writeIORef ref (Just tc)) $
            forAllBlind (arbitraryTestCase (cfg_default_to cfg) (instsFrom (return tc))) $ \tcc ->
              test [tcc] prop
        readIORef ref
      where
        shr1 cex =
          [ cex { tc_eval_var = \y -> if x == y then Just (toValue (Identity z)) else tc_eval_var cex y }
          | x <- usort (QuickSpec.Internal.vars prop),
            typ x == typeOf (undefined :: t),
            Just val <- [tc_eval_var cex x],
            Just (Identity y) <- [fromValue val :: Maybe (Identity t)],
            z <- shr y ]

    eval = evalHaskell (cfg_default_to cfg) insts
