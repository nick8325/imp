{-# LANGUAGE ScopedTypeVariables #-}
module Psychic where

import QuickSpec.Internal as QS hiding (quickSpec)
import QuickSpec.Internal.Haskell hiding (con, TestCase)
import QuickSpec.Internal.Testing
import QuickSpec.Internal.Prop
import QuickSpec.Internal.Type hiding (In)
import QuickSpec.Internal.Utils
import qualified QuickSpec.Internal.Term as QuickSpec.Internal
import QuickSpec.Internal.Explore.PartialApplication(PartiallyApplied)
import qualified QuickSpec.Internal.Testing.QuickCheck as QuickCheck
import Twee.Base(Extended, Term)
import Test.QuickCheck
import Test.QuickCheck.Poly
import Data.Maybe
import Data.List
import Control.Monad
import Data.Functor.Identity
import Twee.Pretty
import Debug.Trace
import Data.IORef

psychic :: forall t sig. (Show t, Typeable t, Signature sig) => [t] -> (t -> [t]) -> sig -> IO ()
psychic tests shr sig = do
  thy <- quickSpec cfg
  loop [] thy
  where
    loop _ [] = return ()
    loop tcs (prop:props) = do
      mtc <- consider tcs prop
      case mtc of
        Nothing -> loop tcs props
        Just tc -> loop (tc:tcs) props

    cfg =
      unSig (hardcoded `mappend` signature sig)
        (Context 1 []) defaultConfig
    cfg' =
      unSig (signature sig)
        (Context 1 []) defaultConfig
    insts = cfg_instances cfg' `mappend` baseInstances
    hardcoded = instFun (elements tests)

    consider tcs prop
      | isJust (QuickCheck.quickCheckTest (QuickCheck.Environment (cfg_quickCheck cfg') tcs eval) prop) = return Nothing
      | otherwise = do
        ref <- newIORef Nothing
        quickCheckWith stdArgs { maxSuccess = QuickCheck.cfg_num_tests (cfg_quickCheck cfg'), maxSize = QuickCheck.cfg_max_test_size (cfg_quickCheck cfg') } $
          counterexample (prettyShow (prettyProp (names insts) prop)) $
          forAllShrinkShow (arbitraryTestCase (cfg_default_to cfg') insts) shr1 (show . get) $ \tc ->
            whenFail (writeIORef ref (Just tc)) $
            counterexample "" $
            isNothing (QuickCheck.quickCheckTest (QuickCheck.Environment (cfg_quickCheck cfg') [tc] eval) prop)
        readIORef ref
      where
        shr1 cex =
          [ cex { tc_eval_var = \y -> if x == y then Just (toValue (Identity z)) else tc_eval_var cex y }
          | x <- usort (QuickSpec.Internal.vars prop),
            typ x == typeOf (undefined :: t),
            Just val <- [tc_eval_var cex x],
            Just (Identity y) <- [fromValue val :: Maybe (Identity t)],
            z <- shr y ]
        get cex =
          head
            [ y
            | x <- usort (QuickSpec.Internal.vars prop),
              typ x == typeOf (undefined :: t),
              Just val <- [tc_eval_var cex x],
              Just (Identity y) <- [fromValue val :: Maybe (Identity t)] ]

    eval = evalHaskell (cfg_default_to cfg) insts
