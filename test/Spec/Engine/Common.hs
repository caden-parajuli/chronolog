{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.Engine.Common where

import Control.Category ((>>>))
import Control.Monad (when)
import Control.Monad.Except (runExceptT)
import Control.Monad.Writer (WriterT)
import Chronolog.Common.Msg (Msg)
import qualified Chronolog.Common.Msg as Msg
import Chronolog.Engine as Engine
import Chronolog.Grammar
import Data.Foldable (traverse_)
import Data.Function ((&))
import Data.Functor ((<&>))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Spec.Common as Common
import qualified Spec.Config as Config
import System.FilePath ((</>))
import Test.Tasty as Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertFailure, testCase)
import Text.PrettyPrint (Doc, brackets, hang, render, text, vcat, ($+$), (<+>))
import Text.PrettyPrint.HughesPJClass (Pretty (..))
import Utility (bullets, ticks)
import Prelude hiding (div)

--------------------------------------------------------------------------------

goldenDirpath :: FilePath
goldenDirpath = Common.goldenDirpath </> "Engine"

--------------------------------------------------------------------------------

type A = String

type C = String

type V = String

--------------------------------------------------------------------------------

-- |
-- A `EngineResult` has some optional associated metadata about how the run
-- went.
data EngineResult c v
  = -- | Engine run resulted in no branches that solved all goals.
    EngineFailure
  | -- |
    -- Engine run resulted in at least one branch that solved all goals and
    -- all successful branches had no suspended goals.
    EngineSuccess
  | -- |
    -- Engine run resulted in at least one branch that solved all goals and had
    -- some suspended goals.
    EngineSuccessWithSuspends
  | -- | Engine run resulted in each solution branch having no suspended goals.
    EngineSuccessWithoutSuspends
  | -- | Engine run resulted in at least `n` branches that solved all goals.
    EngineSuccessWithSolutionsCount Int
  | -- |
    -- Engine run resulted in each solution branch using a substitution that is
    -- a sub-substitution of the `sigma`.
    EngineSuccessWithSubst (Subst c v)
  deriving (Show, Eq)

instance (Pretty c, Pretty v) => Pretty (EngineResult c v) where
  pPrint EngineFailure = "failure"
  pPrint EngineSuccess = "success"
  pPrint EngineSuccessWithSuspends = "success with suspends"
  pPrint EngineSuccessWithoutSuspends = "success without suspends"
  pPrint (EngineSuccessWithSolutionsCount n) = "success with" <+> pPrint n <+> "solutions"
  pPrint (EngineSuccessWithSubst _) = "success with subst"

mkTest_Engine :: forall a c v. (Pretty a, Ord a, Show a, Pretty c, Pretty v, Ord v, Ord c, Show c, Show v) => TestName -> Engine.Config a c v -> EngineResult c v -> TestTree
mkTest_Engine testName cfg result_expected = testCase (render (text testName <+> brackets (pPrint result_expected))) do
  let envs = Engine.runConfig cfg

  putStrLn "\n\n"
  print (fmap pPrint envs)
  putStrLn "\n\n"

  mb_err :: Maybe Doc <- case envs of
    _ | envs_successful <- envs & filter \env -> null env.failedGoals,
        not (null envs_successful) ->
          case result_expected of
            EngineFailure -> return $ Just $ pPrint $ EngineSuccess @c @v
            --
            EngineSuccess -> return Nothing
            EngineSuccessWithSuspends ->
              let envs_successfulWithSuspends = envs_successful & filter \env -> not (null env.suspendedGoals)
               in if null envs_successfulWithSuspends
                    then return $ Just $ pPrint $ EngineSuccessWithoutSuspends @c @v
                    else return Nothing
            EngineSuccessWithoutSuspends ->
              let envs_successfulWithSuspends = envs_successful & filter \env -> not (null env.suspendedGoals)
               in if not $ null envs_successfulWithSuspends
                    then return $ Just $ pPrint $ EngineSuccessWithSuspends @c @v
                    else return Nothing
            EngineSuccessWithSolutionsCount n ->
              if (envs_successful & length) == n
                then return Nothing
                else return $ Just $ pPrint (EngineSuccessWithSolutionsCount @c @v (envs_successful & length)) $+$ bullets (fmap pPrint envs)
            EngineSuccessWithSubst s ->
              let m = s & unSubst
                  m_keys = m & Map.keysSet
               in case envs_successful
                    <&> ( \env ->
                            ( env,
                              let m' = env.sigma & unSubst
                                  m'_keys = m' & Map.keysSet
                                  keys = Set.union m_keys m'_keys
                               in keys & Set.toList & foldMap \x -> case (m Map.!? x, m' Map.!? x) of
                                    (Just e, Just e') -> [(x, e, Just e') | e /= e']
                                    (Just e, Nothing) -> [(x, e, Nothing)]
                                    (Nothing, _) -> []
                            )
                        )
                    & filter (\(_env, mismatches) -> not $ null mismatches) of
                    envs_mismatching ->
                      if null envs_mismatching
                        then return Nothing
                        else
                          return $
                            Just $
                              hang "success with mismatches:" 2 . bullets $
                                envs_mismatching <&> \(env, mismatches) ->
                                  hang "env and mismatches:" 2 . bullets $
                                    [ hang "env:" 2 $ pPrint env,
                                      hang "mismatches:" 2 . bullets $
                                        mismatches <&> \case
                                          (x, e, Nothing) -> "expected" <+> ticks (pPrint x <+> ":=" <+> pPrint e) <+> "but actually is wasn't substituted"
                                          (x, e, Just e') -> "expected" <+> ticks (pPrint x <+> ":=" <+> pPrint e) <+> "but actually" <+> ticks (pPrint x <+> ":=" <+> pPrint e')
                                    ]
      | otherwise -> do
          case result_expected of
            EngineFailure -> return Nothing
            _ -> return $ Just $ pPrint (EngineFailure @c @v) $+$ bullets (fmap pPrint envs)

  case mb_err of
    Nothing -> return ()
    Just err -> do
      assertFailure . render $
        vcat
          [ "expected :" <+> pPrint result_expected,
            "actual   :" <+> err
          ]
