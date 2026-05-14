{-# LANGUAGE OverloadedStrings #-}

module Spec.Engine.Parser (tests) where

import Chronolog.Engine as Engine
import Chronolog.Grammar
import Chronolog.Parser
import Spec.Engine.Common
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import Control.Monad (sequence)

tests :: TestTree
tests =
  testGroup
    "Parser"
    [ mkParsingTest
        "Subtyping"
        rulesSubtyping
        -- (sequence rulesSubtyping)
        (parseQuery "subtype(arr(int, bool), arr(nat, bool))")
        EngineSuccess
    ]

rulesSubtyping :: Either ParseErrorMessage [(Rule A C V)]
rulesSubtyping =
  parse "SubtypingRules" "subtype(bool, bool).\n\
                         \subtype(int, int).\n\
                         \subtype(nat, nat).\n\
                         \subtype(nat, int).\n\
                         \subtype(arr(A, B), arr(A', B')) :- subtype(A', A), subtype(B', B)."
  -- [ parseRule "bool <: bool" "subtype(bool, bool).",
  --   parseRule "int <: int" "subtype(int, int).",
  --   parseRule "nat <: nat" "subtype(nat, nat).",
  --   parseRule "nat <: int" "subtype(nat, int).",
  --   parseRule "arrow" "subtype(arr(A, B), arr(A', B')) :- subtype(A', A), subtype(B', B)." ]

mkParsingTest :: TestName -> Either ParseErrorMessage [(Rule A C V)] -> Either ParseErrorMessage (Atom A C V) -> EngineResult C V -> TestTree
mkParsingTest testName parsedRules parsedGoal expected =
  case parsedRules of
    Left (Left e) -> testCase testName (assertFailure e)
    Left (Right e) -> testCase testName (assertFailure e)
    Right rules -> case parsedGoal of
                     Left (Left e) -> testCase testName (assertFailure e)
                     Left (Right e) -> testCase testName (assertFailure e)
                     Right goal -> mkTest_Engine
                                    testName
                                    (Engine.Config
                                       { initialGas = FiniteGas 50,
                                         strategy = DepthFirstStrategy defaultDepthFirstStrategyOpts,
                                         rules = rules,
                                         exprAliases = [],
                                         goals = [mkGoal 0 goal],
                                         shouldSuspend = const False,
                                         -- shouldSuspend = \case
                                         --   Goal {atom = VarExpr _ :<: VarExpr _} -> True
                                         --   _ -> False,
                                         useIndexing = True
                                       }
                                    )
                                    expected
