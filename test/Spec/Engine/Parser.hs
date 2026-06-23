{-# LANGUAGE OverloadedStrings #-}

module Spec.Engine.Parser (tests) where

import Chronolog.Engine as Engine
import Chronolog.Grammar
import Chronolog.Parser
import Spec.Engine.Common
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

tests :: TestTree
tests =
  testGroup
    "Parser"
    [ mkParsingTest
        "SubtypingSimple"
        rulesSubtyping
        (parseQuery "subtype(arr(int, bool), arr(nat, bool))")
        EngineSuccess,

      mkParsingTest
        "SubtypingAppl"
        rulesSubtypingAppl
        (parseQuery "subtype(zero, \
                            \true, \
                            \type(N1, arrow(type(N2, const(nat)), type(N3, const(nat)))), \
                            \type(M1, arrow(type(M2, const(nat)), type(M3, const(nat)))), \
                            \Constraints, \
                            \Coercion)")
        EngineSuccess
    ]

rulesSubtyping :: Either ParseErrorMessage [DocRule]
rulesSubtyping =
  parse "SubtypingSimple" "subtype(bool, bool). \n\
                          \subtype(int, int). \n\
                          \subtype(nat, nat). \n\
                          \subtype(nat, int). \n\
                          \subtype(arr(A, B), arr(A', B')) :- subtype(A', A), subtype(B', B)."

rulesSubtypingAppl :: Either ParseErrorMessage [DocRule]
rulesSubtypingAppl =
  parse "SubtypingAppl" "% Type constants\n\
                        \constant(nat). \n\
                        
                        \% Types\n\
                        \type(N, const(C)) :- constant(C). \n\
                        \type(N, arrow(T1, T2)). \n\
                        
                        \% Subtyping\n\
                        \% true is for +k, false is for -k \n\
                        
                        \subtype(K, true, type(N, const(C)), type(M, const(C)), cons(lte(N, pl(K, M)), nil), natcoe(N, M, K)). \n\
                        \subtype(K, false, type(N, const(C)), type(M, const(C)), cons(lte(pl(K, N), M), nil), natcoe(N, M, K)). \n\
                        
                        \subtype(K, true, type(N, arrow(T1, T2)), type(M, arrow(T1p, T2p)), cons(lte(N, pl(J, pl(K, M))), concat(L1, L2)), arrowcoe(N, M, K, J, Coe1, Coe2)) \n\
                        \  :- subtype(J, true, T1p, T1, L1, Coe1), \n\
                        \     subtype(J, false, T2, T2p, L2, Coe2). \n\
                        
                        \subtype(K, false, type(N, arrow(T1, T2)), type(M, arrow(T1p, T2p)), cons(lte(pl(K, N), pl(M, J)), concat(L1, L2)), arrowcoe(N, M, K, J, Coe1, Coe2)) \n\
                        \  :- subtype(J, true, T1p, T1, L1, Coe1), \n\
                        \     subtype(J, false, T2, T2p, L2, Coe2)."


mkParsingTest :: TestName -> Either ParseErrorMessage [DocRule] -> Either ParseErrorMessage (Atom A C V) -> EngineResult C V -> TestTree
mkParsingTest testName parsedRules parsedGoal expected =
  case parsedRules of
    Left e -> testCase testName . assertFailure $ "Rule parsing " ++ show e
    Right rules' -> case parsedGoal of
                     Left e -> testCase testName . assertFailure $ "Query parsing " ++ show e
                     Right goal' -> mkTest_Engine
                                    testName
                                    (Engine.Config
                                       { initialGas = FiniteGas 50,
                                         strategy = DepthFirstStrategy defaultDepthFirstStrategyOpts,
                                         rules = map (\(DocRule rule _) -> rule) rules',
                                         exprAliases = [],
                                         goals = [mkGoal 0 goal'],
                                         shouldSuspend = const False,
                                         useIndexing = True
                                       }
                                    )
                                    expected
