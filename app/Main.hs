module Main (main) where

import qualified Chronolog.Engine as Engine
import Chronolog.Grammar
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint), render, text, (<+>))
import qualified Data.List as List

main :: IO ()
main = mkAddTest 7 8 15

mkAddTest :: Int -> Int -> Int -> IO ()
mkAddTest a b c = do
  putStrLn (render $ pPrint a <+> text "+" <+> pPrint b <+> text "=" <+> pPrint c)
  let cfg =
        Engine.Config
          { rules = rulesAdd
          , exprAliases = []
          , initialGas = Engine.InfiniteGas
          , goals = [mkGoal 0 $ eq (plus (fromInt a) (fromInt b)) (fromInt c)]
          , shouldSuspend = const False
          }
  let branches' = Engine.runConfig cfg
  let numSolutions = List.length branches'
  putStrLn $ show numSolutions ++ " solutions found"

type A = String
type C = String
type V = String

rulesAdd :: [Rule A C V]
rulesAdd =
  [ mkRule (RuleName "0+")
      []
      $ (zero `plus` x) `eq` x
  , mkRule (RuleName "+0")
      []
      $ (x `plus` zero) `eq` x
  , mkRule (RuleName "S+")
      [GoalHyp . mkHypGoal $ (x `plus` y) `eq` z]
      $ (s x `plus` y) `eq` s z
  , mkRule (RuleName "+S")
      [GoalHyp . mkHypGoal $ (x `plus` y) `eq` z]
      $ (x `plus` s y) `eq` s z
  ]
  where
    (x, z, y) = (var "x", var "y", var "z")

eq :: Expr C V -> Expr C V -> Atom A C V
eq x y = Atom "Equal" [x, y]

plus :: Expr C V -> Expr C V -> Expr C V
plus x y = ConExpr (Con "Add" [x, y])

var :: V -> Expr C V
var v = VarExpr (Var v Nothing)

s :: Expr C V -> Expr C V
s x = ConExpr (Con "S" [x])

zero :: Expr C V
zero = ConExpr (Con "Z" [])

fromInt :: Int -> Expr C V
fromInt 0 = zero
fromInt x = s (fromInt (x - 1))
