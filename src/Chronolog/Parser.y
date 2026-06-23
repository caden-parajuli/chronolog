{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Chronolog.Parser where

import Chronolog.Lexer

import Control.Exception (Exception)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, elemIndex, splitAt, drop, find)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Exts (fromString, IsString)
import qualified System.Environment as Env
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))

import Chronolog.Grammar

}

%name       fileParser File
%name       ruleParser DocRule
%name       queryParser Atom
%name       exprParser Argument

%tokentype { Token }
%error     { parseError }
%monad     { Alex }
%lexer     { lexer } { Token _ _ TEOF }

%right ','
-- Avoid shift-reduce conflict for HypsCut
%left '('

%token
      ','     { Token _ _ Tcomma      }
      ':-'    { Token _ _ Tif         }
      '.'     { Token _ _ Tperiod     }
      '('     { Token _ _ Tlparen     }
      ')'     { Token _ _ Trparen     }
      '['     { Token _ _ Tlbracket   }
      ']'     { Token _ _ Trbracket   }
      '!'     { Token _ _ Tcut        }
      '^'     { Token _ _ Tcaret      }
      '$'     { Token _ _ Trequire    }
      var     { Token _ _ (Tvar $$)   }
      name    { Token _ _ (Tname $$)  }
      quote   { Token _ _ (Tquote $$) }
      doc     { Token _ _ (Tdoc $$)   }
%%

File :: { File }
: Rules { $1 }

Rules :: { [DocRule] }
: DocRule Rules { $1 : $2 }
| DocRule       { [$1] }

DocRule :: { DocRule }
: Docs Rule  { DocRule $2{ name = fromString . fromMaybe "" . fmap snd $ find ((== "name") . fst) $1 } $1 }

Docs :: { [(String, String)] }
: {- empty -}   { [] }
| Doc Docs      { $1 : $2 }

Doc :: { (String, String) }
: doc   { splitDoc $1 }

Rule :: { Rule String String String }
: Atom '.'                            { mkRule (fromString "") [] $1 }
| Atom ':-' '!' '.'                   { mkRule' (fromString "") [] $1 (\r -> r{ cutRuleOpt = True }) }
| Atom ':-' Existentials HypsCut '.'  { mkRule' (fromString "") (fst $4) $1 (\r -> r{ cutRuleOpt = snd $4, existentialVarsRuleOpt = $3 }) }

-- Chronolog supports cut rules where the cut is at the beginning of the rule
HypsCut :: { ([Hyp String String String], Bool) }
: Hyps                { ($1, False) }
| '!' ',' Hyps        { ($3, True) }
| '(' HypsCut ')'     { $2 }

Hyps :: { [Hyp String String String] }
: Hyps ',' Hyps        { $1 ++ $3  }
| Hyp                  { [$1] }
| '(' Hyps ')'         { $2 }

Hyp :: { Hyp String String String }
: Atom     { GoalHyp (mkHypGoal $1) }
| '$' Atom { GoalHyp (mkHypGoal $2){ goalOpts = defaultGoalOpts{ requiredGoalOpt = True } } }

Existentials :: { Set String }
: {- empty -}                     { Set.empty }
| var '^' Existentials            { Set.insert (fromString $1) $3 }
| '(' VarSet ')' '^' Existentials { Set.union $2 $5 }

VarSet :: { Set String }
: var                  { Set.singleton (fromString $1) }
| VarSet ',' var       { Set.insert (fromString $3) $1 }

Atom :: { Atom String String String }
: name '(' Arguments ')' { Atom (fromString $1) $3 }

Arguments :: { [Expr String String] }
: Argument                { [$1] }
| Argument ',' Arguments  { $1 : $3 }

Argument :: { Expr String String }
: Con                 { ConExpr $1 }
| var                 { mkVarExpr $ fromString $1 }
-- | quote               { Quote $1 }
-- | '[' Arguments ']'   { List $2 }

Con :: { Con String String }
: name '(' Arguments ')' { Con (fromString $1) $3 }
| name                   { Con (fromString $1) [] }

{

type File = [DocRule]

parseError :: Token -> Alex a
parseError (Token _ (AlexPn p _ _) t) = alexError ("P" ++ show (p + 1))

-- Left lexError, Right parseError
data ParseErrorMessage = LexerError String | ParserError String

instance Show ParseErrorMessage where
  show (LexerError e) = "Lexer error: " ++ e
  show (ParserError e) = "Parser error: " ++ e

instance Exception ParseErrorMessage

data DocRule = DocRule (Rule String String String) [(String, String)]

addNameRule :: String -> Rule a c v -> Rule a c v
addNameRule name rule = 
  if rule.name == fromString ""
  then renameRule name rule
  else rule

renameRule :: String -> Rule a c v -> Rule a c v
renameRule name rule = rule{ name = fromString name }

processParseRes :: Either String r -> Either ParseErrorMessage r
processParseRes res = 
  case res of
      Right r  -> Right r
      Left  s' -> case head s' of
                    'L' -> Left (LexerError (tail s'));
                    'P' -> Left (ParserError (tail s'));
                     _  -> Left (ParserError "0") -- This should never happen

parse :: String -> String -> Either ParseErrorMessage File
parse filename s =
  let p = do
            alexSetFilename filename
            fileParser
  in case processParseRes (runAlex s p) of
       Left  l   -> Left l
       -- Number the unnamed rules in the file
       Right res -> Right $ map
                              (\(i, (DocRule rule doc)) -> (DocRule (addNameRule (show i) rule) doc))
                              $ zip [1..] res

parseFile :: String -> IO (Either ParseErrorMessage File)
parseFile filename = do
  content <- readFile filename
  return $ case parse filename content of
             Left e -> Left e
             Right r -> Right r

parseRule :: String -> String -> Either ParseErrorMessage DocRule
parseRule name s = 
  let p = (do
             alexSetFilename name
             ruleParser)
  in 
  case processParseRes (runAlex s p) of
      Left  l -> Left l
      Right (DocRule rule doc)  -> Right $ DocRule (addNameRule name rule) doc

parseRule' :: String -> String -> (RuleOpts String String String -> RuleOpts String String String) -> Either ParseErrorMessage DocRule
parseRule' name s f_ruleOpts = 
  case parseRule name s of
    Left  l   -> Left l
    Right (DocRule rule doc) -> Right $ DocRule rule{ ruleOpts = f_ruleOpts defaultRuleOpts } doc


parseQuery :: String -> Either ParseErrorMessage (Atom String String String)
parseQuery s = 
  let p = (do
             alexSetFilename "query"
             queryParser)
  in 
  processParseRes (runAlex s $ p)


parseExpr :: String -> Either ParseErrorMessage (Expr String String)
parseExpr s = 
  let p = (do
             alexSetFilename "expr"
             exprParser)
  in 
  processParseRes (runAlex s $ p)

-- Note that this also clobbers suspendRuleOpt!
mapNamesRule :: forall a1 a2 c1 c2 v1 v2. (Ord v1, Ord v2) => (a1 -> a2) -> (c1 -> c2) -> (v1 -> v2) -> Rule a1 c1 v1 -> Rule a2 c2 v2
mapNamesRule fa fc fv (Rule name hyps conc ruleOpts) =
  Rule name (map mapNamesHyp hyps) (mapNamesAtom conc) (mapNamesRuleOpts ruleOpts)
    where
      mapNamesHyp :: Hyp a1 c1 v1 -> Hyp a2 c2 v2
      mapNamesHyp (GoalHyp (Goal atom goalOpts goalIndex)) = (GoalHyp (Goal (mapNamesAtom atom) goalOpts goalIndex))

      mapNamesRuleOpts :: RuleOpts a1 c1 v1 -> RuleOpts a2 c2 v2
      mapNamesRuleOpts (RuleOpts cutRuleOpt _ existentialVarsRuleOpt) = RuleOpts cutRuleOpt Nothing (Set.map fv existentialVarsRuleOpt)

      mapNamesAtom :: Atom a1 c1 v1 -> Atom a2 c2 v2
      mapNamesAtom (Atom name args) = Atom (fa name) (map (mapNamesExpr fc fv) args)

mapNamesExpr :: (c1 -> c2) -> (v1 -> v2) -> Expr c1 v1 -> Expr c2 v2
mapNamesExpr fc fv (ConExpr (Con name args)) = ConExpr (Con (fc name) (map (mapNamesExpr fc fv) args))
mapNamesExpr fc fv (VarExpr (Var labelVar indexVar)) = VarExpr (Var (fv labelVar) indexVar)

stripSpace :: String -> String
stripSpace = dropWhileEnd isSpace . dropWhile isSpace

splitDoc :: String -> (String, String)
splitDoc s = 
  case elemIndex ':' s of
    Nothing -> ("", "")
    Just i -> let (k, v) = splitAt i s
               in (stripSpace k, stripSpace . drop 1 $ v)

}


