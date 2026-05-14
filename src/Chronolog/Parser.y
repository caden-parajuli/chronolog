{

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Chronolog.Parser where

import Chronolog.Lexer

import Data.Text(Text,pack,unpack)
import GHC.Exts (fromString, IsString)
import qualified System.Environment as Env
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))

import Chronolog.Grammar

}

%name       fileParser File
%name       ruleParser Rule
%name       queryParser Atom

%tokentype { Token }
%error     { parseError }
%monad     { Alex }
%lexer     { lexer } { Token _ _ TEOF }

%token
      ','     { Token _ _ Tcomma      }
      ':-'    { Token _ _ Tif         }
      '.'     { Token _ _ Tperiod     }
      '('     { Token _ _ Tlparen     }
      ')'     { Token _ _ Trparen     }
      '['     { Token _ _ Tlbracket   }
      ']'     { Token _ _ Trbracket   }
      var     { Token _ _ (Tvar $$)   }
      name    { Token _ _ (Tname $$)  }
      quote   { Token _ _ (Tquote $$) }
%%

File :: { forall a c v. (IsString a, IsString c, IsString v) => File a c v }
: Rules { $1 }

Rules :: { forall a c v. (IsString a, IsString c, IsString v) => [Rule a c v] }
: Rule Rules { $1 : $2 }
| Rule { [$1] }

Rule :: { forall a c v. (IsString a, IsString c, IsString v) => Rule a c v }
: Atom '.'            { mkRule (fromString "") [] $1 }
| Atom ':-' Atoms '.' { mkRule (fromString "") (map (GoalHyp . mkHypGoal) $3) $1 }

Atoms :: { forall a c v. (IsString a, IsString c, IsString v) => [Atom a c v] }
: Atom ',' Atoms { $1 : $3  }
| Atom           { [$1] }

Atom :: { forall a c v. (IsString a, IsString c, IsString v) => Atom a c v }
: name '(' Arguments ')' { Atom (fromString $1) $3 }

Arguments :: { forall c v. (IsString c, IsString v) => [Expr c v] }
: Argument                { [$1] }
| Argument ',' Arguments  { $1 : $3 }

Argument :: { forall c v. (IsString c, IsString v) => Expr c v }
: Con                 { ConExpr $1 }
| var                 { mkVarExpr $ fromString $1 }
{- | quote               { Quote $1 } -}
{- | '[' Arguments ']'   { List $2 } -}

Con :: { forall c v. (IsString c, IsString v) => Con c v }
: name '(' Arguments ')' { Con (fromString $1) $3 }
| name { Con (fromString $1) [] }

{

type File a c v = [Rule a c v]

parseError :: Token -> Alex a
parseError (Token _ (AlexPn p _ _) t) = alexError ("P" ++ show (p + 1))

-- Left lexError, Right parseError
type ParseErrorMessage = Either String String

-- This is an ugly solution. The parser should be able to make use of the filename,
-- but Happy seems to choke on monadic actions when the rules are polymorphic
renameRule :: String -> Rule a c v -> Rule a c v
renameRule name rule = rule{ name = fromString name }

processParseRes :: forall r. Either String r -> Either ParseErrorMessage r
processParseRes res = 
  case res of
      Right r  -> Right r
      Left  s' -> case head s' of
                    'L' -> Left (Left (tail s'));
                    'P' -> Left (Right (tail s'));
                     _  -> Left (Right "0") -- This should never happen

parse :: String -> String -> Either ParseErrorMessage (File String String String)
parse filename s =
  let p = do
            alexSetFilename filename
            fileParser
  in 
  case processParseRes (runAlex s p) of
    Left  l   -> Left l
    -- Number the rules in the file
    Right res -> Right $ map (\(i, rule) -> renameRule (show i) rule) (zip [1..] res)

parseFile :: String -> IO (Either ParseErrorMessage (File String String String))
parseFile filename = do
  content <- readFile filename
  return $ parse filename content

parseRule :: String -> String -> Either ParseErrorMessage (Rule String String String)
parseRule name s = 
  let p = (do
             alexSetFilename name
             ruleParser)
  in 
  case processParseRes (runAlex s p) of
      Left  l -> Left l
      Right r  -> Right $ renameRule name r

parseRule' :: String -> String -> (RuleOpts String String String -> RuleOpts String String String) -> Either ParseErrorMessage (Rule String String String)
parseRule' name s f_ruleOpts = 
  case parseRule name s of
    Left  l   -> Left l
    Right res -> Right $ res{ ruleOpts = f_ruleOpts defaultRuleOpts }


parseQuery :: String -> Either ParseErrorMessage (Atom String String String)
parseQuery s = 
  let p = (do
             alexSetFilename "query"
             queryParser)
  in 
  processParseRes (runAlex s $ p)
}

