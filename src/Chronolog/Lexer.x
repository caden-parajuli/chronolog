{
{-# OPTIONS_GHC -Wno-missing-export-lists #-}


module Chronolog.Lexer where

}

%wrapper "monadUserState"

$int       = [0-9]
$lowercase = [a-z]
$uppercase = [A-Z]
$alpha     = [$lowercase$uppercase]
$varchar   = [$int$uppercase\_]
$char      = [$int$alpha\_\']
$empty     = [\ \t\f\v\r\n]
$any       = [. \r \n]

@var             = $varchar$char*
@name            = $lowercase$char*
@quote           = \"$char+\"
@singlecomment   = "%".*\n
@commentstart    = "/*"
@commentend      = "*/"

token :-
  <0>         \,             { mkTokenEmpty Tcomma      }
  <0>         \:\-           { mkTokenEmpty Tif         }
  <0>         \.             { mkTokenEmpty Tperiod     }
  <0>         \(             { mkTokenEmpty Tlparen     }
  <0>         \)             { mkTokenEmpty Trparen     }
  <0>         \[             { mkTokenEmpty Tlbracket   }
  <0>         \]             { mkTokenEmpty Trbracket   }
  <0>         \!             { mkTokenEmpty Tcut        }
  <0>         \^             { mkTokenEmpty Tcut        }
  <0>         \$             { mkTokenEmpty Trequire    }
  <0>         @var           { mkToken Tvar             }
  <0>         @name          { mkToken Tname            }
  <0>         @quote         { mkToken Tquote           }
  <0>         $empty+        { skip'                    }
  <0>         @singlecomment { skip'                    }
  <0,comment> @commentstart  { startComment             }
  <comment>   @commentend    { endComment               }
  <comment>   [.\n]          { skip'                    }


{

data TokenClass =
        Tcomma
      | Tsemicolon
      | Tif
      | Tperiod
      | Tlparen
      | Trparen
      | Tlbracket
      | Trbracket
      | Tcut
      | Tcaret
      | Trequire
      | Tvar    String
      | Tname   String
      | Tquote  String
      | TEOF
      deriving (Eq, Show)

-- filename, position, token itself
data Token = Token String AlexPosn TokenClass
  deriving (Show, Eq)


mkToken :: (String -> TokenClass) -> AlexAction Token
mkToken c (p, _, _, input) len =
  do
    f <- alexGetFilename
    return $ Token f p (c (take len input))

mkTokenEmpty :: TokenClass -> AlexAction Token
mkTokenEmpty c = mkToken (\ _ -> c)



data AlexUserState = AlexUserState {
  filename :: String,
  commentDepth :: Int
} deriving Show

alexInitUserState = AlexUserState {
  filename = "none",
  commentDepth = 0
}

alexSetFilename :: String -> Alex ()
alexSetFilename n =
  do
    st <- alexGetUserState
    alexSetUserState st { filename = n }

alexGetFilename :: Alex String
alexGetFilename =
  do
    st <- alexGetUserState
    return $ filename st

alexEOF :: Alex Token
alexEOF = do
  (p, _, _, _) <- alexGetInput
  f <- alexGetFilename
  return $ Token f p TEOF

isEOF :: Token -> Bool
isEOF (Token _ _ TEOF) = True
isEOF _                = False

skip' _input _len = alexMonadScanErrOffset

alexMonadScanErrOffset = do
  inp <- alexGetInput
  sc  <- alexGetStartCode
  case alexScan inp sc of
    AlexEOF -> alexEOF
    AlexError ((AlexPn off _ _),_,_,_) -> alexError $ "L" ++ show (off + 1)
    AlexSkip  inp' _ -> do
        alexSetInput inp'
        alexMonadScan
    AlexToken inp' len action -> do
        alexSetInput inp'
        action (ignorePendingBytes inp) len

startComment input len = do
  alexSetStartCode comment
  s <- alexGetUserState
  alexSetUserState s { commentDepth = succ (commentDepth s) }
  skip' input len

endComment input len = do
  s <- alexGetUserState
  let depth = commentDepth s
  let newSC = if depth == 1 then 0 else comment
  alexSetStartCode newSC
  alexSetUserState s { commentDepth = depth - 1 }
  skip' input len


lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScanErrOffset >>= f

}

