{-|
Module      : NewParser
Description : Re-write of the Wybe parser using Parsec.
Copyright   : (c) Ashutosh Rishi Ranjan, 2016
License     : GPL-3
Maintainer  : ashutoshrishi92@gmail.com
Stability   : experimental
Portability : POSIX

This module defines the new Wybe language parser written using the Haskell
parser combinator library, "Parsec". The grammar here follows the grammar of
the old happy based parser.
-}

module NewParser where

{-
NOTES:
Parser Type : ParsecT [Token] () Identity a
-}

import AST
import Control.Monad.Identity
import Scanner
import Text.Parsec
import Text.Parsec.Expr



-- | Alias for our 'Parsec s u'.
type Parser a = Parsec [Token] () a

-- | Alias for Wybe operator token pareser
type WybeOperator a = Operator [Token] () Identity a

-- | Tabulates the precedence and associativeness of 'WybeOperator's.
type WybeOperatorTable a = [[ WybeOperator a ]]



main :: IO ()
main = do
    let file = "tokentest.wybe"
    stream <- fileTokens file
    -- print stream
    -- putStrLn "--------------------"
    case parse itemParser file stream of
        Left err -> print err
        Right expr -> print expr


-----------------------------------------------------------------------------
-- Grammar                                                                 --
-----------------------------------------------------------------------------

-- | Parser entry for a Wybe program.
itemParser :: Parser (Placed Exp)
itemParser = expParser


-- | Parse expressions.
expParser :: Parser (Placed Exp)
expParser =  ifExpParser
         <|> buildExpressionParser operatorTable simpleExpParser
         <?> "Unexpected Expresion."


-- | Exp -> 'if' Exp 'then' Exp 'else' Exp
ifExpParser :: Parser (Placed Exp)
ifExpParser = do
    pos <- tokenPosition <$> ident "if"
    cond <- expParser
    thenBody <- ident "then" *> expParser
    elseBody <- ident "else" *> expParser
    return $ Placed (CondExp cond thenBody elseBody) pos



-----------------------------------------------------------------------------
-- Arithmetic Expression Parsing                                           --
-----------------------------------------------------------------------------

-- | Parse components of an arithmetic expression.
simpleExpParser :: Parser (Placed Exp)
simpleExpParser =  parenExpParser
               <|> intExp
               <|> floatExp
               <?> "Simple Expression."


-- | Parenthesised expressions.
parenExpParser :: Parser (Placed Exp)
parenExpParser = do
    pos <- tokenPosition <$> leftBracket Paren
    e <- content <$> expParser <* rightBracket Paren
    return $ Placed e pos


-- | Table defining operator precedence and associativeness, helps parsec to
-- deal with expression parsing without ambiguity.
operatorTable :: WybeOperatorTable (Placed Exp)
operatorTable =
    [ [ binary "*"   AssocLeft
      , binary "/"   AssocLeft
      , binary "mod" AssocLeft
      ]
    , [ binary "+" AssocLeft
      , binary "-" AssocLeft
      ]
    , [ binary ">"  AssocLeft
      , binary "<"  AssocLeft
      , binary "<=" AssocLeft
      , binary ">=" AssocLeft
      ]
    , [ binary "/=" AssocNone
      , binary "="  AssocNone
      ]
    , [ prefix "not" ]
    , [ binary "and" AssocLeft ]
    , [ binary "or"  AssocLeft ]
    ]


-- | Helper to make a placed function call expression out of n number of
-- arguments.
makeFnCall :: String -> [Placed Exp] -> Placed Exp
makeFnCall sym args@(x:_) = maybePlace (Fncall [] sym args) (place x)
makeFnCall sym [] = Unplaced (Fncall [] sym [])


-- | Helper to create a binary operator expression parser.
binary :: String -> Assoc -> WybeOperator (Placed Exp)
binary sym = Infix (symOrIdent sym *> return (binFn sym))
  where
    binFn s a b = makeFnCall s [a, b]

-- | Helper to create an unary prefix operator expression parser.
prefix :: String -> WybeOperator (Placed Exp)
prefix sym = Prefix (symOrIdent sym *> return (unFn sym))
  where
    unFn s a = makeFnCall s [a]


-- | Helper to parse a symbol or an identifier as the same semantic token.
symOrIdent :: String -> Parser Token
symOrIdent s = choice [ symbol s, ident s]

-----------------------------------------------------------------------------
-- Terminals                                                               --
-----------------------------------------------------------------------------

-- | Tests an individual token.
takeToken :: (Token -> Maybe a) -> Parser a
takeToken = token show tokenPosition


-- | Parse a float literal token.
floatExp :: Parser (Placed Exp)
floatExp = takeToken test
    where
      test (TokFloat f p) = Just $ Placed (FloatValue f) p
      test _ = Nothing


-- | Parse an integer literal token.
intExp :: Parser (Placed Exp)
intExp = takeToken test
  where
    test (TokInt i p) = Just $ Placed (IntValue i) p
    test _ = Nothing


charExp :: Parser (Placed Exp)
charExp = takeToken test
    where
      test (TokChar c p) = Just $ Placed (CharValue c) p
      test _ = Nothing


-- | Parse a string literal token.
stringExp :: Parser (Placed Exp)
stringExp = takeToken test
  where
    test (TokString _ s p) = Just $ Placed (StringValue s) p
    test _ = Nothing


-- | Parse an identifier token.
identifier :: Parser Token
identifier = takeToken test
  where
    test tok@TokIdent{} = Just tok
    test _ = Nothing


-- | Parse all symbol tokens.
symbolAny :: Parser Token
symbolAny = takeToken test
  where
    test tok@TokSymbol{} = Just tok
    test _ = Nothing


-- | Parse the symbol token of the string 'symbol'.
symbol :: String -> Parser Token
symbol sym = takeToken test
  where
    test tok@(TokSymbol s _) = if sym == s then Just tok else Nothing
    test _ = Nothing


-- | Parse a comma token.
comma :: Parser Token
comma = takeToken test
  where
    test tok@TokComma{} = Just tok
    test _ = Nothing


-- | Parse the keyword terminal 'key', in the form of identifier tokens.
ident :: String -> Parser Token
ident key = takeToken test
  where
    test tok@(TokIdent t _) = if t == key then Just tok else Nothing
    test _ = Nothing


-- | Parse a left bracket of style 'bs'.
leftBracket :: BracketStyle -> Parser Token
leftBracket bs = takeToken test
  where
    test tok@(TokLBracket sty _) = if bs == sty
                                   then Just tok
                                   else Nothing
    test _ = Nothing


-- | Parse a right bracket of style 'bs'.
rightBracket :: BracketStyle -> Parser Token
rightBracket bs = takeToken test
  where
    test tok@(TokRBracket sty _) = if bs == sty
                                  then Just tok
                                  else Nothing
    test _ = Nothing
