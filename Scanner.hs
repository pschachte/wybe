--  File     : Scanner.hs
--  Author   : Peter Schachte
--  Origin   : Thu Oct 21 17:42:28 2010
--  Purpose  : Scanner for the Wybe language
--  Copyright: (c) 2010-2012 Peter Schachte.  All rights reserved.

-- |The tokeniser for wybe.
module Scanner (Token(..), tokenPosition, floatValue, intValue, stringValue,
                charValue, identName, symbolName, showPosition, 
                StringDelim(..), BracketStyle(..), fileTokens, tokenise,
                inputTokens) where

import AST
import Data.Char
import Data.List
import Text.ParserCombinators.Parsec.Pos

-- |The tokens of the wybe language, each carrying its source position.
data Token = TokFloat Double SourcePos          -- ^A floating point number
              | TokInt Integer SourcePos        -- ^An integer
              | TokString StringDelim String SourcePos
                                                -- ^A string with its delimiter
              | TokChar Char SourcePos          -- ^A character constant
              | TokIdent String SourcePos       -- ^An identifier
              | TokLBracket BracketStyle SourcePos
                                                -- ^Some kind of left bracket
              | TokRBracket BracketStyle SourcePos
                                                -- ^Some kind of right bracket
              | TokComma SourcePos              -- ^A comma
              | TokSymbol String SourcePos      -- ^A symbol of made up of
                                                --  non-identifier chars
              deriving (Show)

-- |Returns the source position of a token.
tokenPosition :: Token -> SourcePos
tokenPosition (TokFloat _     pos) = pos
tokenPosition (TokInt   _     pos) = pos
tokenPosition (TokString _ _  pos) = pos
tokenPosition (TokChar _      pos) = pos
tokenPosition (TokIdent _     pos) = pos
tokenPosition (TokLBracket _  pos) = pos
tokenPosition (TokRBracket _  pos) = pos
tokenPosition (TokComma       pos) = pos
tokenPosition (TokSymbol _    pos) = pos

-- |Returns the value of a float token.
floatValue :: Token -> Double
floatValue (TokFloat float _) = float
floatValue _ = shouldnt "not a float"

-- |Returns the value of an int token.
intValue :: Token -> Integer
intValue (TokInt int _) = int
intValue _ = shouldnt "not an int"

-- |Returns the value of a string token.
stringValue :: Token -> String
stringValue (TokString _ string _) = string
stringValue _ = shouldnt "not a string"

-- |Returns the value of a character constant token.
charValue :: Token -> Char
charValue (TokChar char _) = char
charValue _ = shouldnt "not a char"

-- |Returns the name of an identifier token.
identName :: Token -> String
identName (TokIdent str _) = str
identName _ = shouldnt "not an ident"

-- |Returns the name of a symbol token.
symbolName :: Token -> String
symbolName (TokSymbol str _) = str
symbolName _ = shouldnt "not a symbol"

-- |How to display a source position.
showPosition :: SourcePos -> String
showPosition pos
  = sourceName pos ++ ":" 
    ++ show (sourceLine pos) ++ ":"
    ++ show (sourceColumn pos)

-- |The different string delimiters.
data StringDelim = DoubleQuote | BackQuote | LongQuote String
                 deriving (Show)

-- |The different kinds of brackets.
data BracketStyle = Paren | Bracket | Brace
                  deriving (Show, Eq)


-- |The contents of a file as a list of tokens.
fileTokens :: FilePath -> IO [Token]
fileTokens filename =
  do content <- readFile filename
     return (tokenise (initialPos filename) content)


-- |The contents of stdin as a list of tokens.
inputTokens :: IO [Token]
inputTokens =
  do content <- getContents
     return (tokenise (initialPos "<stdin>") content)


-- |Convert a sequence of characters to a sequence of tokens.
-- XXX Still not handling backslash-delimited strings; still want them?
tokenise :: SourcePos -> String -> [Token]
tokenise _ [] = []
tokenise pos str@(c:cs)
  | isSpace c || isControl c = tokenise (updatePosChar pos c) cs
  | isDigit c = let (tok,rest,newpos) = 
                      scanNumberToken (if c=='0' then 8 else 10)
                      (fromIntegral $ digitToInt c) 
                      (updatePosChar pos c) cs
                in  tok:(tokenise newpos rest)
  | isAlpha c = let (name,rest) = span isIdentChar str
                in  multiCharTok name rest (TokIdent name pos) pos
  | otherwise = case c of
                    ',' -> singleCharTok c cs pos $ TokComma pos
                    '(' -> singleCharTok c cs pos $ TokLBracket Paren pos
                    '[' -> singleCharTok c cs pos $ TokLBracket Bracket pos
                    '{' -> singleCharTok c cs pos $ TokLBracket Brace pos
                    ')' -> singleCharTok c cs pos $ TokRBracket Paren pos
                    ']' -> singleCharTok c cs pos $ TokRBracket Bracket pos
                    '}' -> singleCharTok c cs pos $ TokRBracket Brace pos
                    '\'' -> tokeniseChar pos cs
                    '\"' -> tokeniseString DoubleQuote pos cs
                    -- backquote makes anything an identifier
                    '`' -> let (name,rest) = span (not . (=='`')) str
                           in  multiCharTok name rest (TokIdent name pos) pos
                    '#' -> tokenise (setSourceColumn pos 1)
                           $ dropWhile (not . (=='\n')) cs
                    _   -> tokeniseSymbol pos str

-- |Handle a single character token and tokenize the rest of the input.
singleCharTok :: Char -> String -> SourcePos -> Token -> [Token]
singleCharTok c cs pos tok = tok:(tokenise (updatePosChar pos c) cs)

-- |Handle a mult-character token and tokenize the rest of the input.
multiCharTok :: String -> String -> Token -> SourcePos -> [Token]
multiCharTok str cs tok pos = tok:(tokenise (updatePosString pos str) cs)

-- |Handle a character constant token and tokenize the rest of the input.
tokeniseChar :: SourcePos -> String -> [Token]
tokeniseChar pos ('\\':c:'\'':rest) =
  (TokChar (escapedChar c) pos) :
  tokenise 
  (updatePosChar 
   (updatePosChar (updatePosChar (updatePosChar pos '\'') c) '\\')
   '\'')
  rest
tokeniseChar pos (c:'\'':cs) =
  (TokChar c pos):
  tokenise (updatePosChar (updatePosChar (updatePosChar pos '\'') c) '\'') cs
tokeniseChar pos chars =
    error $ showPosition pos 
    ++ ": Syntax error in single character constant beginning '" 
    ++ take 3 chars ++ "..."

-- |Handle a symbol token and tokenize the rest of the input.
tokeniseSymbol :: SourcePos -> String -> [Token]
tokeniseSymbol pos (c:cs) =
  let (sym,rest) = span isSymbolChar cs
      pos' = updatePosString pos 
  in  multiCharTok (c:sym) rest (TokSymbol (c:sym) pos) pos
tokeniseSymbol _ [] = shouldnt "empty symbol does not exist"

-- |Tokenise a delimited string and tokenize the rest of the input..
-- XXX This doesn't handle escapes within strings
tokeniseString :: StringDelim -> SourcePos -> String -> [Token]
tokeniseString delim pos cs =
  let termchar = delimChar delim
      (str,rest) = span (/= termchar) cs
  in  (TokString delim str pos):
      (if null rest then [] else tokenise (updatePosChar 
                                           (updatePosString
                                            (updatePosChar pos termchar)
                                            str)
                                           termchar) $ tail rest)

-- |Is the specified char the expected final delimiter?
delimChar DoubleQuote = '\"'
delimChar _ = shouldnt "not a delimiter character"

-- |Recognise an escaped character constant.
-- XXX doesn't currently support unicode escapes
escapedChar :: Char -> Char
escapedChar 'a' = '\a'
escapedChar 'b' = '\b'
escapedChar 'f' = '\f'
escapedChar 'n' = '\n'
escapedChar 'r' = '\r'
escapedChar 't' = '\t'
escapedChar 'v' = '\v'
escapedChar c = c

-- |Scan a number token.  Handles decimal and hex ints, floats with
--  decimal point and/or e notation, and ignores embedded underscores.
-- XXX doesn't put position of *start* of number in token.
scanNumberToken :: Integer -> Integer -> SourcePos -> String -> 
                   (Token,String,SourcePos)
scanNumberToken _ n pos "" = (TokInt n pos, "",pos)
scanNumberToken radix n pos str@(c:cs)
  | isHexDigit c && (fromIntegral $ digitToInt c) < radix = 
                scanNumberToken radix 
                (radix*n + (fromIntegral $ digitToInt c)) 
                (updatePosChar pos c) cs
  | (c == 'x' || c == 'X') && n == 0 = scanNumberToken 16 0 
                                       (updatePosChar pos c) cs
  | c == '_' = scanNumberToken radix n (updatePosChar pos c) cs
  | c == '.' && radix == 10 = scanNumberFrac (fromIntegral n) 0.1 
                              (updatePosChar pos c) cs
  | c == 'e' || c == 'E' = scanNumberExponent (fromIntegral n) 
                           (updatePosChar pos c) cs
  | otherwise = (TokInt n pos, str, pos)


-- |Scan the fractional part of a float.
scanNumberFrac :: Double -> Double -> SourcePos -> String -> 
                  (Token,String,SourcePos)
scanNumberFrac n weight pos "" = (TokFloat n pos, "",pos)
scanNumberFrac n weight pos str@(c:cs)
  | '0' <= c && c <= '9' = scanNumberFrac 
                           (n+weight*(fromIntegral $ digitToInt c))
                           (weight * 0.1) (updatePosChar pos c) cs
  | c == 'e' || c == 'E' = scanNumberExponent n (updatePosChar pos c) cs
  | otherwise = (TokFloat n pos, str,pos)


-- |Scan the exponent part of a float.
scanNumberExponent :: Double -> SourcePos -> String -> 
                      (Token,String,SourcePos)
scanNumberExponent n pos cs =
  let (digits,rest) = span isDigit cs
  in (TokFloat (n*10**(fromIntegral $ read digits)) pos, rest,
      updatePosString pos digits)

-- |Is this a character that can appear in an identifier?
isIdentChar :: Char -> Bool
isIdentChar ch = isAlphaNum ch || ch == '_'

-- |Is this a character that can appear in a symbol?
isSymbolChar :: Char -> Bool
isSymbolChar ch = not (isAlphaNum ch || isSpace ch || isControl ch 
                       || ch `elem` ",.([{)]}#'\"\\")
