--  File     : Scanner.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct 21 17:42:28 2010
--  Purpose  : Scanner for the Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

module Scanner (Token(..), tokenPosition, identName, showPosition, 
                StringDelim(..), BracketStyle(..), fileTokens, 
                inputTokens) where

import Data.Char
import Data.List
import Text.ParserCombinators.Parsec.Pos

data Token = TokFloat Double SourcePos
              | TokInt Integer SourcePos
              | TokString StringDelim String SourcePos
              | TokChar Char SourcePos
              | TokIdent String SourcePos
              | TokLBracket BracketStyle SourcePos
              | TokRBracket BracketStyle SourcePos
              | TokComma SourcePos
              | TokSemicolon SourcePos
              | TokColon SourcePos
              | TokSymbol String SourcePos  -- symbol of non-identifier chars
              deriving (Show)

tokenPosition :: Token -> SourcePos
tokenPosition (TokFloat _     pos) = pos
tokenPosition (TokInt   _     pos) = pos
tokenPosition (TokString _ _  pos) = pos
tokenPosition (TokChar _      pos) = pos
tokenPosition (TokIdent _     pos) = pos
tokenPosition (TokLBracket _  pos) = pos
tokenPosition (TokRBracket _  pos) = pos
tokenPosition (TokComma       pos) = pos
tokenPosition (TokSemicolon   pos) = pos
tokenPosition (TokColon       pos) = pos
tokenPosition (TokSymbol _    pos) = pos

identName :: Token -> String
identName (TokIdent str _) = str


showPosition :: SourcePos -> String
showPosition pos
  = sourceName pos ++ ":" 
    ++ show (sourceLine pos) ++ ":"
    ++ show (sourceColumn pos)

data StringDelim = DoubleQuote | BackQuote | LongQuote String
                 deriving (Show)

data BracketStyle = Paren | Bracket | Brace
                  deriving (Show)


fileTokens :: FilePath -> IO [Token]
fileTokens filename =
  do content <- readFile filename
     return (tokenise (initialPos filename) content)


inputTokens :: IO [Token]
inputTokens =
  do content <- getContents
     return (tokenise (initialPos "") content)


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
                    ';' -> singleCharTok c cs pos $ TokSemicolon pos
                    ':' -> singleCharTok c cs pos $ TokColon pos
                    '(' -> singleCharTok c cs pos $ TokLBracket Paren pos
                    '[' -> singleCharTok c cs pos $ TokLBracket Bracket pos
                    '{' -> singleCharTok c cs pos $ TokLBracket Brace pos
                    ')' -> singleCharTok c cs pos $ TokRBracket Paren pos
                    ']' -> singleCharTok c cs pos $ TokRBracket Bracket pos
                    '}' -> singleCharTok c cs pos $ TokRBracket Brace pos
                    '\'' -> tokeniseChar pos cs
                    '\"' -> tokeniseString DoubleQuote pos cs
                    '`' -> tokeniseString BackQuote pos cs
                    '#' -> tokenise (setSourceColumn pos 1)
                           $ dropWhile (not . (=='\n')) cs
                    _   -> tokeniseSymbol pos str

-- XXX Still not handling backslash-delimited strings; still want them?

singleCharTok :: Char -> String -> SourcePos -> Token -> [Token]
singleCharTok c cs pos tok = tok:(tokenise (updatePosChar pos c) cs)

multiCharTok :: String -> String -> Token -> SourcePos -> [Token]
multiCharTok str cs tok pos = tok:(tokenise (updatePosString pos str) cs)


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


delimChar DoubleQuote = '\"'
delimChar BackQuote = '`'


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

escapedChar :: Char -> Char
escapedChar 'a' = '\a'
escapedChar 'b' = '\b'
escapedChar 'f' = '\f'
escapedChar 'n' = '\n'
escapedChar 'r' = '\r'
escapedChar 't' = '\t'
escapedChar 'v' = '\v'
escapedChar c = c
-- XXX must support hex unicode escapes

-- XXX doesn't put position of *start* of number in token
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


scanNumberFrac :: Double -> Double -> SourcePos -> String -> 
                  (Token,String,SourcePos)
scanNumberFrac n weight pos "" = (TokFloat n pos, "",pos)
scanNumberFrac n weight pos str@(c:cs)
  | '0' <= c && c <= '9' = scanNumberFrac 
                           (n+weight*(fromIntegral $ digitToInt c))
                           (weight * 0.1) (updatePosChar pos c) cs
  | c == 'e' || c == 'E' = scanNumberExponent n (updatePosChar pos c) cs
  | otherwise = (TokFloat n pos, str,pos)


scanNumberExponent :: Double -> SourcePos -> String -> 
                      (Token,String,SourcePos)
scanNumberExponent n pos cs =
  let (digits,rest) = span isDigit cs
  in (TokFloat (n*10**(fromIntegral $ read digits)) pos, rest,
      updatePosString pos digits)


tokeniseSymbol pos (c:cs) =
  let (sym,rest) = span isSymbolChar cs
      pos' = updatePosString pos 
  in  multiCharTok (c:sym) rest (TokSymbol (c:sym) pos) pos

isIdentChar :: Char -> Bool
isIdentChar ch = isAlphaNum ch || ch == '_'

isSymbolChar :: Char -> Bool
isSymbolChar ch = not (isAlphaNum ch || isSpace ch || isControl ch 
                       || ch `elem` ",;.([{)]}#'\"\\")
