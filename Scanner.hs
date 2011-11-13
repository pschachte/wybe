--  File     : Scanner.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct 21 17:42:28 2010
--  Purpose  : Scanner for the Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

module Scanner (Token(..), FrgToken(..), StringDelim(..), 
                BracketStyle(..), frgtoken, fileTokens, inputTokens) where

import Data.Char
import Data.List
import Text.ParserCombinators.Parsec.Pos

data Token = Token FrgToken SourcePos
           deriving (Show)

data FrgToken = TokFloat Double
              | TokInt Integer
              | TokString StringDelim String
              | TokIdent String
              | TokLBracket BracketStyle
              | TokRBracket BracketStyle
              | TokComma
              | TokSemicolon
              | TokColon
              | TokSymbol String   -- symbol made of non-identifier characters
              deriving (Show)


frgtoken :: Token -> FrgToken
frgtoken (Token tok _) = tok

data StringDelim = SingleQuote | DoubleQuote | BackQuote | LongQuote String
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
                in  (Token tok pos):(tokenise newpos rest)
  | isAlpha c = let (name,rest) = span isIdentChar str
                in  multiCharTok name rest (TokIdent name) pos
  | otherwise = case c of
                    ',' -> singleCharTok c cs pos TokComma
                    ';' -> singleCharTok c cs pos TokSemicolon
                    ':' -> singleCharTok c cs pos TokColon
                    '(' -> singleCharTok c cs pos $ TokLBracket Paren
                    '[' -> singleCharTok c cs pos $ TokLBracket Bracket
                    '{' -> singleCharTok c cs pos $ TokLBracket Brace
                    ')' -> singleCharTok c cs pos $ TokRBracket Paren
                    ']' -> singleCharTok c cs pos $ TokRBracket Bracket
                    '}' -> singleCharTok c cs pos $ TokRBracket Brace
                    '\'' -> tokeniseString SingleQuote pos cs
                    '\"' -> tokeniseString DoubleQuote pos cs
                    '`' -> tokeniseString BackQuote pos cs
                    '#' -> tokenise (setSourceColumn pos 1)
                           $ dropWhile (not . (=='\n')) cs
                    _   -> let (sym,rest) = span isSymbolChar cs
                               pos' = updatePosString pos 
                           in  multiCharTok (c:sym) rest (TokSymbol $ c:sym) pos

-- XXX Still not handling backslash-delimited strings; still want them?

singleCharTok :: Char -> String -> SourcePos -> FrgToken -> [Token]
singleCharTok c cs pos tok = (Token tok pos):(tokenise (updatePosChar pos c) cs)

multiCharTok :: String -> String -> FrgToken -> SourcePos -> [Token]
multiCharTok str cs tok pos = 
  (Token tok pos):(tokenise (updatePosString pos str) cs)


-- XXX This doesn't handle escapes within strings
tokeniseString :: StringDelim -> SourcePos -> String -> [Token]
tokeniseString delim pos cs =
  let termchar = delimChar delim
      (str,rest) = span (/= termchar) cs
  in  (Token (TokString delim str) pos):
      (if null rest then [] else tokenise (updatePosChar 
                                           (updatePosString
                                            (updatePosChar pos termchar)
                                            str)
                                           termchar) $ tail rest)


delimChar SingleQuote = '\''
delimChar DoubleQuote = '\"'
delimChar BackQuote = '`'


scanNumberToken :: Integer -> Integer -> SourcePos -> String -> 
                   (FrgToken,String,SourcePos)
scanNumberToken _ n pos "" = (TokInt n, "",pos)
scanNumberToken radix n pos str@(c:cs)
  | isHexDigit c && (fromIntegral $ digitToInt c) < radix = 
                scanNumberToken radix 
                (radix*n + (fromIntegral $ digitToInt c)) 
                (updatePosChar pos c) cs
  | (c == 'x' || c == 'X') && n == 0 = scanNumberToken 16 0 
                                       (updatePosChar pos c) cs
  | c == '.' && radix == 10 = scanNumberFrac (fromIntegral n) 0.1 
                              (updatePosChar pos c) cs
  | c == 'e' || c == 'E' = scanNumberExponent (fromIntegral n) 
                           (updatePosChar pos c) cs
  | otherwise = (TokInt n, str, pos)


scanNumberFrac :: Double -> Double -> SourcePos -> String -> 
                  (FrgToken,String,SourcePos)
scanNumberFrac n weight pos "" = (TokFloat n, "",pos)
scanNumberFrac n weight pos str@(c:cs)
  | '0' <= c && c <= '9' = scanNumberFrac 
                           (n+weight*(fromIntegral $ digitToInt c))
                           (weight * 0.1) (updatePosChar pos c) cs
  | c == 'e' || c == 'E' = scanNumberExponent n (updatePosChar pos c) cs
  | otherwise = (TokFloat n, str,pos)


scanNumberExponent :: Double -> SourcePos -> String -> 
                      (FrgToken,String,SourcePos)
scanNumberExponent n pos cs =
  let (digits,rest) = span isDigit cs
  in (TokFloat $ n*10**(fromIntegral $ read digits), rest,
      updatePosString pos digits)

isIdentChar :: Char -> Bool
isIdentChar ch = isAlphaNum ch || ch == '_'

isSymbolChar :: Char -> Bool
isSymbolChar ch = not (isAlphaNum ch || isSpace ch || isControl ch 
                       || ch `elem` ",;.([{)]}#'\"\\")
