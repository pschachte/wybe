--  File     : Scanner.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct 21 17:42:28 2010
--  Purpose  : Scanner for the Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

module Scanner (Token, tokenise) where

import Data.Char
import Data.List

data Token = Float Double
           | Int Integer
           | String StringDelim String
           | Ident String
           | LBracket BracketStyle
           | RBracket BracketStyle
           | Comma
           | Semicolon
           | Point
           | Symbol String      -- symbol made of non-identifier characters
           deriving (Show)


data StringDelim = SingleQuote | DoubleQuote | BackQuote | LongQuote String
                 deriving (Show)

data BracketStyle = Paren | Bracket | Brace
                  deriving (Show)

tokenise :: String -> [Token]
tokenise [] = []
tokenise str@(c:cs)
  | isSpace c || isControl c = tokenise cs
  | isDigit c = let (tok,rest) = 
                      scanNumberToken (if c=='0' then 8 else 10)
                                      (fromIntegral $ digitToInt c) cs
                in  tok:(tokenise rest)
  | isAlpha c = let (name,rest) = span isIdentChar str
                in  (Ident name):(tokenise rest)
  | otherwise = case c of
                    ',' -> Comma:(tokenise cs)
                    ';' -> Semicolon:(tokenise cs)
                    '.' -> Point:(tokenise cs)
                    '(' -> LBracket Paren:(tokenise cs)
                    '[' -> LBracket Bracket:(tokenise cs)
                    '{' -> LBracket Brace:(tokenise cs)
                    ')' -> RBracket Paren:(tokenise cs)
                    ']' -> RBracket Bracket:(tokenise cs)
                    '}' -> RBracket Brace:(tokenise cs)
                    '\'' -> tokeniseString SingleQuote cs
                    '\"' -> tokeniseString DoubleQuote cs
                    '`' -> tokeniseString BackQuote cs
                    '#' -> tokenise $ dropWhile (not . (=='\n')) cs
                    _   -> let (sym,rest) = span isSymbolChar cs
                           in  (Symbol (c:sym)):(tokenise rest)
-- XXX Still not handling backslash-delimited strings; still want them?


-- XXX This doesn't handle escapes within strings
tokeniseString :: StringDelim -> String -> [Token]
tokeniseString delim cs =
  let (str,rest) = span (/= delimChar delim) cs
  in  (String delim str):(if null rest then [] else tokenise $ tail rest)


delimChar SingleQuote = '\''
delimChar DoubleQuote = '\"'
delimChar BackQuote = '`'


scanNumberToken :: Integer -> Integer -> String -> (Token,String)
scanNumberToken _ n "" = (Int n, "")
scanNumberToken radix n str@(c:cs)
  | isHexDigit c && (fromIntegral $ digitToInt c) < radix = 
                scanNumberToken radix 
                (radix*n + (fromIntegral $ digitToInt c)) cs
  | (c == 'x' || c == 'X') && n == 0 = scanNumberToken 16 0 cs
  | c == '.' && radix == 10 = scanNumberFrac (fromIntegral n) 0.1 cs
  | c == 'e' || c == 'E' = scanNumberExponent (fromIntegral n) cs
  | otherwise = (Int n, str)


scanNumberFrac :: Double -> Double -> String -> (Token,String)
scanNumberFrac n weight "" = (Float n, "")
scanNumberFrac n weight str@(c:cs)
  | '0' <= c && c <= '9' = scanNumberFrac 
                           (n+weight*(fromIntegral $ digitToInt c))
                           (weight * 0.1)               
                           cs
  | c == 'e' || c == 'E' = scanNumberExponent n cs
  | otherwise = (Float n, str)


scanNumberExponent :: Double -> String -> (Token,String)
scanNumberExponent n cs =
  let (digits,rest) = span isDigit cs
  in (Float $ n*10**(fromIntegral $ read digits), rest)

isIdentChar :: Char -> Bool
isIdentChar ch = isAlphaNum ch || ch == '_'

isSymbolChar :: Char -> Bool
isSymbolChar ch = not (isAlphaNum ch || isSpace ch || isControl ch 
                       || ch `elem` ",;.([{)]}#'\"\\")
