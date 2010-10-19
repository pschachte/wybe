--  File     : csv.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct  7 21:09:04 2010
--  Purpose  : Parser for Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

import Text.ParserCombinators.Parsec
import Prelude hiding (lookup,catch)

fregeFile = do
  skipSpace
  many fregeItem

skipSpace = skipMany whiteSpace
  
whiteSpace = ignoreSpace <|> comment

ignoreSpace = do
  space
  return ()

comment = do
  char '#'
  manyTill anyChar (try newline)
  return ()

fregeItem = ident

ident = do
  ch1 <- identStartChar
  rest <- many identChar
  skipSpace
  return (ch1:rest)

identStartChar = letter <|> char '_'
identChar = identStartChar <|> digit

parseFrege :: String -> Either ParseError [String]
parseFrege input = parse fregeFile "(unknown)" input

main = do
  file <- getContents
  let output = parseFrege file
  putStrLn $ show output
