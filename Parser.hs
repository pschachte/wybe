--  File     : csv.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct  7 21:09:04 2010
--  Purpose  : Parser for Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

import Text.ParserCombinators.Parsec
import Prelude hiding (lookup,catch)
import Data.Char (isSpace, isDigit, digitToInt)
import Data.List (mapAccumL)
import Data.Map (Map, empty, insert, lookup, (!), fromList)
import Control.Monad.State
import Control.Exception ()

csvFile = endBy line eol
line = sepBy cell (char ',')
cell = many (noneOf ",\n\r")

eol =   try (string "\n\r")
    <|> try (string "\r\n")
    <|> string "\n"
    <|> string "\r"

parseCSV :: String -> Either ParseError [[String]]
parseCSV input = parse csvFile "(unknown)" input

main = do
  file <- getContents
  let output = parseCSV file
  putStrLn $ show output
