--  File     : csv.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Oct  7 21:09:04 2010
--  Purpose  : Parser for Frege language
--  Copyright: © 2010 Peter Schachte.  All rights reserved.

module Main (main)  where

import Text.ParserCombinators.Parsec
import Prelude hiding (lookup,catch)
import AST
import Scanner

type FrgParser = GenParser Token ()

-- Top-level file item
data FrgItem = FrgItem Visibility TopItem deriving (Show)

data TopItem = ModuleItem String deriving (Show)


frgtoken :: (FrgToken -> Maybe a) -> FrgParser a
frgtoken test
  = token showToken posToken testToken
  where
    showToken (Token tok pos) = show tok
    posToken  (Token tok pos) = pos
    testToken (Token tok pos) = test tok


identifier :: FrgParser String
identifier 
  = frgtoken (\tok -> case tok of 
                 Ident name -> Just name
                 other      -> Nothing)

keyword :: String -> FrgParser ()
keyword key 
  = frgtoken (\tok -> case tok of 
                 Ident name | name == key -> Just ()
                 other                    -> Nothing)

lparen :: String -> FrgParser ()
lparen key 
  = frgtoken (\tok -> case tok of 
                 LBracket Paren -> Just ()
                 other          -> Nothing)

rparen :: String -> FrgParser ()
rparen key 
  = frgtoken (\tok -> case tok of 
                 RBracket Paren -> Just ()
                 other          -> Nothing)



fregeFile = many fregeItem

fregeItem = 
  do
    vis <- visibility
    keyword "module"
    id <- identifier
    return (FrgItem vis (ModuleItem id))
  

visibility =
  do keyword "pub"
     return Public
  <|>
  return Private


parseFrege :: [Token] -> Either ParseError [FrgItem]
parseFrege input = parse fregeFile "(unknown)" input

main = do
  file <- inputTokens
  let output = parseFrege file
  putStrLn $ show output


compileFile :: FilePath -> IO ()
compileFile filename = do
  file <- fileTokens filename
  let output = parseFrege file
  putStrLn $ show output
