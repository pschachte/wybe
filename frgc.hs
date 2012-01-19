--  File     : frgc.hs
--  Author   : Peter Schachte
--  Origin   : Sun Dec  4 18:39:16 2011
--  Purpose  : Frege compiler main code
--  Copyright: © 2011-2012 Peter Schachte.  All rights reserved.
--

module Main where

import Options
import AST
import Parser
import Scanner
import Normalise
import Types
import System.FilePath (takeBaseName)
import Data.List

main :: IO ()
main = do
    (opts, files) <- handleCmdline
    mapM_ (processFile opts) files

processFile :: Options -> String -> IO ()
processFile opts file = do
  toks <- if file == "-" then inputTokens else fileTokens file
  let modname = if file == "-" then "stdin" else takeBaseName file
  let parseTree = parse toks
  modul <- runCompiler opts parseTree modname Nothing Nothing compiler
  return ()

compiler :: Compiler ()
compiler = do
    optionallyPutStr ((>0) . optVerbosity)
      $ intercalate "\n" . map show . parseTree
    normalise
    optionallyPutStr ((>0) . optVerbosity) (show . modul)
    reportErrors
    return ()
