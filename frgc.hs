--  File     : frgc.hs
--  Author   : Peter Schachte
--  Origin   : Sun Dec  4 18:39:16 2011
--  Purpose  : Frege compiler main code
--  Copyright: © 2011-2012 Peter Schachte.  All rights reserved.
--

module Main where

import AST
import Parser
import Scanner
import Normalise
import System.Environment
import System.Console.GetOpt
import System.FilePath (takeBaseName)
import Version
import Printout
import Data.List

data Options = Options
 { optVerbosity   :: Int
 , optShowVersion :: Bool
 , optShowHelp    :: Bool
 } deriving Show

defaultOptions    = Options
 { optVerbosity   = 0
 , optShowVersion = False
 , optShowHelp    = False
 }

options :: [OptDescr (Options -> Options)]
options =
 [ Option ['v'] ["verbose"]
     (NoArg (\ opts -> opts { optVerbosity = 1 + optVerbosity opts }))
     "verbose output on stderr"
 , Option ['V'] ["version"]
     (NoArg (\ opts -> opts { optShowVersion = True }))
     "show version number"
 , Option ['h'] ["help"]
     (NoArg (\ opts -> opts { optShowHelp = True }))
     "display this help text and exit"
 ]


header :: String
header = "Usage: frgc [OPTION...] files..."

compilerOpts :: [String] -> IO (Options, [String])
compilerOpts argv = 
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))

main :: IO ()
main = do
  argv <- getArgs
  (opts,files) <- compilerOpts argv
  if optShowHelp opts then
    putStrLn $ usageInfo header options
    else if optShowVersion opts then
           putStrLn $ "frgc " ++ version ++ "\nBuilt " ++ buildDate
         else processFiles opts files

processFiles :: Options -> [String] -> IO ()
processFiles opts [] = return ()
processFiles opts (file:files) = do
  toks <- if file == "-" then inputTokens else fileTokens file
  let modname = if file == "-" then "stdin" else takeBaseName file
  let parseTree = parse toks
  if (optVerbosity opts) > 0 then
    putStrLn $ intercalate "\n" $ map show parseTree
    else return ()
  let (ast,errs) = normalise modname Nothing Nothing parseTree
  mapM putStrLn errs
  if (optVerbosity opts) > 0 then
    putStrLn $ show ast
    else return ()
  processFiles opts files
