--  File     : Options.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Jan 19 17:15:01 2012
--  Purpose  : Handle compiler options/switches
--  Copyright: © 2012 Peter Schachte.  All rights reserved.
--
----------------------------------------------------------------
--                      Compiler Optionsa
----------------------------------------------------------------

module Options (Options(..), handleCmdline) where

import System.Console.GetOpt
import System.Environment
import System.Exit
import Version

data Options = Options{  
    optForce         :: Bool
    , optVerbosity   :: Int
    , optShowVersion :: Bool
    , optShowHelp    :: Bool
    } deriving Show

defaultOptions    = Options
 { optForce       = False
 , optVerbosity   = 0
 , optShowVersion = False
 , optShowHelp    = False
 }

options :: [OptDescr (Options -> Options)]
options =
 [ Option ['f'] ["force"]
     (NoArg (\ opts -> opts { optForce = True }))
   "force compilation even when unnecessary"
 , Option ['v'] ["verbose"]
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

handleCmdline :: IO (Options, [String])
handleCmdline = do
    argv <- getArgs
    (opts,files) <- compilerOpts argv
    if optShowHelp opts then do
        putStrLn $ usageInfo header options
        exitSuccess
      else if optShowVersion opts then do
               putStrLn $ "frgc " ++ version ++ "\nBuilt " ++ buildDate
               exitSuccess
           else return (opts,files)
