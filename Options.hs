--  File     : Options.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Jan 19 17:15:01 2012
--  Purpose  : Handle compiler options/switches
--  Copyright: © 2012 Peter Schachte.  All rights reserved.
--
----------------------------------------------------------------
--                      Compiler Options
----------------------------------------------------------------

-- |The wybe compiler command line options.
module Options (Options(..), handleCmdline, verbose, defaultOptions) where

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.FilePath
import Data.List as List
import Data.List.Split
import Data.Map as Map
import Data.Set as Set
import Version

-- |Command line options for the wybe compiler.
data Options = Options{  
    optForce         :: Bool     -- ^Compile specified files even if up to date
    , optForceAll    :: Bool     -- ^Compile all files even if up to date
    , optVerbosity   :: Int      -- ^How much debugging and progress output
    , optShowVersion :: Bool     -- ^Print compiler version and exit
    , optShowHelp    :: Bool     -- ^Print compiler help and exit
    , optLibDirs     :: [String] -- ^Directories where library files live
    , optLogAspects  :: Maybe (Set String)
                                 -- ^Which aspects to log, Nothing to log all
    } deriving Show

-- |Defaults for all compiler options
defaultOptions    = Options
 { optForce       = False
 , optForceAll    = False
 , optVerbosity   = 0
 , optShowVersion = False
 , optShowHelp    = False
 , optLibDirs     = []
 , optLogAspects  = Just Set.empty
 }

-- |Command line option parser and help text
options :: [OptDescr (Options -> Options)]
options =
 [ Option ['f'] ["force"]
     (NoArg (\ opts -> opts { optForce = True }))
   "force compilation of specified files"
 , Option [] ["force-all"]
     (NoArg (\ opts -> opts { optForceAll = True }))
   "force compilation of all dependencies"
 , Option ['L']     ["libdir"]
   (ReqArg (\ d opts -> opts { optLibDirs = optLibDirs opts ++ [d] }) "DIR")
         "specify a library directory [default $WYBELIBS]"
 , Option ['l']     ["log"]
   (ReqArg (\ a opts -> opts { optLogAspects = addLogRequest
                                               (optLogAspects opts) 
                                               a }) "ASPECT")
         "add comma-separated aspects to log, or 'all'"
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


-- |Help text header string
header :: String
header = "Usage: wybemk [OPTION...] targets..."

-- |Parse command line arguments
compilerOpts :: [String] -> IO (Options, [String])
compilerOpts argv = 
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (List.foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))

-- |Was the specified verbosity level (or greater) specified?
verbose :: Int -> Options -> Bool
verbose n opts = optVerbosity opts >= n

-- |Parse the command line and handle all options asking to print 
--  something and exit.
handleCmdline :: IO (Options, [String])
handleCmdline = do
    argv <- getArgs
    assocList <- getEnvironment
    let env = Map.fromList assocList
    (opts0,files) <- compilerOpts argv
    let opts = if List.null $ optLibDirs opts0
                then maybe (opts0  { optLibDirs = ["."] })
                     (\l -> opts0 { optLibDirs = splitSearchPath l }) $
                     Map.lookup "WYBELIBS" env
                else opts0
    if optShowHelp opts 
      then do
        putStrLn $ usageInfo header options
        exitSuccess
      else if optShowVersion opts 
           then do
               putStrLn $ "wybemk " ++ version ++ "\nBuilt " ++ buildDate
               putStrLn $ "Using " ++ show (length (optLibDirs opts)) ++
                 " library directories:\n    " ++
                 intercalate "\n    " (optLibDirs opts)
               exitSuccess
           else if List.null files 
                then do
                    putStrLn $ usageInfo header options
                    exitFailure
                else do
                    return (opts,files)

-- | Add 
addLogRequest :: Maybe (Set String) -> String -> Maybe (Set String)
addLogRequest Nothing _ = Nothing  -- Nothing means log everything
addLogRequest (Just set) aspectsCommaSep =
  let set' = Set.union set $ Set.fromList $ separate ',' aspectsCommaSep
  in  if Set.member "all" set'
      then Nothing
      else Just set'

-- |The inverse of intercalate:  split up a list into sublists separated 
--  by the separator list.
separate :: Eq a => a -> [a] -> [[a]]
separate separator [] = [[]]
separate separator (e:es) =
  if e == separator
  then []:separate separator es
  else let (s:ss) = separate separator es
       in  (e:s):ss
