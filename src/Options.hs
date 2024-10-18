--  File     : Options.hs
--  Author   : Peter Schachte
--  Purpose  : Handle compiler options/switches
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
----------------------------------------------------------------
--                      Compiler Options
----------------------------------------------------------------

-- |The wybe compiler command line options.
module Options (Options(..), 
                LogSelection(..), 
                OptFlag(..),
                optimisationEnabled,
                handleCmdline, 
                defaultOptions) where

import           Data.List             as List
import           Data.List.Extra       (lower)
import           Data.Map              as Map
import           Data.Set              as Set
import           Data.Either           as Either
import           Text.Read             (readMaybe)
import           Control.Monad
import           System.Console.GetOpt
import           System.Environment
import           System.Exit
import           System.FilePath
import           Version
import           System.Directory
import           System.Console.ANSI

-- |Command line options for the wybe compiler.
data Options = Options
    { optForce         :: Bool     -- ^Compile specified files even if up to date
    , optForceAll      :: Bool     -- ^Compile all files even if up to date
    , optShowVersion   :: Bool     -- ^Print compiler version and exit
    , optShowHelp      :: Bool     -- ^Print compiler help and exit
    , optHelpLog       :: Bool     -- ^Print log option help and exit
    , optHelpOpt       :: Bool     -- ^Print optiisation option help and exit
    , optLibDirs       :: [String] -- ^Directories where library files live
    , optLogAspects    :: Set LogSelection
                                   -- ^Which aspects to log
    , optOptimisations :: Set OptFlag
                                   -- ^Enabled optimisations
    , optLLVMOptLevel  :: Word     -- ^LLVM optimisation level
    , optDumpLib       :: Bool     -- ^Also dump wybe.* modules when dumping
    , optVerbose       :: Bool     -- ^Be verbose in compiler output
    , optNoFont        :: Bool     -- ^Disable ISO font change codes in messages
    , optNoVerifyLLVM  :: Bool     -- ^Don't run LLVM verification
    , optErrors        :: Set String 
                                   -- ^Erroneous flag error messages
    } deriving Show


-- |Defaults for all compiler options
defaultOptions :: Options
defaultOptions = Options
  { optForce         = False
  , optForceAll      = False
  , optShowVersion   = False
  , optShowHelp      = False
  , optHelpLog       = False
  , optHelpOpt       = False
  , optLibDirs       = []
  , optLogAspects    = Set.empty
  , optOptimisations = defaultOptFlags
  , optLLVMOptLevel  = 3
  , optDumpLib       = False
  , optVerbose       = False
  , optNoFont        = False
  , optNoVerifyLLVM  = False
  , optErrors        = Set.empty
  }


class (Ord a) => Toggleable a where
    parseFlag :: String -> Either String (Set a -> Set a)

    toggle :: String -> (Options -> Set a) -> (Options -> Set a -> Options)
            -> String -> Options -> Options
    toggle prefix getter setter str opts@Options{optErrors=errors} =
        let strs = separate ',' str
            (unknown, toggles) = partitionEithers $ parseFlag <$> strs
            unknown' = Set.fromList $ (prefix ++) <$> unknown
            opts' = opts{optErrors=errors `Set.union` unknown'}
            flags' = List.foldl (flip (.)) id toggles $ getter opts'
        in setter opts' flags'

-- |All compiler features we may want to log
data LogSelection =
  All | AST | BodyBuilder | Builder | Clause | Expansion | FinalDump
  | Flatten | Normalise | Optimise | Resources | Types
  | Unbranch | LLVM | Emit | Analysis | Transform | Uniqueness
  | LastCallAnalysis
  deriving (Eq, Ord, Bounded, Enum, Show, Read)

instance Toggleable LogSelection where
    parseFlag flag = maybe (Left flag) Right $ optMap Map.!? lower flag
      where
        optMap = Map.fromList 
            $ [(pre ++ lower (show s), mut s)
              | s <- [minBound..maxBound]
              , (pre, mut) <- [ ("", Set.insert)
                              , ("no-", Set.delete) ]]
           ++ [ ("all", const $ Set.fromList [minBound..maxBound])
              , ("no-all", const Set.empty)
              ]

-- | Add log aspects specified by the String to the given options.
-- Adds error messages when the log aspect is unknown
addLogAspects :: String -> Options -> Options
addLogAspects = toggle "unknown log aspect: "
                optLogAspects (\s o -> s{optLogAspects=o})

allLogSelections :: [LogSelection]
allLogSelections = [minBound .. maxBound]

logSelectionDescription :: LogSelection -> String
logSelectionDescription All
    = "Log all aspects of the compilation process"
logSelectionDescription AST
    = "Log operations on the AST or IR"
logSelectionDescription BodyBuilder
    = "Log building up of proc bodies"
logSelectionDescription Builder
    = "Log the build process"
logSelectionDescription Clause
    = "Log generation of clausal form"
logSelectionDescription Expansion
    = "Log inlining and similar optimisations"
logSelectionDescription Flatten
    = "Log flattening of expressions"
logSelectionDescription FinalDump
    = "Log a dump of the final AST produced"
logSelectionDescription Optimise
    = "Log optimisation"
logSelectionDescription Normalise
    = "Log normalised items"
logSelectionDescription Resources
    = "Log handling of resources"
logSelectionDescription Types
    = "Log type checking"
logSelectionDescription Unbranch
    = "Log transformation of loops and selections into clausal form"
logSelectionDescription LLVM
    = "Log generation of LLVM code"
logSelectionDescription Emit
    = "Log emission of LLVM IR from the definitions created"
logSelectionDescription Analysis
    = "Log analysis of LPVM IR"
logSelectionDescription Transform
    = "Log transform of mutate instructions"
logSelectionDescription Uniqueness
    = "Log uniqueness checking"
logSelectionDescription LastCallAnalysis
    = "Log last call analysis"


-- | Enumeration of compiler optimisations
data OptFlag = LLVMOpt | MultiSpecz | TailCallModCons
    deriving (Eq, Ord, Enum, Bounded, Show)

-- | Default optimisations enabled:  all of them
defaultOptFlags :: Set OptFlag
defaultOptFlags = Set.fromList [minBound..maxBound]


instance Toggleable OptFlag where
    parseFlag flag = maybe (Left flag) Right $ optMap Map.!? lower flag
      where
        optMap = Map.fromList [(pre ++ optimisationFlag s, mut s)
                              | s <- [minBound..maxBound]
                              , (pre, mut) <- [ ("", Set.insert)
                                              , ("no-", Set.delete) ]]


-- | Add optimisation flags specified by the String to the given options.
-- Adds error messages when the flag is unknown
addOptFlags :: String -> Options -> Options
addOptFlags = toggle "unknown optimisation flag: "
                optOptimisations (\s o -> s{optOptimisations=o})


-- | Check if a given OptFlag is enabled 
optimisationEnabled :: OptFlag -> Options -> Bool
optimisationEnabled flag Options{optOptimisations=opts} = flag `Set.member` opts


-- | Description of an OptFlag
optimisationFlagDesc :: OptFlag -> String
optimisationFlagDesc flag 
    = desc' ++ 
        " (default: " ++ if optimisationEnabled flag defaultOptions
                         then "enabled)" else "disabled)"
  where 
    desc' = case flag of 
        LLVMOpt         -> "run the LLVM optimisations on the emitted LLVM"
        MultiSpecz      -> "run the multiple specialisation optimisation"
        TailCallModCons -> "run the tail-call-modulo-construction optimisation "


-- | Command line flag for a given OptFlag
optimisationFlag :: OptFlag -> String
optimisationFlag LLVMOpt = "llvm-opt"
optimisationFlag MultiSpecz = "multi-specz"
optimisationFlag TailCallModCons = "tcmc"


-- |Command line option parser and help text
options :: [OptDescr (Options -> Options)]
options =
    [ Option ['f'] ["force"]
        (NoArg (\ opts -> opts { optForce = True }))
        "force compilation of specified files"
    , Option []    ["force-all"]
        (NoArg (\ opts -> opts { optForceAll = True }))
        "force compilation of all dependencies"
    , Option ['L'] ["libdir"]
        (ReqArg (\ d opts -> opts { optLibDirs = optLibDirs opts ++ [d] }) "DIR")
        ("specify a library directory [default $WYBELIBS or " ++ libDir ++ "]")
    , Option ['l'] ["log"]
      (ReqArg addLogAspects "ASPECT")
       "add comma-separated aspects to log, or 'all'"
    , Option ['h'] ["help"]
        (NoArg (\ opts -> opts { optShowHelp = True }))
        "display this help text and exit"
    , Option []    ["log-help"]
        (NoArg (\ opts -> opts { optHelpLog = True }))
        "display help on logging options and exit"
    , Option []    ["opt-help"]
        (NoArg (\ opts -> opts { optHelpOpt = True }))
        "display help on optimisation flags and exit"
    , Option ['V'] ["version"]
        (NoArg (\ opts -> opts { optShowVersion = True }))
        "show version number"
    , Option ['x'] ["opt"]
        (ReqArg addOptFlags "FLAGS")
        "add comma-separated optimisation flags"
    , Option ['O'] ["llvm-opt-level"]
        (ReqArg setLLVMOptLevel "LEVEL")
        "specify the LLVM compiler optimisation level"
    , Option []    ["dump-lib"]
        (NoArg (\opts -> opts { optDumpLib = True }))
        "also dump wybe library when dumping"
    , Option ['v'] ["verbose"]
        (NoArg (\opts -> opts { optVerbose = True }))
        "dump verbose messages after compilation"
    , Option ['n'] ["no-fonts"]
        (NoArg (\opts -> opts { optNoFont = True }))
        "disable font highlighting in messages"
    , Option []    ["no-verify-llvm"]
        (NoArg (\opts -> opts { optNoVerifyLLVM = True }))
        "disable verification of generated LLVM code"
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

-- |Parse the command line and handle all options asking to print
--  something and exit.
handleCmdline :: IO (Options, [String])
handleCmdline = do
    argv <- getArgs
    assocList <- getEnvironment
    let env = Map.fromList assocList
    (opts0,files) <- compilerOpts argv
    let libs0 = case optLibDirs opts0 of
                [] -> maybe [libDir] splitSearchPath $ Map.lookup "WYBELIBS" env
                lst -> lst
    libs <- mapM makeAbsolute libs0
    let opts = opts0 { optLibDirs = libs }
    if optShowHelp opts
    then do
        putStrLn $ usageInfo header options
        exitSuccess
    else if optHelpLog opts 
    then do
        putStrLn "Use the -l or --log option to select logging to stdout.\n\
                 \If an option is prefixed with 'no-', the logging option will not\n\
                 \be applied.\n\
                 \If an option is specified multiple times, only the last applies.\n\
                 \The argument to this option should be a comma-separated\n\
                 \list (with no spaces) of these options:"
        putStr $ formatMapping show logSelectionDescription
        exitSuccess
    else if optHelpOpt opts 
    then do
        putStrLn "Use the --opt option to select applied optimisations.\n\
                 \If a flag is prefixed with 'no-', the optimisation will not\n\
                 \be applied.\n\
                 \If a flag is specified multiple times, only the last applies.\n\
                 \The argument to this option should be a comma-separated\n\
                 \list (with no spaces) of these options:"
        putStr $ formatMapping optimisationFlag optimisationFlagDesc
        exitSuccess
    else if optShowVersion opts
    then do
        putStrLn $ "wybemk " ++ version ++ " (git " ++ gitHash ++ ")"
        putStrLn $ "Built " ++ buildDate
        putStrLn $ "Using library directories:\n    " ++
            intercalate "\n    " (optLibDirs opts)
        exitSuccess
    else let errs = optErrors opts
         in if not $ List.null errs 
    then do
        unless (optNoFont opts) $ setSGR [SetColor Foreground Vivid Red]
        putStrLn $ "Command line option errors:\n  " ++ intercalate "\n  " (Set.toList errs)
        exitFailure
    else if List.null files
    then do
        putStrLn $ usageInfo header options
        exitFailure
    else return (opts,files)
    

-- Set the LLVM optimisation level specified by the string.
-- Add an error message if the string is not a number.
setLLVMOptLevel :: String -> Options -> Options
setLLVMOptLevel str opts@Options{optErrors=errors}=
    case readMaybe str of
        Nothing -> opts{optErrors=("LLVM opt level should be a number: " ++ str) 
                                    `Set.insert` errors}
        Just lvl -> opts{optLLVMOptLevel=lvl}



-- |The inverse of intercalate:  split up a list into sublists separated
--  by the separator list.
separate :: Eq a => a -> [a] -> [[a]]
separate separator [] = [[]]
separate separator (e:es) =
  if e == separator
  then []:separate separator es
  else let (s:ss) = separate separator es
       in  (e:s):ss


-- |Produce a table showing the domain and range of the input function and
formatMapping :: (Bounded a, Enum a, Show a) => (a -> String) -> (a -> String) -> String
formatMapping nameMap descMap =
    let domain = [minBound .. maxBound]
        width = 2 + maximum (List.map (length . show) domain)
    in  unlines $
        [ let t = nameMap elt
          in  replicate (width - length t) ' ' ++ t ++ " : " ++ descMap elt
        | elt <- domain]
