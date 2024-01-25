--  File     : AST.hs
--  Author   : Peter Schachte
--  Purpose  : Show Wybe intermediate representation
--  Copyright: (c) 2010-2019 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module ASTShow (
  logDump, logDumpWith
  ) where

import AST
import Options (optDumpLib, LogSelection)
import UnivSet (showSet)
import Data.List as List
import Data.Set  as Set
import Data.Map  as Map
import Data.Maybe
-- import Control.Monad
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.Trans.State
import System.IO
import LLVM.Pretty (ppllvm)
import qualified Data.Text.Lazy as TL


-- |How to show a module.
instance Show Module where
    show mod =
        let int  = modInterface mod
            typeMods = typeModifiers int
            maybeimpl = modImplementation mod
        in " Module " ++ showModSpec (modSpec mod) ++
           bracketList "(" ", " ")" (show <$> modParams mod) ++
           (if typeMods == defaultTypeModifiers
               then ""
               else "\n modifiers       : " ++ (show $ typeModifiers int)) ++
           "\n  representation  : " ++
           (if modIsType mod
            then maybe "(not yet known)" show (modTypeRep mod)
            else "(not a type)") ++
           "\n  public submods  : " ++
           showMap "" "\n                    " "" (++ " -> ")
                   showModSpec (pubSubmods int) ++
           "\n  public resources: " ++ showMapLines show (pubResources int) ++
           "\n  public procs    : " ++
           intercalate "\n                    "
           (List.map show $ Set.toList $ Set.unions $
            List.map Map.keysSet $ Map.elems $ pubProcs int) ++
           if isNothing maybeimpl then "\n  implementation not available"
           else let impl = fromJust maybeimpl
                in
                 "\n  imports         : " ++
                 intercalate "\n                    "
                 [showUse 20 mod dep |
                  (mod,(dep,_)) <- Map.assocs $ modImports impl] ++
                 -- Keep this around in case it's needed again:
                --  "\n  types           : " ++
                --  showMapLines (showSet showModSpec) (modKnownTypes impl) ++
                 "\n  resources       : " ++
                 showMapLines show (modResources impl) ++
                 (if Map.null (modSubmods impl)
                  then ""
                  else "\n  submodules      : " ++
                       showMap "" ", " "" (const "") showModSpec
                       (modSubmods impl)) ++
                 "\n  procs           : " ++ "\n" ++
                 (showMap "" "\n\n" "" (const "") (showProcDefs 0)
                  (modProcs impl)) ++
                 (maybe "\n\nLLVM code       : None\n"
                  (("\n\n  LLVM code       :\n\n" ++) . TL.unpack . ppllvm)
                  $ modLLVM impl)


-- |How to show a map, one line per item.
showMapLines :: (v -> String) -> Map Ident v -> String
showMapLines = showMap "" "\n                    " "" (++": ")


-- |How to show a map to source positions, one line per item.
showMapPoses :: Map Ident OptPos -> String
showMapPoses = showMap "" ", " "" id showOptPos


-- |Dump the content of the specified module and all submodules if either
-- of the specified log selectors have been selected for logging.  This
-- is called between the passes of those two selectors.
logDump :: LogSelection -> LogSelection -> String -> Compiler ()
logDump = logDumpWith (const $ return Nothing)


-- |Dump the content of the specified module and all submodules, with the
-- result of an optional action applied to each module if either of the
-- specified log selectors have been selected for logging.  This is called
-- between the passes of those two selectors.
logDumpWith :: (Module -> Compiler (Maybe String))
            -> LogSelection -> LogSelection -> String -> Compiler ()
logDumpWith action selector1 selector2 pass =
    whenLogging2 selector1 selector2 $ do
        modList <- gets (Map.elems . modules)
        dumpLib <- gets (optDumpLib . options)
        let toLog mod = let spec  = modSpec mod
                        in  List.null spec || dumpLib || head spec /= "wybe"
        let logging = List.filter toLog modList
        mbStrs <- mapM action logging
        liftIO $ hPutStrLn stderr $ replicate 70 '='
          ++ "\nAFTER " ++ pass ++ ":\n"
          ++ intercalate ("\n" ++ replicate 50 '-' ++ "\n")
          (zipWith (\mod mbStr -> show mod ++ maybe "" ("\n\n" ++) mbStr)
              logging mbStrs)
