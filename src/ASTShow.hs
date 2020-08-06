--  File     : AST.hs
--  Author   : Peter Schachte
--  Purpose  : Show Wybe intermediate representation
--  Copyright: (c) 2010-2019 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module ASTShow (
  logDump
  ) where

import AST
import Options (LogSelection)
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
            maybeimpl = modImplementation mod
        in " Module " ++ showModSpec (modSpec mod) ++
           maybeShow "(" (modParams mod) ")" ++
           "\n  public submods  : " ++ showMapPoses (pubDependencies int) ++
           "\n  public types    : " ++ showMapLines (pubTypes int) ++
           "\n  public resources: " ++ showMapLines (pubResources int) ++
           "\n  public procs    : " ++
           intercalate "\n                    "
           (List.map show $ Set.toList $ Set.unions $
            List.map Map.keysSet $ Map.elems $ pubProcs int) ++
           if isNothing maybeimpl then "\n  implementation not available"
           else let impl = fromJust maybeimpl
                    indent = replicate 20 ' '
                in
                 "\n  imports         : " ++
                 intercalate "\n                    "
                 [showUse 20 mod dep |
                  (mod,(dep,_)) <- Map.assocs $ modImports impl] ++
                 -- "\n  vis types       : " ++
                 -- (fillLines indent 20 80 $
                 --  showSetMapItems $ modKnownTypes impl) ++
                 -- "\n  vis resources   : " ++
                 -- (fillLines indent 20 80 $
                 --  showSetMapItems $ modKnownResources impl) ++
                 -- "\n  vis procs       : " ++
                 -- (fillLines indent 20 80 $
                 --  showSetMapItems $ modKnownProcs impl) ++
                 "\n  types           : " ++ showMapTypes (modTypes impl) ++
                 "\n  resources       : " ++ showMapLines (modResources impl) ++
                 (if Map.null (modSubmods impl)
                  then ""
                  else "\n  submodules      : " ++
                       showMap ", " (const "") showModSpec (modSubmods impl)) ++
                 "\n  procs           : " ++ "\n" ++
                 (showMap "\n\n" (const "") (showProcDefs 0)
                  (modProcs impl)) ++
                 (maybe "\n\nLLVM code       : None\n"
                  (("\n\n  LLVM code       :\n\n" ++) . TL.unpack . ppllvm)
                  $ modLLVM impl)


-- |How to show a map, one line per item.
showMapLines :: Show v => Map Ident v -> String
showMapLines = showMap "\n                    " (++": ") show

showSetMapItems :: (Show b, Ord b) => (Map a (Set b)) -> String
showSetMapItems setMap =
    intercalate ", " $
    List.map show $ Set.toList $
    List.foldr Set.union Set.empty $ Map.elems setMap


-- |How to show a map, items separated by commas.
showMapTypes :: Map Ident TypeDef -> String
showMapTypes = showMap ", " (++ "/") show

-- |How to show a map to source positions, one line per item.
showMapPoses :: Map Ident OptPos -> String
showMapPoses = showMap ", " id showMaybeSourcePos

-- |How to show a map from identifiers to values, given a separator
--  for items, and a separator for keys from values, and a function
--  to show the values.
showMap :: String -> (k -> String) -> (v -> String) -> Map k v -> String
showMap outersep keyFn valFn m =
    intercalate outersep $ List.map (\(k,v) -> keyFn k ++ valFn v) $
    Map.assocs m


-- |Dump the content of the specified module and all submodules if either
-- of the specified log selectors have been selected for logging.  This
-- is called between the passes of those two selectors.
logDump :: LogSelection -> LogSelection -> String -> Compiler ()
logDump selector1 selector2 pass =
    whenLogging2 selector1 selector2 $ do
      modList <- gets (Map.elems . modules)
      let toLog mod = let spec  = modSpec mod
                      in  List.null spec || head spec /= "wybe"
      liftIO $ hPutStrLn stderr $ replicate 70 '='
        ++ "\nAFTER " ++ pass ++ ":\n"
        ++ intercalate ("\n" ++ replicate 50 '-' ++ "\n")
        (List.map show $ List.filter toLog modList)
