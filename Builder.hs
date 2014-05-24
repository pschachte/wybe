--  File     : Builder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Jan 31 16:37:48 2012
--  Purpose  : Handles compilation at the module level.
--  Copyright: © 2012 Peter Schachte.  All rights reserved.
--
--  The wybe compiler handles module dependencies, and builds
--  executables by itself, without the need for build tools like 
--  make.  To keep compile times manageable while supporting 
--  optimisation, we build bottom-up, ensuring that all a module's 
--  imports are compiled before compling the module itself.  In the 
--  case of circular module dependencies, each strongly-connected 
--  component in the module dependency graph is compiled as a unit.
--
--  One shortcoming of the bottom-up approach is that some analyses 
--  are best performed top-down.  For example, we can only eliminate 
--  unneeded procedures when we've seen all the calls to all 
--  procedures in the module.  By compiling bottom-up, we do not have 
--  access to this information.  Our solution to this problem is to 
--  perform the top-down analysis after the bottom-up compilation, 
--  generating results that we can use for the next compilation.  If 
--  the top-down analysis produces results that conflict with the 
--  previous top-down analysis, so that the compilation produced 
--  invalid results, then we must re-compile enough of the program to 
--  fix the problem.  It is hoped that this will happen infrequently 
--  enough that the time saved by not usually having to make separate 
--  traversals for analysis and compilation will more than make up 
--  for the few times we need to recompile.


-- |Code to oversee the compilation process.
module Builder (buildTargets, compileModule) where

import Options         (Options, verbose, optForce, optForceAll, optLibDirs)
import AST
import Parser          (parse)
import Scanner         (inputTokens, fileTokens, Token)
import Normalise       (normalise)
import Types           (typeCheckModSCC)
import Optimise        (optimiseModSCCBottomUp)
import System.FilePath
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Maybe      (isNothing, fromJust, catMaybes)
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans
import System.Time     (ClockTime)
import System.Directory (getModificationTime, doesFileExist, 
                         getCurrentDirectory, canonicalizePath)
import System.Exit (exitFailure, exitSuccess)
import Config


-- |Build the specified targets with the specified options.
buildTargets :: Options -> [FilePath] -> Compiler ()
buildTargets opts targets = do
    mapM_ (buildTarget $ optForce opts || optForceAll opts) targets
    messages <- gets msgs
    (liftIO . putStr) $ unlines messages
    errored <- gets errorState
    verboseDump
    if errored then liftIO exitFailure else liftIO exitSuccess


-- |Build a single target; flag specifies to re-compile even if the 
--  target is up-to-date.
buildTarget :: Bool -> FilePath -> Compiler ()
buildTarget force target = do
    let tType = targetType target
    if tType == UnknownFile
      then message Error ("Unknown target file type " ++ target) Nothing
      else do
        let modname = takeBaseName target
        let dir = takeDirectory target
        built <- buildModuleIfNeeded force [modname] [dir]
        -- XXX prints nothing to be done even when dependencies were built
        -- XXX doesn't build executable even when dependencies were built
        if (built==False) 
          then (liftIO . putStrLn) $ "Nothing to be done for " ++ target
          else
            when (tType == ExecutableFile) (buildExecutable target modname)


-- |Compile or load a module dependency.
buildDependency :: ModSpec -> Compiler ()
buildDependency modspec = do
    force <- option optForceAll
    possDirs <- gets (optLibDirs . options)
    localDir <- getModule modDirectory
    buildModuleIfNeeded force modspec (localDir:possDirs)
    return ()


-- |Compile a single module to an object file.
buildModuleIfNeeded :: Bool    -- ^Force compilation of this module
              -> ModSpec       -- ^Module name
              -> [FilePath]    -- ^Directories to look in
              -> Compiler Bool -- ^Returns whether or not file 
                              -- actually needed to be compiled
buildModuleIfNeeded force modspec possDirs = do
    loading <- gets (List.elem modspec . List.map modSpec . underCompilation)
    if loading
      then return False
      else do
        maybemod <- getLoadedModule modspec
        case maybemod of
            Just modl -> return False -- nothing to do
            Nothing -> do
                srcOb <- srcObjFiles modspec possDirs
                case srcOb of
                    Nothing -> do
                        message Error ("Could not find module " ++ 
                                       showModSpec modspec) Nothing
                        return False
                    Just (_,False,objfile,True,_) -> do 
                        -- only object file exists
                        loadModule objfile
                        return False
                    Just (srcfile,True,objfile,False,modname) -> do 
                        -- only source file exists
                        buildModule modname objfile srcfile
                        return True
                    Just (srcfile,True,objfile,True,modname) -> do
                        srcDate <- (liftIO . getModificationTime) srcfile
                        dstDate <- (liftIO . getModificationTime) objfile
                        if force || srcDate > dstDate
                          then do
                            buildModule modname objfile srcfile
                            return True
                          else
                            return False
                    Just (_,False,_,False,_) ->
                        shouldnt "inconsistent file existence"


-- |Find the source and/or object files for the specified module.  We
-- search the library search path for the files.  
srcObjFiles :: ModSpec -> [FilePath] -> 
               Compiler (Maybe (FilePath,Bool,FilePath,Bool,Ident))
srcObjFiles modspec possDirs = do
    let splits = List.map (flip take modspec) [1..length modspec]
    dirs <- mapM (\d -> do
                       mapM (\ms -> do
                                  let srcfile = moduleFilePath sourceExtension 
                                                d ms
                                  let objfile = moduleFilePath objectExtension 
                                                d ms
                                  let modname = List.last ms
                                  srcExists <- (liftIO . doesFileExist) srcfile
                                  objExists <- (liftIO . doesFileExist) objfile
                                  return $ if srcExists || objExists 
                                           then [(srcfile,srcExists,
                                                  objfile,objExists,modname)]
                                           else [])
                         splits)
            possDirs
    let validDirs = concat $ concat dirs
    if List.null validDirs
      then return Nothing
      else return $ Just $ head validDirs


-- |Actually load and compile the module
buildModule :: Ident -> FilePath -> FilePath -> Compiler ()
buildModule modname objfile srcfile = do
    tokens <- (liftIO . fileTokens) srcfile
    let parseTree = parse tokens
    let dir = takeDirectory objfile
    compileModule dir [modname] Nothing parseTree
    

-- |Compile a module given the parsed source file contents.
compileModule :: FilePath -> ModSpec -> Maybe [Ident] -> [Item] -> Compiler ()
compileModule dir modspec params parseTree = do
    enterModule dir modspec params
    setUpModule parseTree
    underComp <- gets underCompilation
    mods <- exitModule -- may be empty list if module is mutually dependent
    compileModSCC mods


-- |Build executable from object file
--   XXX not yet implemented
buildExecutable :: FilePath -> Ident -> Compiler ()
buildExecutable file _ =
    message Error ("can't build executable " ++ file ++ " yet") Nothing


-- |Load module export info from compiled file
--   XXX not yet implemented
loadModule :: FilePath -> Compiler ()
loadModule objfile =
    message Error ("Can't handle pre-compiled file " ++ objfile ++ " yet") 
    Nothing


-- |Set up a new module for compilation.  Assumes that a fresh module 
--  has already been entered.  Normalises and installs the given list 
--  of file items, and handles any required imports.
setUpModule :: [Item] -> Compiler ()
setUpModule items = do
    -- verboseMsg 1 $ return (intercalate "\n" $ List.map show items)
    -- XXX This means we generate LPVM code for a module before 
    -- considering dependencies.  This will need to change if we 
    -- really need dependency info to do initial LPVM translation, or 
    -- if it's too memory-intensive to load all code to be compiled 
    -- into memory at once.  Note that this does not do a proper 
    -- top-down traversal, because we may not visit *all* users of a 
    -- module before handling the module.  If we decide we need to do 
    -- that, then we'll need to handle the full dependency 
    -- relationship explicitly before doing any compilation.
    Normalise.normalise items
    handleImports


-- |Actually compile a list of modules that form an SCC in the module
--  dependency graph.  This is called in a way that guarantees that
--  all proc calls will be to procs that either have already been
--  compiled or are defined in modules on this list.
compileModSCC :: [ModSpec] -> Compiler ()
compileModSCC specs = do
    -- liftIO $ putStrLn $ "type checking module SCC " ++ showModSpecs specs ++ "..."
    -- liftIO $ putStrLn $ replicate 70 '=' ++ "\nAFTER NORMALISATION:\n"
    -- verboseDump
    typeCheckModSCC specs
    -- liftIO $ putStrLn $ "type checked"
    -- liftIO $ putStrLn $ replicate 70 '=' ++ "\nAFTER TYPE CHECK:\n"
    -- verboseDump
    optimiseModSCCBottomUp specs
    -- liftIO $ putStrLn $ replicate 70 '=' ++ "\nAFTER OPTIMISATION:\n"
    -- verboseDump
    mods <- mapM getLoadedModule specs
    -- callgraph <- mapM (\m -> getSpecModule m
    --                        (Map.toAscList . modProcs . 
    --                         fromJust . modImplementation))
    return ()

---------------------- Resolving Overloading -----------------------

-- resolveOverloading :: ModSpec -> Compiler ()
-- -- resolveOverloading spec = do
-- --     (liftIO . putStrLn) (show spec)
-- --     return ()
-- resolveOverloading spec = do
--     updateModImplementationM
--       (updateModProcsM 
--        (\m -> do
--              processed <- mapM (\(k,p) -> do
--                                     p' <- mapM resolveProc p
--                                     return (k,p'))
--                          (Map.toAscList m)
--              return $ Map.fromAscList processed))

-- resolveProc :: ProcDef -> Compiler ProcDef
-- resolveProc (ProcDef id proto def pos) = do
--     def' <- mapM (updatePlacedM resolvePrim) def
--     return $ ProcDef id proto def' pos

-- resolvePrim :: Prim -> Compiler Prim
-- resolvePrim prim = return prim

---------------------- Purely Local Checks -----------------------

localCheckMod :: ModSpec -> Compiler ()
localCheckMod spec = do
    return ()


------------------------ Handling Imports ------------------------

-- |Handle all the imports of the current module.
handleImports :: Compiler ()
handleImports = do
    imports <- getModuleImplementationField (keys . modImports)
    mapM_ buildDependency imports -- ++ [["wybe"]]
    -- modspec <- getModuleSpec
    -- mod <- getModule id
    -- updateModules (Map.insert modspec mod)

------------------------ Filename Handling ------------------------

-- |The different sorts of files that could be specified on the 
--  command line.
data TargetType = InterfaceFile | ObjectFile | ExecutableFile | UnknownFile
                deriving (Show,Eq)


-- |Given a file specification, return what sort of file it is.  The 
--  file need not exist.
targetType :: FilePath -> TargetType
targetType filename
  | ext' == interfaceExtension  = InterfaceFile
  | ext' == objectExtension     = ObjectFile
  | ext' == executableExtension = ExecutableFile
  | otherwise                  = UnknownFile
      where ext' = dropWhile (=='.') $ takeExtension filename

-- |Given a source or executable file path, return the file path of 
--  the corresponding object file.
fileObjFile :: FilePath -> FilePath
fileObjFile filename = replaceExtension filename objectExtension

-- |Given an object or executable file path, return the file path of 
--  the corresponding source file.
fileSourceFile :: FilePath -> FilePath
fileSourceFile filename = replaceExtension filename sourceExtension

-- |Find the file path for the specified module spec relative to the
--  specified file path for the referencing module.
moduleFilePath :: String -> FilePath -> ModSpec -> FilePath
moduleFilePath extension dir spec = do
    addExtension (joinPath $ (splitDirectories dir) ++ spec) extension
