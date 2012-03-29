--  File     : Builder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Jan 31 16:37:48 2012
--  Purpose  : 
--  Copyright: © 2012 Peter Schachte.  All rights reserved.
--

-- |Code to oversee the compilation process.
module Builder (buildTargets, compileModule) where

import Options         (Options, verbose, optForce, optForceAll)
import AST
import Parser          (parse)
import Scanner         (inputTokens, fileTokens, Token)
import Normalise       (normalise)
import Types           (typeCheck)
import System.FilePath
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Maybe      (isNothing, fromJust)
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans
import System.Time     (ClockTime)
import System.Directory (getModificationTime, doesFileExist, 
                         getCurrentDirectory, canonicalizePath)
import System.Exit (exitFailure)
import Config


-- |Build the specified targets with the specified options.
buildTargets :: Options -> [FilePath] -> Compiler ()
buildTargets opts targets = do
    mapM_ (buildTarget $ optForce opts || optForceAll opts) targets
    messages <- getCompiler msgs
    (liftIO . putStr) $ intercalate "\n" messages
    errored <- getCompiler errorState
    when errored $ liftIO exitFailure


-- |Build a single target; flag specifies to re-compile even if the 
--  target is up-to-date.
buildTarget :: Bool -> FilePath -> Compiler ()
buildTarget force target = do
    let tType = targetType target
    if tType == UnknownFile
      then error ("Unknown target file type " ++ target)
      else do
        let modname = takeBaseName target
        built <- buildModule force modname (fileObjFile target) 
                (fileSourceFile target)
        if (built==False) 
          then (liftIO . putStrLn) $ "Nothing to be done for " ++ target
          else
            when (tType == ExecutableFile) (buildExecutable target modname)


-- |Compile or load a module dependency.
buildDependency :: ModSpec -> Compiler ()
buildDependency modspec = do
    dir <- getDirectory
    let srcfile = moduleFilePath sourceExtension dir modspec
    let objfile = moduleFilePath objectExtension dir modspec
    let modname = takeBaseName srcfile
    force <- option optForceAll
    buildModule force modname objfile srcfile
    return ()

-- |Compile a single module to an object file.
buildModule :: Bool            -- ^Force compilation of this module
              -> Ident         -- ^Module name
              -> FilePath      -- ^Object file to generate
              -> FilePath      -- ^Source file to compile if necessary
              -> Compiler Bool -- ^Returns whether or not file was
                              --  actually compiled
buildModule force modname objfile srcfile = do
    maybemod <- getLoadedModule [modname]
    case maybemod of
        Just modl -> return False
        Nothing -> do
            exists <- (liftIO . doesFileExist) srcfile
            objExists <- (liftIO . doesFileExist) objfile
            if not exists 
              then
                error ("Source file " ++ srcfile ++ " does not exist")
              else if not objExists || force 
                   then do
                       buildModule' modname objfile srcfile
                       return True
                   else do
                       srcDate <- (liftIO . getModificationTime) srcfile
                       dstDate <- (liftIO . getModificationTime) objfile
                       if srcDate > dstDate
                         then do 
                           buildModule' modname objfile srcfile
                           return True
                         else do
                           loadModule objfile
                           return False

-- |Actually load and compile the module
buildModule' :: Ident -> FilePath -> FilePath -> Compiler ()
buildModule' modname objfile srcfile = do
    tokens <- (liftIO . fileTokens) srcfile
    let parseTree = parse tokens
    let dir = takeDirectory objfile
    compileModule dir [modname] Nothing parseTree
    
-- |Compile a module given the parsed source file contents.
compileModule :: FilePath -> ModSpec -> Maybe [Ident] -> [Item] -> Compiler ()
compileModule dir modspec params parseTree = do
    enterModule dir modspec params
    setUpModule parseTree
    mods <- exitModule
    compile mods

-- |Build executable from object file
--   XXX not yet implemented
buildExecutable :: FilePath -> Ident -> Compiler ()
buildExecutable _ _ =
    error "Can't build executables yet"


-- |Load module export info from compiled file
--   XXX not yet implemented
loadModule :: FilePath -> Compiler ()
loadModule objfile =
    error "Can't handle pre-compiled files yet"


-- |Set up a new module for compilation.  Assumes that a fresh module 
--  has already been entered.  Normalises and installs the given list 
--  of file items, and handles any required imports.
setUpModule :: [Item] -> Compiler ()
setUpModule items = do
    verboseMsg 1 (intercalate "\n" $ List.map show items)
    Normalise.normalise items
    handleImports


-- |Actually compile a list of file items, assuming the Compiler has
--  been set up for the new module.
compile :: [Module] -> Compiler ()
compile mods = do
    verboseMsg 1 (intercalate ("\n" ++ replicate 50 '-' ++ "\n") 
                  (List.map show mods))
--    flowCheck
    typeCheck
    return ()


------------------------ Handling Imports ------------------------

-- |Handle all the imports of the current module.
handleImports :: Compiler ()
handleImports = do
    imports <- getModuleImplementationField (keys . modImports)
    mapM_ buildDependency $ fromJust imports
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
