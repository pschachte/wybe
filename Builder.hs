--  File     : Builder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Jan 31 16:37:48 2012
--  Purpose  : 
--  Copyright: © 2012 Peter Schachte.  All rights reserved.
--

module Builder (buildTargets, compiler) where

import Options         (Options, optVerbosity, optForce, optForceAll)
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
                         getCurrentDirectory)
import Config

getBuilderField :: (BuilderState -> t) -> Builder t
getBuilderField selector = do
    state <- get
    return $ selector state


updateBuilderField :: (BuilderState -> BuilderState) -> Builder ()
updateBuilderField updater = do
    state <- get
    put $ updater state


getOpt :: (Options -> t) -> Builder t
getOpt opt = do
    opts <- getBuilderField builderOptions
    return $ opt opts


-- Return Just the specified module, if already loaded; else return Nothing
getLoadedModule :: ModSpec -> Builder (Maybe Module)
getLoadedModule modspec = do
    bstate <- get
    return $ Map.lookup modspec (modules bstate)


buildTargets :: Options -> [FilePath] -> IO ()
buildTargets opts targets = do
    execStateT 
      (mapM_ (buildTarget $ optForce opts || optForceAll opts) targets)
      (Builder opts [] False Map.empty 0)
    return ()


buildTarget :: Bool -> FilePath -> Builder ()
buildTarget force target = do
    let tType = targetType target
    if tType == UnknownFile
      then error ("Unknown target file type " ++ target)
      else do
        (modl,built) <- buildModule force (takeBaseName target) 
                       (fileObjFile target) (fileSourceFile target)
        if (built==False) 
          then (liftIO . putStrLn) $ "Nothing to be done for " ++ target
          else
            when (tType == ExecutableFile) (buildExecutable target modl)


buildModule :: Bool -> Ident -> FilePath -> FilePath -> Builder (Module,Bool)
buildModule force modname objfile srcfile = do
    maybemod <- getLoadedModule [modname]
    case maybemod of
        Just modl -> return (modl,False)
        Nothing -> do
            exists <- (liftIO . doesFileExist) srcfile
            objExists <- (liftIO . doesFileExist) objfile
            if not exists 
              then
                error ("Source file " ++ srcfile ++ " does not exist")
              else if not objExists || force 
                   then do
                       modl <- buildModule' modname objfile srcfile
                       return (modl,True)
                   else do
                       srcDate <- (liftIO . getModificationTime) srcfile
                       dstDate <- (liftIO . getModificationTime) objfile
                       if srcDate > dstDate
                         then do 
                           modl <- buildModule' modname objfile srcfile
                           return (modl,True)
                         else do
                           modl <- loadModule objfile
                           return (modl,False)


buildModule' :: Ident -> FilePath -> FilePath -> Builder Module
buildModule' modname objfile srcfile = do
    tokens <- (liftIO . fileTokens) srcfile
    let dir = takeDirectory objfile
    processTokens dir modname tokens


processTokens :: FilePath -> String -> [Token] -> Builder Module
processTokens dir modname tokens = do
    let parseTree = parse tokens
    bldr <- get
    (modl,bldr') <- (liftIO . runCompiler bldr dir modname Nothing Nothing) 
                   (compiler parseTree)
    put bldr'
    return modl
    

-- XXX Build executable from object file
buildExecutable :: FilePath -> Module -> Builder ()
buildExecutable _ _ =
    error "Can't build executables yet"


-- XXX Load module export info from compiled file
loadModule :: FilePath -> Builder Module
loadModule objfile =
    error "Can't handle pre-compiled files yet"


-- getModuleImports :: ModSpec -> Visibility -> Builder Module
-- getModuleImports modspec vis = do
--     dir <- getDirectory
--     file <- (liftIO . moduleFilePath modspec) dir
--     let dir' = takeDirectory file
--     let modname = takeBaseName file
--     tokens <- (liftIO . fileTokens) file
--     let parseTree = parse tokens
--     modul <- compileImport parseTree dir' modname Nothing Nothing vis compiler
--     return $ extractInterface modul


compiler :: [Item] -> Compiler ()
compiler items = do
    optionallyPutStr ((>0) . optVerbosity)
      $ const (intercalate "\n" $ List.map show items)
    Normalise.normalise items
    optionallyPutStr ((>0) . optVerbosity) (show . modul)
--    handleImports
    modname <- getModuleName
--    when (modname /= "") generateInterface 
--    flowCheck
    typeCheck
    reportErrors


moduleFilePath :: ModSpec -> FilePath -> IO FilePath
moduleFilePath spec dir = do
    let file = addExtension (joinPath $ (splitDirectories dir) ++ spec) 
               sourceExtension
    exists <- doesFileExist file
    if exists then return file
      else
        error ("Can't find module " ++ show spec)


------------------------ Filename Handling ------------------------

data TargetType = InterfaceFile | ObjectFile | ExecutableFile | UnknownFile
                deriving (Show,Eq)

targetType :: FilePath -> TargetType
targetType filename
  | ext' == interfaceExtension  = InterfaceFile
  | ext' == objectExtension     = ObjectFile
  | ext' == executableExtension = ExecutableFile
  | otherwise                  = UnknownFile
      where ext' = dropWhile (=='.') $ takeExtension filename

fileObjFile :: FilePath -> FilePath
fileObjFile filename = replaceExtension filename objectExtension

fileSourceFile :: FilePath -> FilePath
fileSourceFile filename = replaceExtension filename sourceExtension