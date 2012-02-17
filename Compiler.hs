--  File     : Compiler.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Jan 31 16:37:48 2012
--  Purpose  : 
--  Copyright: © 2012 Peter Schachte.  All rights reserved.
--

module Compiler (makeTarget, getModuleImports, compiler, sourceExtension) where

import Options         (Options, optVerbosity, optForce, optForceAll)
import AST             (Compiler, ModuleInterface, ModSpec, Visibility,
                        TargetType(..), targetType,
                        runCompiler, compileImport, extractInterface,
                        parseTree, modul, getModuleName, optionallyPutStr, 
                        reportErrors, getDirectory)
import Parser          (parse)
import Scanner         (inputTokens, fileTokens, Token)
import Normalise       (normalise)
import Types           (typeCheck)
import System.FilePath (splitExtension, splitDirectories, takeBaseName,
                        takeDirectory, joinPath, addExtension)
import Data.List       (intercalate)
import Data.Maybe      (isNothing, fromJust)
import Control.Monad   (when)
import Control.Monad.Trans (liftIO)
import System.Time     (ClockTime)
import System.Directory (getModificationTime, doesFileExist, 
                         getCurrentDirectory)
import Config

makeTarget :: Options -> String -> IO ()
makeTarget opts target = do
    if target == "-" then do
        tokens <- inputTokens
        dir <- getCurrentDirectory
        processFile' opts dir "stdin" tokens Object
      else do
        let (base,ext) = splitExtension target
        let source = addExtension base sourceExtension
        let tType' = targetType ext
        exists <- doesFileExist source
        if not exists then
            error ("Source file " ++ source ++ " does not exist")
          else 
            if isNothing tType' then
                error ("Unknown target file type " ++ target)
            else do
                let tType = fromJust tType'
                let dir = takeDirectory base
                let modname = takeBaseName base
                targetExists <- doesFileExist target
                if not targetExists || optForce opts || optForceAll opts then do
                    tokens <- fileTokens source
                    processFile' opts dir modname tokens tType
                  else do
                    srcDate <- getModificationTime source
                    dstDate <- getModificationTime target
                    if srcDate > dstDate then do
                        tokens <- fileTokens source
                        processFile' opts dir modname tokens tType
                      else
                        putStrLn $ "Nothing to be done for " ++ target
    

processFile' :: Options -> FilePath -> String -> [Token] -> TargetType -> IO ()
processFile' opts dir modname tokens tType = do
    let parseTree = parse tokens
    modul <- runCompiler opts parseTree dir modname Nothing Nothing tType 
            compiler
    return ()


getModuleImports :: ModSpec -> Visibility -> Compiler ModuleInterface
getModuleImports modspec vis = do
    dir <- getDirectory
    file <- (liftIO . moduleFilePath modspec) dir
    let dir' = takeDirectory file
    let modname = takeBaseName file
    tokens <- (liftIO . fileTokens) file
    let parseTree = parse tokens
    modul <- compileImport parseTree dir' modname Nothing Nothing vis compiler
    return $ extractInterface modul


compiler :: Compiler ()
compiler = do
    optionallyPutStr ((>0) . optVerbosity)
      $ intercalate "\n" . map show . parseTree
    normalise
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
    