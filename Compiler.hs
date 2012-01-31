--  File     : Compiler.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Jan 31 16:37:48 2012
--  Purpose  : 
--  Copyright: © 2012 Peter Schachte.  All rights reserved.
--

module Compiler (processFile, getModuleImports, compiler, sourceExtension) where

import Options         (Options, optVerbosity)
import AST             (Compiler, ModuleInterface, ModSpec, Visibility,
                        runCompiler, compileImport, extractInterface,
                        parseTree, modul, getModuleName, optionallyPutStr, 
                        reportErrors, getDirectory)
import Parser          (parse)
import Scanner         (inputTokens, fileTokens, Token)
import Normalise       (normalise)
import Types           (typeCheck)
import System.FilePath (takeBaseName, takeDirectory, splitDirectories, 
                        joinPath, addExtension)
import Data.List       (intercalate)
import Control.Monad   (when)
import Control.Monad.Trans (liftIO)
import System.Time     (ClockTime)
import System.Directory (getModificationTime, doesFileExist, 
                         getCurrentDirectory)


sourceExtension :: String
sourceExtension = "frg"

processFile :: Options -> String -> IO ()
processFile opts file = do
    if file == "-" then do
        tokens <- inputTokens
        dir <- getCurrentDirectory
        processFile' opts dir "stdin" tokens
      else do
        exists <- doesFileExist file
        if exists then do
            tokens <- fileTokens file
            processFile' opts (takeDirectory file) (takeBaseName file) 
              tokens
          else
            error ("Source file " ++ file ++ " does not exist")


processFile' :: Options -> FilePath -> String -> [Token] -> IO ()
processFile' opts dir modname tokens = do
    let parseTree = parse tokens
    modul <- runCompiler opts parseTree dir modname Nothing Nothing compiler
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
    