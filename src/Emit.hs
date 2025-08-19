--  File     : Emit.hs
--  Author   : Rishi Ranjan, Modified by Zed(Zijun) Chen and Peter Schachte.
--  Purpose  : Emit LLVM code
--  Copyright: (c) 2016 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Emit (emitObjectFile, emitBitcodeFile, emitAssemblyFile,
             emitNativeAssemblyFile, makeArchive, makeExec
            )
where

import           AST
import           BinaryFactory              (encodeModule)
import           Config                     (objectExtension, bitcodeExtension,
                                             assemblyExtension,
                                             nativeAssemblyExtension,
                                             linkerDeadStripArgs,
                                             llvmToBitcodeCommand,
                                             llvmToNativeAssemblerCommand,
                                             llvmToObjectCommand,
                                             removeLPVMSection)
import           Control.Monad ( (>=>), unless )
import           Control.Monad.Trans        (liftIO, lift)
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import qualified Data.ByteString            as BS
import qualified Data.ByteString.Char8      as B8
import qualified Data.ByteString.Lazy       as BL
import           Data.List                  as List
import           Data.Map                   as Map
import qualified Data.Text.Lazy             as TL
import           Distribution.System        (buildOS, OS (..))
import           ObjectInterface
import           Options                    (LogSelection (LLVM,Builder,Emit),
                                             Options(..), optNoVerifyLLVM, optLLVMOptLevel,
                                             optimisationEnabled, OptFlag(LLVMOpt))
import qualified Version
import           System.Exit                (ExitCode (..))
import           System.IO                  (openFile, hClose, Handle,
                                             IOMode (WriteMode), hPutStrLn)
import           System.Process             (proc, readCreateProcessWithExitCode)
import           System.FilePath            ((-<.>), takeDirectory)
import           System.Directory           (getPermissions, removeFile)
import           Util                       (createLocalCacheFile, pathIsWriteable)
import           LLVM
import Data.String


-- | With a LPVM Module, create a target object file, including the serialised
-- bytestring of the LPVM module.
emitObjectFile :: ModSpec -> FilePath -> Compiler ()
emitObjectFile m f = do
    let filename = f -<.> Config.objectExtension
    llFilename <- emitAssemblyFile m f
    logEmit $ "===> Producing object file " ++ filename
    userOptions <- gets options
    filename <- do
        writable <- liftIO $ pathIsWriteable filename
        if writable
        then return filename
        else do
            logEmit $ "Do not have write permission on file " ++ filename
                ++ ", use local cache file instead"
            liftIO $ createLocalCacheFile filename
    let (cmd,cmdLine) = llvmToObjectCommand llFilename filename userOptions
    runOSCmd cmd cmdLine
    lift $ removeFile llFilename


-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Bitcode file.
emitBitcodeFile :: ModSpec -> FilePath -> Compiler ()
emitBitcodeFile m f = do
    let filename = f -<.> Config.bitcodeExtension
    llFilename <- emitAssemblyFile m f
    -- astMod <- getModule id
    logEmit $ "===> Producing bitcode file " ++ filename
    userOptions <- gets options
    let (cmd,cmdLine) = llvmToBitcodeCommand llFilename filename userOptions
    runOSCmd cmd cmdLine
    lift $ removeFile llFilename


-- | Create a target LLVM Assembly (.ll) file.  This function forms the basis
-- for all LLVM code generation.
emitAssemblyFile :: ModSpec -> FilePath -> Compiler FilePath
emitAssemblyFile m f = do
    let filename = f -<.> Config.assemblyExtension
    logEmit $ "Creating assembly file for " ++ showModSpec m ++
        ", with optimisations."
    logEmit $ "===> Writing LLVM assembly file " ++ filename
    opts <- gets options
    handle <- liftIO $ openFile filename WriteMode
    writeLLVM handle m True True
    liftIO $ hClose handle
    return filename


-- | With the LLVM AST representation of a LPVM Module, create a target native
-- assembly language file.
emitNativeAssemblyFile :: ModSpec -> FilePath -> Compiler ()
emitNativeAssemblyFile m f = do
    let filename = f -<.> Config.nativeAssemblyExtension
    llFilename <- emitAssemblyFile m f
    -- astMod <- getModule id
    logEmit $ "===> Producing bitcode file " ++ filename
    userOptions <- gets options
    let (cmd,cmdLine) =
            llvmToNativeAssemblerCommand llFilename filename userOptions
    runOSCmd cmd cmdLine
    lift $ removeFile llFilename


-- | Compile the specified .ll file to the specified output file, using the
-- the configured LLVM assembler with the specified switches.
runOSCmd :: String          -- OS command to run
         -> [String]        -- commandline arguments
         -> Compiler ()
runOSCmd cmd cmdLine = do
    logEmit $ "Running command: " ++ cmd ++ concatMap (" "++) cmdLine
    (exCode, _, serr) <- liftIO $
        readCreateProcessWithExitCode (proc cmd cmdLine) ""
    case exCode of
        ExitSuccess -> do
            logEmit $ "completed successfully"
                ++ "\nstderr:\n" ++ serr
                ++ "\n-------\n"
        _ -> Error <!> serr


-- | Handle the ExceptT monad. If there is an error, it is better to fail.
liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return


-------------------------------------------------------------------------------
-- Optimisations                                                             --
-------------------------------------------------------------------------------

-- | Setup the set of passes for optimisations.
-- Currently using the curated set provided by LLVM.
passes :: Word -> [String]
passes lvl = ["-O" ++ show lvl]



----------------------------------------------------------------------------
-- -- * Linking                                                           --
----------------------------------------------------------------------------
-- * Link time dead code elimination -- More detail can be found here:
-- https://github.com/pschachte/wybe/issues/60 There are two goals: (1) remove
-- unused code. (2) remove the lpvm section.  On macOS, (1) (2) are done by
-- using linker arg: `-dead_strip`.  On Linux, (1) is done by using linker arg:
-- `--gc-sections` (requires separate ELF section for each function). (2) is
-- done by calling `objcopy` after the linker build the executable.
-- XXX it's better to use the linker to remove the lpvm section.


-- | Remove OSX Ld warnings of incompatible built object file version.
suppressLdWarnings :: String -> String
suppressLdWarnings s = intercalate "\n" $ List.filter notWarning $ lines s
  where
    notWarning l = not ("ld: warning:" `List.isPrefixOf` l)


-- | Using `cc` as a linker, link the object files and create target executable.
makeExec :: [FilePath]          -- Object Files
         -> FilePath            -- Target File
         -> Compiler ()
makeExec ofiles target = do
    let options = "-no-pie" : Config.linkerDeadStripArgs
    -- let options = linkerDeadStripArgs
    let args = List.filter (not . List.null) 
             $ options ++ ofiles ++ ["-o", target]
    logEmit $ "Generating final executable with command line: cc "
              ++ unwords args
    (exCode, _, serr) <- liftIO $
        readCreateProcessWithExitCode (proc "cc" args) ""
    case exCode of
        ExitSuccess -> do
            logMsg LLVM $ "--- CC ---\n"
                ++ "$ cc " ++ unwords args
                ++ "\nCC Log:\n" ++ suppressLdWarnings serr
                ++ "\n-------\n"
            result <- liftIO $ Config.removeLPVMSection target
            case result of
                Right ()  -> return ()
                Left serr -> Error <!> serr
        _ -> Error <!> serr


-- | Use `ar' system util to link object files into an archive file.
makeArchive :: [FilePath] -> FilePath -> Compiler ()
makeArchive ofiles target = do
    logMsg Builder $ "Building Archive: " ++ target ++ " with: "
        ++ show ofiles
    let args = ["rvs", target] ++ ofiles
    (exCode, _, serr) <- liftIO $
        readCreateProcessWithExitCode (proc "ar" args) ""
    case exCode of
        ExitSuccess ->
            logMsg Builder $ "--- AR Util ---\n"
                ++ "$ ar " ++ unwords args
                ++ "\nAR Log:\n" ++ suppressLdWarnings serr
                ++ "\n-------\n"
        _ -> Error <!> serr

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

logEmit :: String -> Compiler ()
logEmit = logMsg Emit
