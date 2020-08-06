--  File     : Emit.hs
--  Author   : Rishi Ranjan, Modified by Zed(Zijun) Chen.
--  Purpose  : Emit LLVM code
--  Copyright: (c) 2016 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Emit (emitObjectFile, emitBitcodeFile, emitAssemblyFile,
             makeArchive, makeExec,
             logLLVMString
            )
where

import           AST
import           BinaryFactory              (encodeModule)
import           Blocks                     (concatLLVMASTModules)
import           Config
import           Control.Monad
import           Control.Monad.Trans        (liftIO)
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import qualified Data.ByteString            as BS
import qualified Data.ByteString.Char8      as B8
import qualified Data.ByteString.Lazy       as BL
import           Data.List                  as List
import           Data.Map                   as Map
import qualified Data.Text.Lazy             as TL
import           Distribution.System        (buildOS, OS (..)) 
import qualified LLVM.AST                   as LLVMAST
import           LLVM.Context
import           LLVM.Module                as Mod
import           LLVM.PassManager
import           LLVM.Pretty                (ppllvm)
import           LLVM.Target
import           ObjectInterface
import           Options                    (LogSelection (Blocks,Builder,Emit))
import           System.Exit                (ExitCode (..))
import           System.Process



-- | With the LLVM AST representation of a LPVM Module, create a
-- target object file, embedding the 'AST.Module' serialised bytestring
-- into the '__lpvm' section of the Macho-O object file.
emitObjectFile :: ModSpec -> FilePath -> Compiler ()
emitObjectFile m f = do
    logEmit $ "Creating object file for *" ++ showModSpec m ++ "*" ++
        " @ '" ++ f ++ "'"
    -- astMod <- getModule id
    logEmit $ "Encoding and wrapping Module *" ++ showModSpec m
              ++ "* in a wrapped object."
    logEmit $ "Running passmanager on the generated LLVM for *"
              ++ showModSpec m ++ "*."
    -- modBS <- encodeModule astMod
    modBS <- encodeModule m
    llmod <- descendentModuleLLVM m
    makeWrappedObjFile f llmod modBS


-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Bitcode file.
emitBitcodeFile :: ModSpec -> FilePath -> Compiler ()
emitBitcodeFile m f = do
    logEmit $ "Creating wrapped bitcode file for *" ++ showModSpec m ++ "*"
              ++ " @ '" ++ f ++ "'"
    -- astMod <- getModule id
    logEmit $ "Encoding and wrapping Module *" ++ showModSpec m
              ++ "* in a wrapped bitcodefile."
    -- modBS <- encodeModule astMod
    modBS <- encodeModule m
    llmod <- descendentModuleLLVM m
    liftIO $ makeWrappedBCFile f llmod modBS


-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Assembly file.
emitAssemblyFile :: ModSpec -> FilePath -> Compiler ()
emitAssemblyFile m f = do
    logEmit $ "Creating assembly file for " ++ showModSpec m ++
        ", with optimisations."
    llmod <- descendentModuleLLVM m
    liftIO $ withOptimisedModule llmod
        (\mm -> withHostTargetMachineDefault $ \_ ->
            writeLLVMAssemblyToFile (File f) mm)


-- | Concatenate the LLVMAST.Module implementations of the descendents of
-- the given module.
descendentModuleLLVM :: ModSpec -> Compiler LLVMAST.Module
descendentModuleLLVM mspec = do
    someMods <- descendentModules mspec
    unless (List.null someMods) $
        logEmit $ "### Combining descendents of " ++ showModSpec mspec
                   ++ ": " ++ showModSpecs someMods
    concatLLVMASTModules mspec someMods


-- | Handle the ExceptT monad. If there is an error, it is better to fail.
liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

-- | Return string form LLVM IR represenation of a LLVMAST.Module
codeemit :: LLVMAST.Module -> IO BS.ByteString
codeemit llmod = withOptimisedModule llmod moduleLLVMAssembly
-- codeemit llmod = withModule llmod moduleLLVMAssembly


-------------------------------------------------------------------------------
-- Optimisations                                                             --
-------------------------------------------------------------------------------

-- | Setup the set of passes for optimisations.
-- Currently using the curated set provided by LLVM.
passes :: PassSetSpec
passes = defaultCuratedPassSetSpec { optLevel = Just 3 }


-- | Return a string LLVM IR representation of a LLVMAST.Module after
-- a curated set of passes has been executed on the C++ Module form.
codeEmitWithPasses :: LLVMAST.Module -> IO BS.ByteString
codeEmitWithPasses llmod =
    withContext $ \context ->
        withModuleFromAST context llmod $ \m ->
            withPassManager passes $ \pm -> do
                success <- runPassManager pm m
                if success
                    then moduleLLVMAssembly m
                    else error "Running of optimisation passes not successful!"

-- | Testing function to analyse optimisation passes.
testOptimisations :: LLVMAST.Module -> IO ()
testOptimisations llmod = do
    llstr <- codeEmitWithPasses llmod
    putStrLn $ replicate 80 '-'
    putStrLn "Optimisation Passes"
    putStrLn $ replicate 80 '-'
    B8.putStrLn llstr
    putStrLn $ replicate 80 '-'


-- | Using a bracket pattern, perform an action on the C++ Module
-- representation of a LLVMAST.Module after the C++ module has been through
-- a set of curated passes.
withOptimisedModule :: LLVMAST.Module -> (Mod.Module -> IO a)
                    -> IO a
withOptimisedModule llmod action =
    withContext $ \context ->
        withModuleFromAST context llmod $ \m ->
            withPassManager passes $ \pm -> do
                success <- runPassManager pm m
                if success
                    then action m
                    else error "Running of optimisation passes not successful"

-- | Bracket pattern to run an [action] on the [LLVMAST.Module].
withModule :: LLVMAST.Module -> (Mod.Module -> IO a) -> IO a
withModule llmod action =
    withContext $ \context ->
        withModuleFromAST context llmod action



----------------------------------------------------------------------------
-- Target Emitters                                                        --
----------------------------------------------------------------------------

-- | Drop an LLVMAST.Module (haskell) into a LLVM Module.Module (C++),
-- and write it as an object file.
makeObjFile :: FilePath -> LLVMAST.Module -> IO ()
makeObjFile file llmod =
    withHostTargetMachineDefault $ \tm ->
        withOptimisedModule llmod $ \m ->
            writeObjectToFile tm (File file) m

-- | Drop an LLVMAST.Module (haskell) intop a Mod.Module (C++)
-- represenation and write is a bitcode file.
makeBCFile :: FilePath -> LLVMAST.Module -> IO ()
makeBCFile file llmod =
    withContext $ \context ->
        withModuleFromAST context llmod $ \m ->
            writeBitcodeToFile (File file) m


-- | Use the bitcode wrapper structure to wrap both the AST.Module
-- (serialised) and the bitcode generated for the Module
makeWrappedBCFile :: FilePath -> LLVMAST.Module -> BL.ByteString -> IO ()
makeWrappedBCFile file llmod modBS =
    withContext $ \context ->
        withModuleFromAST context llmod $ \m ->
            do bc <- moduleBitcode m
               let wrapped = getWrappedBitcode (BL.fromStrict bc) modBS
               BL.writeFile file wrapped


-- | Drop an LLVMAST.Module (haskell) into a Module.Module (C++),
-- and write it as an object file.
makeAssemblyFile :: FilePath -> LLVMAST.Module -> IO ()
makeAssemblyFile file llmod =
    withContext $ \context ->
        withModuleFromAST context llmod $ \m ->
            withHostTargetMachineDefault $ \_ ->
                writeLLVMAssemblyToFile (File file) m


-- | Create a Macho-O object file and embed a 'AST.Module' bytestring
-- representation into the '__lpvm' section in it.
makeWrappedObjFile :: FilePath -> LLVMAST.Module -> BL.ByteString -> Compiler ()
makeWrappedObjFile file llmod modBS = do
    tmpDir <- gets tmpDir
    result <- liftIO $ withContext $ \_ ->
        withModule llmod $ \m -> do
            withHostTargetMachineDefault $ \tm ->
                writeObjectToFile tm (File file) m
            insertLPVMData tmpDir modBS file
    case result of
        Right () -> return ()
        Left serr -> Error <!> serr



----------------------------------------------------------------------------
-- -- * Linking                                                           --
----------------------------------------------------------------------------
-- * Link time dead code elimination -- More detail can be found here: https://github.com/pschachte/wybe/issues/60
-- There are two goals: (1) remove unused code. (2) remove the lpvm section
-- On macOS (1) (2) are done by using linker arg: `-dead_strip`
-- On Linux (1) is done by using linker arg: `--gc-sections` (requires separate
-- ELF section for each function). (2) is done by calling `objcopy` after the
-- linker build the executable.
-- XXX it's better to use the linker to remove the lpvm section.


-- | Remove OSX Ld warnings of incompatible built object file version.
suppressLdWarnings :: String -> String
suppressLdWarnings s = intercalate "\n" $ List.filter notWarning $ lines s
  where
    notWarning l = not ("ld: warning:" `List.isPrefixOf` l)


-- | With the `ld` linker, link the object files and create target
-- executable.
makeExec :: [FilePath]          -- Object Files
         -> FilePath            -- Target File
         -> Compiler ()
makeExec ofiles target = do
    let options = ["-no-pie"] ++ linkerDeadStripArgs
    let args = options ++ ofiles ++ ["-o", target]
    logEmit $ "Generating final executable with command line: cc "
              ++ unwords args
    (exCode, _, serr) <- liftIO $
        readCreateProcessWithExitCode (proc "cc" args) ""
    case exCode of
        ExitSuccess -> do
            logMsg Blocks $ "--- CC ---\n"
                ++ "$ cc " ++ unwords args
                ++ "\nCC Log:\n" ++ suppressLdWarnings serr
                ++ "\n-------\n"
            result <- liftIO $ removeLPVMSection target
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

-- | Log LLVM IR representation of the given module.
logLLVMString :: ModSpec -> Compiler ()
logLLVMString thisMod =
  do reenterModule thisMod
     maybeLLMod <- getModuleImplementationField modLLVM
     case maybeLLMod of
       (Just llmod) ->
         do let llstr = ppllvm llmod
            logEmit $ replicate 80 '-'
            logEmit $ TL.unpack llstr
            logEmit $ replicate 80 '-'
       Nothing -> error "No LLVM Module Implementation"
     reexitModule
     return ()

-- | Pull the LLVMAST representation of the module and generate the LLVM
-- IR String for it, if it exists.
extractLLVM :: AST.Module -> Compiler BS.ByteString
extractLLVM thisMod =
  case modImplementation thisMod >>= modLLVM of
      Just llmod -> liftIO $ codeemit llmod
      Nothing    -> return $ B8.pack "No LLVM IR generated."

-- | Log the LLVMIR strings for all the modules compiled, except the standard
-- library.
logLLVMDump :: LogSelection -> LogSelection -> String -> Compiler ()
logLLVMDump selector1 selector2 pass =
  whenLogging2 selector1 selector2 $
    do modList <- gets (Map.elems . modules)
       let noLibMod = List.filter ((/="wybe"). List.head . modSpec) modList
       liftIO $ putStrLn $ showModSpecs $ List.map modSpec noLibMod
       llvmir <- mapM extractLLVM noLibMod
       liftIO $ putStrLn $ replicate 70 '=' ++ "\nAFTER " ++ pass ++ ":\n\n" ++
         intercalate ("\n" ++ replicate 50 '-' ++ "\n") (B8.unpack <$> llvmir)
