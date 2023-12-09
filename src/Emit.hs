--  File     : Emit.hs
--  Author   : Rishi Ranjan, Modified by Zed(Zijun) Chen.
--  Purpose  : Emit LLVM code
--  Copyright: (c) 2016 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Emit (emitObjectFile, emitBitcodeFile, emitAssemblyFile,
             makeArchive, makeExec,
             logLLVMString, extractLLVM
            )
where

import           AST
import           BinaryFactory              (encodeModule)
import           Blocks                     (concatLLVMASTModules)
import           Config
import Control.Monad ( (>=>), unless )
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
import           LLVM.Analysis              (verify)
import           ObjectInterface
import           Options                    (LogSelection (Blocks,Builder,Emit),
                                             Options(..), optNoVerifyLLVM, optLLVMOptLevel,
                                             optimisationEnabled, OptFlag(LLVMOpt))
import           System.Exit                (ExitCode (..))
import           System.Process
import           System.FilePath            ((-<.>))
import           System.Directory           (getPermissions, writable, doesFileExist)
import           Util                       (createLocalCacheFile)
import LLVM.AST (Module(moduleDefinitions), Definition (GlobalDefinition), Type (ArrayType, IntegerType))
import LLVM.AST.Global
import qualified LLVM.AST.Global as G
import qualified LLVM.AST.Constant as C
import Data.String
import Config (lpvmSectionName)


-- This does not check the permission if the file does not exists.
-- It is fine for our current usage, but we should improve it.
_haveWritePermission :: FilePath -> IO Bool
_haveWritePermission file = do
    exists <- doesFileExist file
    if exists
    then do
        permission <- getPermissions file
        return $ writable permission
    else return True


-- | With the LLVM AST representation of a LPVM Module, create a
-- target object file, embedding the 'AST.Module' serialised bytestring
-- into the '__lpvm' section of the Macho-O object file.
emitObjectFile :: ModSpec -> FilePath -> Compiler ()
emitObjectFile m f = do
    let filename = f -<.> objectExtension
    logEmit $ "Creating object file for *" ++ showModSpec m ++ "*" ++
        " @ '" ++ filename ++ "'"
    logEmit $ "Encoding and wrapping Module *" ++ showModSpec m
              ++ "* in a wrapped object."
    logEmit $ "Running passmanager on the generated LLVM for *"
              ++ showModSpec m ++ "*."
    modBS <- encodeModule m
    llmod <- descendentModuleLLVM m
    filename <- do
        writable <- liftIO $ _haveWritePermission filename
        if writable
        then return filename
        else do
            logEmit $ "Do not have write permission on file " ++ filename
                ++ ", use local cache file instead"
            liftIO $ createLocalCacheFile filename
    logEmit $ "===> Writing object file " ++ filename
    makeWrappedObjFile filename llmod modBS


-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Bitcode file.
emitBitcodeFile :: ModSpec -> FilePath -> Compiler ()
emitBitcodeFile m f = do
    let filename = f -<.> bitcodeExtension
    logEmit $ "Creating wrapped bitcode file for *" ++ showModSpec m ++ "*"
              ++ " @ '" ++ filename ++ "'"
    -- astMod <- getModule id
    logEmit $ "Encoding and wrapping Module *" ++ showModSpec m
              ++ "* in a wrapped bitcodefile."
    -- modBS <- encodeModule astMod
    modBS <- encodeModule m
    llmod <- descendentModuleLLVM m
    logEmit $ "===> Writing bitcode file " ++ filename
    opts <- gets options
    liftIO $ makeWrappedBCFile opts filename llmod modBS


-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Assembly file.
emitAssemblyFile :: ModSpec -> FilePath -> Compiler ()
emitAssemblyFile m f = do
    let filename = f -<.> assemblyExtension
    logEmit $ "Creating assembly file for " ++ showModSpec m ++
        ", with optimisations."
    llmod <- descendentModuleLLVM m
    logEmit $ "===> Writing assembly file " ++ filename
    opts <- gets options
    let withMod = if optimisationEnabled LLVMOpt opts then withOptimisedModule else withModule 
    liftIO $ withMod opts llmod
        (\mm -> withHostTargetMachineDefault $ \_ ->
            writeLLVMAssemblyToFile (File filename) mm)

-- | Concatenate the LLVMAST.Module implementations of the descendents of
-- the given module.
descendentModuleLLVM :: ModSpec -> Compiler LLVMAST.Module
descendentModuleLLVM mspec = do
    someMods <- sameOriginModules mspec
    unless (List.null someMods) $
        logEmit $ "### Combining descendents of " ++ showModSpec mspec
                   ++ ": " ++ showModSpecs someMods
    llmod <- concatLLVMASTModules mspec someMods
    modBS <- encodeModule mspec
    logEmit $ "### flattened LPVM module to " ++ show modBS
    addLPVMtoLLVM mspec llmod modBS


-- | Create a definition to hold the encoded LPVM for a module as LLVM data
lpvmDefine :: ModSpec -> BL.ByteString -> Definition
lpvmDefine mspec modBS
             = GlobalDefinition $ globalVariableDefaults {
                      name = LLVMAST.Name $ fromString $ show mspec
                    , isConstant = True
                    , G.type' = ArrayType (fromIntegral $ BL.length modBS) (IntegerType 8)
                    , initializer = Just $ C.Array (IntegerType 8)
                                         $ List.map (C.Int 8 . fromIntegral)
                                         $ BL.unpack modBS
                    , section = Just $ fromString lpvmSectionName
                    }


-- | Inject the linearised LPVM byte string into the LLVM code, so that it can
-- later be extracted from the generated object file.
addLPVMtoLLVM :: ModSpec -> LLVMAST.Module -> BL.ByteString -> Compiler LLVMAST.Module
addLPVMtoLLVM mspec llmod modBS = do
    return $ llmod { moduleDefinitions = lpvmDefine mspec modBS:moduleDefinitions llmod}


-- | Handle the ExceptT monad. If there is an error, it is better to fail.
liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

-- | Return string form LLVM IR represenation of a LLVMAST.Module
codeemit :: Options -> LLVMAST.Module -> IO BS.ByteString
codeemit opts llmod = withOptimisedModule opts llmod moduleLLVMAssembly
-- codeemit noVerify llmod = withModule noVerify llmod moduleLLVMAssembly


-------------------------------------------------------------------------------
-- Optimisations                                                             --
-------------------------------------------------------------------------------

-- | Setup the set of passes for optimisations.
-- Currently using the curated set provided by LLVM.
passes :: Word -> PassSetSpec
passes lvl = defaultCuratedPassSetSpec { optLevel = Just lvl }


-- -- | Return a string LLVM IR representation of a LLVMAST.Module after
-- -- a curated set of passes has been executed on the C++ Module form.
-- codeEmitWithPasses :: LLVMAST.Module -> IO BS.ByteString
-- codeEmitWithPasses llmod =
--     withContext $ \context ->
--         withModuleFromAST context llmod $ \m ->
--             withPassManager passes $ \pm -> do
--                 success <- runPassManager pm m
--                 if success
--                     then moduleLLVMAssembly m
--                     else error "Running of optimisation passes not successful!"

-- -- | Testing function to analyse optimisation passes.
-- testOptimisations :: LLVMAST.Module -> IO ()
-- testOptimisations llmod = do
--     llstr <- codeEmitWithPasses llmod
--     putStrLn $ replicate 80 '-'
--     putStrLn "Optimisation Passes"
--     putStrLn $ replicate 80 '-'
--     B8.putStrLn llstr
--     putStrLn $ replicate 80 '-'


-- | Using a bracket pattern, perform an action on the C++ Module
-- representation of a LLVMAST.Module after the C++ module has been through
-- a set of curated passes.
withOptimisedModule :: Options -> LLVMAST.Module -> (Mod.Module -> IO a) -> IO a
withOptimisedModule opts@Options{optLLVMOptLevel=lvl} llmod action =
    withModule opts llmod $ \m -> do
        withPassManager (passes lvl) $ \pm -> do
            success <- runPassManager pm m
            if success
            then action m
            else error "Running of optimisation passes not successful"


-- | Bracket pattern to run an [action] on the [LLVMAST.Module].
withModule :: Options -> LLVMAST.Module -> (Mod.Module -> IO a) -> IO a
withModule Options{optNoVerifyLLVM=noVerify} llmod action =
    withContext $ \context ->
        withModuleFromAST context llmod $ \m -> do
            unless noVerify $ verify m
            action m



----------------------------------------------------------------------------
-- Target Emitters                                                        --
----------------------------------------------------------------------------

-- | Use the bitcode wrapper structure to wrap both the AST.Module
-- (serialised) and the bitcode generated for the Module
makeWrappedBCFile :: Options -> FilePath -> LLVMAST.Module -> BL.ByteString -> IO ()
makeWrappedBCFile opts file llmod modBS =
    withOptimisedModule opts llmod $ \m -> do
        bc <- moduleBitcode m
        let wrapped = getWrappedBitcode (BL.fromStrict bc) modBS
        BL.writeFile file wrapped

-- | Create a Macho-O object file and embed a 'AST.Module' bytestring
-- representation into the '__lpvm' section in it.
makeWrappedObjFile :: FilePath -> LLVMAST.Module -> BL.ByteString -> Compiler ()
makeWrappedObjFile file llmod modBS = do
    tmpDir <- gets tmpDir
    opts <- gets options
    liftIO $ withContext $ \_ ->
        withOptimisedModule opts llmod $ \m -> do
            withHostTargetMachineDefault $ \tm ->
                writeObjectToFile tm (File file) m


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
    -- let options = linkerDeadStripArgs
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
logLLVMString thisMod = do
    reenterModule thisMod
    maybeLLMod <- getModuleImplementationField modLLVM
    case maybeLLMod of
        (Just llmod) -> do
            let llstr = ppllvm llmod
            logEmit $ replicate 80 '-'
            logEmit $ TL.unpack llstr
            logEmit $ replicate 80 '-'
        Nothing -> error "No LLVM Module Implementation"
    reexitModule
    return ()

-- | Pull the LLVMAST representation of the module and generate the LLVM
-- IR String for it, if it exists.
extractLLVM :: AST.Module -> Compiler String
extractLLVM thisMod = do
    opts <- gets options
    case modImplementation thisMod >>= modLLVM of
        Just llmod -> liftIO $ B8.unpack <$> codeemit opts llmod
        Nothing    -> return "No LLVM IR generated."

-- | Log the LLVMIR strings for all the modules compiled, except the standard
-- library.
logLLVMDump :: LogSelection -> LogSelection -> String -> Compiler ()
logLLVMDump selector1 selector2 pass =
    whenLogging2 selector1 selector2 $ do
        modList <- gets (Map.elems . modules)
        let noLibMod = List.filter ((/="wybe"). List.head . modSpec) modList
        liftIO $ putStrLn $ showModSpecs $ List.map modSpec noLibMod
        llvmir <- mapM extractLLVM noLibMod
        liftIO $ putStrLn $ replicate 70 '=' ++ "\nAFTER " ++ pass ++ ":\n\n" ++
            intercalate ("\n" ++ replicate 50 '-' ++ "\n") llvmir
