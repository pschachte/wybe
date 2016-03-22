module Emit where

import           AST
import           Codegen
import           Control.Applicative ((<$>), (<*>))
import           Control.Monad
import           Control.Monad.Trans (lift, liftIO)
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Data.List as List
import           Data.Map as Map
import           Foreign.Ptr (FunPtr, castFunPtr)
import qualified LLVM.General.AST as LLVMAST
import           LLVM.General.CodeModel
import           LLVM.General.Context
import           LLVM.General.Module as Mod
import           LLVM.General.Target

import qualified Data.ByteString.Lazy as BL

import           LLVM.General.Analysis
import           LLVM.General.PassManager
import           LLVM.General.Transforms

import qualified LLVM.General.ExecutionEngine as EE

import           System.Directory
import           System.Process
import System.IO (hGetContents)

import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Binary (encode)

import           Config
import           ObjectInterface
import           Options (LogSelection (Emit))
import           System.FilePath (dropExtension)

foreign import ccall "dynamic" haskFun :: FunPtr (IO Double) -> (IO Double)

run :: FunPtr a -> IO Double
run fn = haskFun (castFunPtr fn :: FunPtr (IO Double))


-- | Bracket matter to pull an LLVM AST Module representation of a
-- LPVM module specification, and run some action on it under the compiler
-- monad.
withModuleLLVM :: ModSpec -> (LLVMAST.Module -> IO a) -> Compiler a
withModuleLLVM thisMod action = do
    reenterModule thisMod
    maybeLLMod <- getModuleImplementationField modLLVM
    finishModule
    case maybeLLMod of
      (Just llmod) -> liftIO $ action llmod
      (Nothing) -> error "No LLVM Module Implementation"

-- | With the LLVM AST representation of a LPVM Module, create a
-- target object file, embedding the 'AST.Module' serialised bytestring
-- into the '__lpvm' section of the Macho-O object file.
emitObjectFile :: ModSpec -> FilePath -> Compiler ()
emitObjectFile m f = do
    logEmit $ "Creating object file for *" ++ (showModSpec m) ++ "*" ++
        " @ '" ++ f ++ "'"
    reenterModule m
    maybeLLMod <- getModuleImplementationField modLLVM
    case maybeLLMod of
        (Just llmod) ->
            do astMod <- getModule id
               logEmit $ "Encoding and wrapping Module *" ++ (showModSpec m)
                   ++ "* in a wrapped object."
               liftIO $ makeWrappedObjFile f llmod astMod
        (Nothing) -> error "No LLVM Module Implementation"
    finishModule
    return ()
    -- withModuleLLVM m (makeWrappedObjFile f)
    -- Also make the bitcode file for now
    -- emitBitcodeFile m $ (dropExtension f) ++ ".bc"

-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Bitcode file.
emitBitcodeFile :: ModSpec -> FilePath -> Compiler ()
emitBitcodeFile m f = do
   logEmit $ "Creating wrapped bitcode file for *" ++ (showModSpec m) ++ "*"
       ++ " @ '" ++ f ++ "'"
   reenterModule m
   maybeLLMod <- getModuleImplementationField modLLVM
   case maybeLLMod of
     (Just llmod) ->
       do astMod <- getModule id
          logEmit $ "Encoding and wrapping Module *" ++ (showModSpec m)
            ++ "* in a wrapped bitcodefile."
          liftIO $ makeWrappedBCFile f llmod astMod
     (Nothing) -> error "No LLVM Module Implementation"
   finishModule
   return ()

-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Assembly file.
emitAssemblyFile :: ModSpec -> FilePath -> Compiler ()
emitAssemblyFile m f = do
    logEmit $ "Creating assembly file for " ++ (showModSpec m) ++
        ("with optimisations.")
    -- withModuleLLVM m (makeAssemblyFile f)
    withModuleLLVM m $ \llmod -> withOptimisedModule llmod
        (\mm -> liftError $ withHostTargetMachine $ \tm ->
            liftError $ writeLLVMAssemblyToFile (File f) mm)


-- | Handle the ExceptT monad. If there is an error, it is better to fail.
liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

-- | Return string form LLVM IR represenation of a LLVMAST.Module
codeemit :: LLVMAST.Module -> IO String
codeemit mod =
    withContext $ \context ->
        liftError $ withModuleFromAST context mod $ \m ->
            moduleLLVMAssembly m >>= return


-------------------------------------------------------------------------------
-- Optimisations                                                             --
-------------------------------------------------------------------------------

-- | Setup the set of passes for optimisations.
-- Currently using the curated set provided by LLVM.
passes :: PassSetSpec
passes = defaultCuratedPassSetSpec { optLevel = Just 3 }


-- | Return a string LLVM IR representation of a LLVMAST.Module after
-- a curated set of passes has been executed on the C++ Module form.
codeEmitWithPasses :: LLVMAST.Module -> IO String
codeEmitWithPasses llmod = do
    withContext $ \context -> do
        liftError $ withModuleFromAST context llmod $ \m -> do
            withPassManager passes $ \pm -> do
                success <- runPassManager pm m
                if success
                    then moduleLLVMAssembly m >>= return
                    else error "Running of optimisation passes not successful!"

-- | Testing function to analyse optimisation passes.
testOptimisations :: LLVMAST.Module -> IO ()
testOptimisations llmod = do
    llstr <- codeEmitWithPasses llmod
    putStrLn $ replicate 80 '-'
    putStrLn "Optimisation Passes"
    putStrLn $ replicate 80 '-'
    putStrLn llstr
    putStrLn $ replicate 80 '-'


-- | Using a bracket pattern, perform an action on the C++ Module
-- representation of a LLVMAST.Module after the C++ module has been through
-- a set of curated passes.
withOptimisedModule :: LLVMAST.Module -> (Mod.Module -> IO a)
                    -> IO a
withOptimisedModule llmod action = do
    withContext $ \context -> do
        liftError $ withModuleFromAST context llmod $ \m -> do
            withPassManager passes $ \pm -> do
                success <- runPassManager pm m
                if success
                    then action m
                    else error "Running of optimisation passes not successful"


----------------------------------------------------------------------------
-- Target Emitters                                                        --
----------------------------------------------------------------------------

-- | Drop an LLVMAST.Module (haskell) into a LLVM Module.Module (C++),
-- and write it as an object file.
makeObjFile :: FilePath -> LLVMAST.Module -> IO ()
makeObjFile file llmod =
    withContext $ \context ->
        liftError $ withModuleFromAST context llmod $ \m ->
            liftError $ withHostTargetMachine $ \tm ->
                liftError $ writeObjectToFile tm (File file) m

-- | Drop an LLVMAST.Module (haskell) intop a Mod.Module (C++)
-- represenation and write is a bitcode file.
makeBCFile :: FilePath -> LLVMAST.Module -> IO ()
makeBCFile file llmod =
    withContext $ \context ->
        liftError $ withModuleFromAST context llmod $ \m ->
            liftError $ writeBitcodeToFile (File file) m


-- | Use the bitcode wrapper structure to wrap both the AST.Module
-- (serialised) and the bitcode generated for the Module
makeWrappedBCFile :: FilePath -> LLVMAST.Module -> AST.Module -> IO ()
makeWrappedBCFile file llmod origMod =
    withContext $ \context ->
        liftError $ withModuleFromAST context llmod $ \m ->
            do bc <- moduleBitcode m
               -- encode the AST.Module type into a bytestring
               let modBS = encode origMod
               let wrapped = getWrappedBitcode (BL.fromStrict bc) modBS
               BL.writeFile file wrapped


-- | Drop an LLVMAST.Module (haskell) into a Module.Module (C++),
-- and write it as an object file.
makeAssemblyFile :: FilePath -> LLVMAST.Module -> IO ()
makeAssemblyFile file llmod =
    withContext $ \context ->
        liftError $ withModuleFromAST context llmod $ \m ->
            liftError $ withHostTargetMachine $ \tm ->
                liftError $ writeLLVMAssemblyToFile (File file) m


-- | Create a Macho-O object file and embed a 'AST.Module' bytestring
-- representation into the '__lpvm' section in it.
makeWrappedObjFile :: FilePath -> LLVMAST.Module -> AST.Module -> IO ()
makeWrappedObjFile file llmod origMod = do
    withContext $ \context -> do
        liftError $ withModuleFromAST context llmod $ \m -> do
            let modBS = encode origMod
            liftError $ withHostTargetMachine $ \tm ->
                liftError $ writeObjectToFile tm (File file) m
            insertLPVMDataLd modBS file



------------------------------------------------------------------------------
-- JIT Support                                                              --
------------------------------------------------------------------------------

-- | Initialize the JIT compiler under the IO monad.
jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c optlevel model ptrelim fastins
  where
    optlevel = Just 0  -- optimization level
    model    = Nothing -- code model ( Default )
    ptrelim  = Nothing -- frame pointer elimination
    fastins  = Nothing -- fast instruction selection


-- | Convert a LLVMAST.Module representation to LLVM IR and run it with a JIT
-- compiler+optimiser. The running and emitting is done to stdout. The JIT will
-- look for the function `main` to execute.
runJIT :: LLVMAST.Module -> IO (Either String LLVMAST.Module)
runJIT mod = do
  withContext $ \context ->
    jit context $ \executionEngine ->
      runExceptT $ withModuleFromAST context mod $ \m ->
        withPassManager passes $ \pm -> do
          -- Optimization Pass
          {-runPassManager pm m-}
          optmod <- moduleAST m
          s <- moduleLLVMAssembly m
          putStrLn s

          EE.withModuleInEngine executionEngine m $ \ee -> do
            mainfn <- EE.getFunction ee (LLVMAST.Name "main")
            case mainfn of
              Just fn -> do
                putStrLn $ "Running: "
                res <- run fn
                putStrLn $ "Main returned: " ++ show res
              Nothing -> return ()

          -- Return the optimized module
          return optmod


----------------------------------------------------------------------------
-- -- * Linking                                                           --
----------------------------------------------------------------------------


-- | With the `ld` linker, link the object files and create target
-- executable.
makeExec :: [FilePath]          -- Object Files
         -> FilePath            -- Target File
         -> IO String
makeExec ofiles target =
    do dir <- getCurrentDirectory
       let args = ofiles ++ sharedLibs ++ ["-o", target]
       -- Supressing the annoying Xcode warning
       (_,_, Just hout,_) <- createProcess (proc "cc" args){std_err = CreatePipe}
       errCons <- hGetContents hout
       -- putStrLn errCons
       -- createProcess (proc "cc" args)
       return errCons

-- makeExec ofiles target =
--     do dir <- getCurrentDirectory
--        let args = ofiles ++ sharedLibs ++ ldArgs ++ ldSystemArgs
--                   ++ ["-o", target]
--        createProcess (proc "ld" args)
--        return ()



----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

logEmit :: String -> Compiler ()
logEmit s = logMsg Emit s

-- | Log LLVM IR representation of the given module.
logLLVMString :: ModSpec -> Compiler ()
logLLVMString thisMod =
  do reenterModule thisMod
     maybeLLMod <- getModuleImplementationField modLLVM
     case maybeLLMod of
       (Just llmod) ->
         do llstr <- liftIO $ codeemit llmod
            logEmit $ replicate 80 '-'
            logEmit llstr
            logEmit $ replicate 80 '-'
       (Nothing) -> error "No LLVM Module Implementation"
     finishModule
     return ()

-- | Pull the LLVMAST representation of the module and generate the LLVM
-- IR String for it, if it exists.
extractLLVM :: AST.Module -> Compiler String
extractLLVM thisMod =
  do case (modImplementation thisMod) >>= modLLVM of
       Just llmod -> liftIO $ codeemit llmod
       Nothing -> return "No LLVM IR generated."

-- | Log the LLVMIR strings for all the modules compiled, except the standard
-- library.
logLLVMDump :: LogSelection -> LogSelection -> String -> Compiler ()
logLLVMDump selector1 selector2 pass = do
  whenLogging2 selector1 selector2 $
    do modList <- gets (Map.elems . modules)
       let noLibMod = List.filter ((/="wybe"). List.head . modSpec) modList
       liftIO $ putStrLn $ showModSpecs $ List.map modSpec noLibMod
       llvmir <- mapM extractLLVM noLibMod
       liftIO $ putStrLn $ replicate 70 '=' ++ "\nAFTER " ++ pass ++ ":\n\n" ++
         intercalate ("\n" ++ replicate 50 '-' ++ "\n") llvmir
