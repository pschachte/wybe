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

import           LLVM.General.Analysis
import           LLVM.General.PassManager
import           LLVM.General.Transforms

import qualified LLVM.General.ExecutionEngine as EE

import           System.Directory
import           System.Process

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
withModuleLLVM :: ModSpec -> (LLVMAST.Module -> IO ()) -> Compiler ()
withModuleLLVM thisMod action = do
    reenterModule thisMod
    maybeLLMod <- getModuleImplementationField modLLVM
    case maybeLLMod of
      (Just llmod) -> liftIO $ action llmod
      (Nothing) -> error "No LLVM Module Implementation"
    finishModule
    return ()

-- | With the LLVM AST representation of a LPVM Module, create a
-- target object file.
emitObjectFile :: ModSpec -> FilePath -> Compiler ()
emitObjectFile m f = do
    logEmit $ "Creating object file for *" ++ (showModSpec m) ++ "*" ++
        " @ '" ++ f ++ "'"
    withModuleLLVM m (makeObjFile f)
    -- Also make the bitcode file for now
    emitBitcodeFile m $ (dropExtension f) ++ ".bc"

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
    logEmit $ "Creating assembly file for " ++ (showModSpec m)
    withModuleLLVM m (makeAssemblyFile f)


-- | Handle the ExceptT monad. If there is an error, it is better to fail.
liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

-- | Emit the llvm IR version of the LLVMAST.Module to IO
codeemit :: LLVMAST.Module -> IO String
codeemit mod =
    withContext $ \context ->
        liftError $ withModuleFromAST context mod $ \m ->
            do llstr <- moduleLLVMAssembly m
               -- putStrLn llstr
               return llstr


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

-- | Drop an LLVMAST.Module (hasjell) intop a Mod.Module (C++)
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


-- | Emit the llvm IR of the LLVMAST.Module representation of the given
-- module tp stdout and use a JIT compiler+optimiser to execute it.
llvmEmitToIO :: ModSpec -> Compiler ()
llvmEmitToIO thisMod =
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       case maybeLLMod of
         -- (Just llmod) -> liftIO $ runJIT llmod
         (Just llmod) -> liftIO $ codeemit llmod
         (Nothing) -> error "No LLVM Module Implementation"
       finishModule
       return ()



-- | Initialize the JIT compiler under the IO monad.
jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c optlevel model ptrelim fastins
  where
    optlevel = Just 0  -- optimization level
    model    = Nothing -- code model ( Default )
    ptrelim  = Nothing -- frame pointer elimination
    fastins  = Nothing -- fast instruction selection

-- | Setup the set of passes the JIT will be using for optimisations.
passes :: PassSetSpec
passes = defaultCuratedPassSetSpec { optLevel = Just 3 }


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
         -> IO ()
makeExec ofiles target =
    do dir <- getCurrentDirectory
       let args = ofiles ++ sharedLibs ++ ["-o", target]
       -- Supressing the annoying Xcode warning 
       (_, _, Just herr, _) <-
           createProcess (proc "cc" args){ std_err = CreatePipe }
       return ()

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
