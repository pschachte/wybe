module Emit where

import           AST
import           Codegen
import           Control.Monad
import           Control.Monad.Trans          (lift, liftIO)
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Foreign.Ptr                  (FunPtr, castFunPtr)
import qualified LLVM.General.AST             as LLVMAST
import           LLVM.General.CodeModel
import           LLVM.General.Context
import           LLVM.General.Module          as Mod
import           LLVM.General.Target

import           LLVM.General.Analysis
import           LLVM.General.PassManager
import           LLVM.General.Transforms

import qualified LLVM.General.ExecutionEngine as EE

import           System.Directory
import           System.Process

import           Config                       (linkerArgs, sharedLibs)
import           Options                      (LogSelection (Emit))

foreign import ccall "dynamic" haskFun :: FunPtr (IO Double) -> (IO Double)

run :: FunPtr a -> IO Double
run fn = haskFun (castFunPtr fn :: FunPtr (IO Double))


-- | Bracket matter to pull an LLVM AST Module representation of a
-- LPVM module specification, and run some action on it under the compiler
-- monad.
withModuleLLVM :: ModSpec -> (LLVMAST.Module -> IO ()) -> Compiler ()
withModuleLLVM thisMod action =
  do reenterModule thisMod
     maybeLLMod <- getModuleImplementationField modLLVM
     case maybeLLMod of
       (Just llmod) -> liftIO $ action llmod
       (Nothing) -> error "No LLVM Module Implementation"
     finishModule
     return ()

-- | With the LLVM AST representation of a LPVM Module, create a
-- target object file.
emitObjectFile :: ModSpec -> FilePath -> Compiler ()
emitObjectFile m f =
  do logEmit $ "Creating object file for " ++ (showModSpec m)
     withModuleLLVM m (makeObjFile f)

-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Bitcode file.
emitBitcodeFile :: ModSpec -> FilePath -> Compiler ()
emitBitcodeFile m f =
  do logEmit $ "Creating bitcode file for " ++ (showModSpec m)
     withModuleLLVM m (makeBCFile f)

-- | With the LLVM AST representation of a LPVM Module, create a
-- target LLVM Assembly file.
emitAssemblyFile :: ModSpec -> FilePath -> Compiler ()
emitAssemblyFile m f =
  do logEmit $ "Creating assembly file for " ++ (showModSpec m)
     withModuleLLVM m (makeAssemblyFile f)


logLLVMString :: ModSpec -> Compiler ()
logLLVMString thisMod =
  do reenterModule thisMod
     maybeLLMod <- getModuleImplementationField modLLVM
     case maybeLLMod of
       (Just llmod) -> liftIO $ codeemit llmod
       (Nothing) -> error "No LLVM Module Implementation"
     finishModule
     return ()

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
llvmEmitToIO :: ModSpec -> Compiler AST.Module
llvmEmitToIO thisMod =
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       case maybeLLMod of
         -- (Just llmod) -> liftIO $ runJIT llmod
         (Just llmod) -> liftIO $ codeemit llmod
         (Nothing) -> error "No LLVM Module Implementation"
       finishModule


-- | Handle the ExceptT monad. If there is an error, it is better to fail.
liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

-- | Emit the llvm IR version of the LLVMAST.Module to IO
codeemit :: LLVMAST.Module -> IO String
codeemit mod =
    withContext $ \context ->
        liftError $ withModuleFromAST context mod $ \m ->
            do putStrLn $ "Emitting module: " ++ (LLVMAST.moduleName mod)
               llstr <- moduleLLVMAssembly m
               putStrLn llstr
               return llstr

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


-- |Build executable from object file
buildExecutable :: ModSpec -> FilePath -> Compiler ()
buildExecutable thisMod fpath =
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       let objFileName = (fpath ++ ".o")
       case maybeLLMod of
         (Just llmod) ->
             do liftIO $ makeObjFile objFileName llmod
                logEmit $ "Built object file: " ++ objFileName
                liftIO $ makeExec fpath
                logEmit $ "Built executable: " ++ fpath
         (Nothing) -> message Error "No LLVM Module Implementation" Nothing
       finishModule
       return ()

makeExec :: FilePath -> IO ()
makeExec execFile =
    do dir <- getCurrentDirectory
       let objFile = (execFile ++ ".o")
       let args = [objFile] ++ sharedLibs ++ linkerArgs
                  ++ ["-o", execFile]
       createProcess (proc "ld" args)
       return ()

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

logEmit :: String -> Compiler ()
logEmit s = logMsg Emit s
