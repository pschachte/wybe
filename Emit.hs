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


import           Options                      (LogSelection (Emit))


foreign import ccall "dynamic" haskFun :: FunPtr (IO Double) -> (IO Double)

run :: FunPtr a -> IO Double
run fn = haskFun (castFunPtr fn :: FunPtr (IO Double))


-- | Lookup the 'Target' for the given target triple.
getTarget :: IO (Target, String)
getTarget =
    do initializeAllTargets
       let triple = "x86_64-apple-macosx10.11.1"
       liftError $ lookupTarget Nothing triple


-- | Create an Object file of the LLVMAST.Module representation of the
-- given module specification using the default object code generation of
-- llvm.
llvmEmitToObjectFile :: ModSpec
                     -> FilePath
                     -> Compiler AST.Module
llvmEmitToObjectFile thisMod fpath=
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       let ofile = File fpath
       case maybeLLMod of
         (Just llmod) -> liftIO $ makeObjFile ofile llmod
         (Nothing) -> error "No LLVM Module Implementation"
       finishModule

-- | Drop an LLVMAST.Module (haskell) into a Module.Module (C++),
-- and write it as an object file.
makeObjFile :: File -> LLVMAST.Module -> IO ()
makeObjFile file llmod =
    withContext $ \context ->
        liftError $ withModuleFromAST context llmod $ \m ->
            liftError $ withHostTargetMachine $ \tm ->
                liftError $ writeObjectToFile tm file m

-- | Create a LLVM Bitcode file of the LLVMAST.Module representation of
-- the given module.
llvmEmitToBitcodeFile :: ModSpec -> FilePath -> Compiler AST.Module
llvmEmitToBitcodeFile thisMod fpath =
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       let ofile = File fpath
       case maybeLLMod of
         (Just llmod) -> liftIO $ makeBCFile ofile llmod
         (Nothing) -> error "No LLVM Module Implementation"
       finishModule

-- | Drop an LLVMAST.Module (hasjell) intop a Mod.Module (C++)
-- represenation and write is a bitcode file.
makeBCFile :: File -> LLVMAST.Module -> IO ()
makeBCFile file llmod =
    withContext $ \context ->
        liftError $ withModuleFromAST context llmod $ \m ->
            liftError $ writeBitcodeToFile file m


-- | Emit the llvm IR of the LLVMAST.Module representation of the given
-- module tp stdout and use a JIT compiler+optimiser to execute it.
llvmEmitToIO :: ModSpec -> Compiler AST.Module
llvmEmitToIO thisMod =
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       case maybeLLMod of
         (Just llmod) -> liftIO $ runJIT llmod
         -- (Just llmod) -> liftIO $ codeemit llmod
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
            do putStrLn $ "Emitting for: " ++ (LLVMAST.moduleName mod)
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

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

logLLVM :: String -> Compiler ()
logLLVM s = logMsg Emit s
