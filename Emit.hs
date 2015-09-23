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


type LLVMEmit = StateT LLVMAST.Module Compiler


llvmEmitModule :: ModSpec -> Compiler AST.Module
llvmEmitModule thisMod =
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       case maybeLLMod of
         (Just llmod) -> liftIO $ runJIT llmod
         -- (Just llmod) -> liftIO $ codeemit llmod
         (Nothing) -> error "No LLVM Module Implementation"
       finishModule

liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

codeemit :: LLVMAST.Module -> IO String
codeemit mod =
    withContext $ \context ->
        liftError $ withModuleFromAST context mod $ \m ->
            do putStrLn $ "Emitting for: " ++ (LLVMAST.moduleName mod)
               llstr <- moduleLLVMAssembly m
               putStrLn llstr
               return llstr

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c optlevel model ptrelim fastins
  where
    optlevel = Just 0  -- optimization level
    model    = Nothing -- code model ( Default )
    ptrelim  = Nothing -- frame pointer elimination
    fastins  = Nothing -- fast instruction selection

passes :: PassSetSpec
passes = defaultCuratedPassSetSpec { optLevel = Just 3 }


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
                res <- run fn
                putStrLn $ "Evaluated to: " ++ show res
              Nothing -> return ()

          -- Return the optimized module
          return optmod


logLLVM :: String -> Compiler ()
logLLVM s = logMsg Emit s
