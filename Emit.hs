module Emit where


import           AST
import           Codegen
import           Control.Monad
import           Control.Monad.Trans        (lift, liftIO)
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Data.List                  as List
import           Data.Map                   as Map
import qualified LLVM.General.AST           as LLVMAST
import           LLVM.General.Context
import           LLVM.General.Module
import           Options                    (LogSelection (Emit))

type LLVMEmit = StateT LLVMAST.Module Compiler


llvmEmitModule :: ModSpec -> Compiler AST.Module
llvmEmitModule thisMod =
    do reenterModule thisMod
       maybeLLMod <- getModuleImplementationField modLLVM
       case maybeLLMod of
         (Just llmod) -> liftIO $ codeemit llmod
         (Nothing) -> error "No LLVM Module Implementation"
       finishModule

liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

codeemit :: LLVMAST.Module -> IO String
codeemit mod =
    withContext $ \context ->
        liftError $ withModuleFromAST context mod $ \m ->
            do llstr <- moduleLLVMAssembly m
               putStrLn llstr
               return llstr

logLLVM :: String -> Compiler ()
logLLVM s = logMsg Emit s
