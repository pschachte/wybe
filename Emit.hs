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
       (names, procs) <- fmap unzip $
                         getModuleImplementationField (Map.toList . modProcs)
       let procs' = List.foldr (++) [] procs
       let defs = List.map takeDefinition procs'
       s <- liftIO $ codeemit (showModSpec thisMod) defs
       -- logLLVM s

       finishModule

liftError :: ExceptT String IO a -> IO a
liftError = runExceptT >=> either fail return

codeemit :: String -> [LLVMAST.Definition] -> IO String
codeemit name defs =
    withContext $ \context ->
        liftError $ withModuleFromAST context mod $ \m ->
            do llstr <- moduleLLVMAssembly m
               putStrLn llstr
               return llstr
        where
          mod = modWithDefinitions name defs


modWithDefinitions :: String -> [LLVMAST.Definition] -> LLVMAST.Module
modWithDefinitions nm defs = LLVMAST.Module nm Nothing Nothing defs




takeDefinition :: ProcDef -> LLVMAST.Definition
takeDefinition p = case procImpln p of
                     (ProcDefBlocks _ def) -> def
                     _ -> error "No definition found."



logLLVM :: String -> Compiler ()
logLLVM s = logMsg Emit s
