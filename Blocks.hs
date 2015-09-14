--  File     : Blocks.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Transform a clausal form (LPVM) module to LLVM
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--

module Blocks ( blockTransformModule
              , translateProc )
       where

import           AST
import           Codegen
import           Control.Monad
import           Control.Monad.Trans       (lift, liftIO)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Maybe
import           Options                   (LogSelection (Blocks))

----------------------------------------------------------------------------
-- LLVM Compiler Monad                                                    --
----------------------------------------------------------------------------

-- | The llvm compiler monad is a state transformer monad carrying the
--  clause compiler state over the compiler monad.
-- XXX Maybe this won't be needed once the Codegen module design is finalised
-- XXX Right now, it fits the scaffolding of the build functions in Build.hs
type LLVMComp = StateT LLVMCompState Compiler

-- | The state of translation to LLVM.
-- XXX To be decided
data LLVMCompState = LLVMNop
                     deriving Show

initLLVMComp :: LLVMCompState
initLLVMComp = LLVMNop

evalLLVMComp :: LLVMComp t -> Compiler t
evalLLVMComp llcomp =
  evalStateT llcomp initLLVMComp


-- XXX Not Needed
blockTransformModule :: ModSpec -> Compiler ()
blockTransformModule mod = do
  reenterModule mod
  -- (names, procs) <- :: StateT CompilerState IO ([Ident], [[ProcDef]])
  (onames, procs) <- fmap unzip $
                     getModuleImplementationField (Map.toList . modProcs)
  -- liftIO $ putStrLn "Test"
  -- logBlocks "Testing logging"
  -- updateImplementation (\imp -> imp {modProcs = procs'})
  exitModule
  return ()


-- | Translate a ProcDef whose procImpln field is of the type ProcDefPrim, to
-- ProcDefBlocks (LLVM form). By now the final compilation to LPVM should be done
-- and Codegen module can be leveraged to emit LLVM.
-- TODO: wrap around Codegen/LLVM state monad from Codegen module
-- XXX: This is just scaffolding for now
translateProc :: ProcDef -> Compiler ProcDef
translateProc proc =
    evalLLVMComp $ do
      let def@(ProcDefPrim proto _) = procImpln proc
      logBlocks $ "Proc: " ++ (showProcDef 0 proc)
      return proc


noteProcsSuperprocs :: ModSpec -> ProcName -> [ProcDef] ->
                       Map Ident [ProcDef] -> Map Ident [ProcDef]
noteProcsSuperprocs mod name defs procs =
  List.foldr (\(def,n) ->
               noteImplnSuperprocs (ProcSpec mod name n) (procImpln def))
  procs $ zip defs [0..]

noteImplnSuperprocs :: ProcSpec -> ProcImpln ->
                       Map Ident [ProcDef] -> Map Ident [ProcDef]
noteImplnSuperprocs _ (ProcDefSrc _) _ =
  shouldnt "scanning unprocessed code for calls"
-- XXX do the actual work here:
noteImplnSuperprocs caller (ProcDefPrim _ body) procs = procs
noteImplnSuperprocs _ (ProcDefBlocks _ _) _ =
  shouldnt "scanning already compiled code for calls"


-- | Log messages under the Blocks logOption
logBlocks :: String -> LLVMComp ()
logBlocks s = lift $ logMsg Blocks s

