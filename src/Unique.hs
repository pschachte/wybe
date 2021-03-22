-- BEGIN MAJOR DOC

-- END MAJOR DOC
----------------------------------------------------------------

module Unique where

import AST
import Snippets
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.List as List
import Data.Set as Set
import Data.Map as Map
import Data.Maybe


type Uniqueness

data UniquenessState = Uniqueness {
    uniqueUsedSet :: [VarName]  -- QUESTION: type
}

initUniquenessState :: UniquenessState
initUniquenessState = Uniqueness []

uniquenessCheckProcDef :: ProcName -> Compiler (UniquenessState)
uniquenesscheckStmt :: ModSpec -> ProcName -> OptPos -> Typing
                    -> [(Set VarName,Placed Stmt)] -> BindingState -> Determinism
                    -> Stmt -> OptPos
                    -> Compiler ([Placed Stmt], [(Set VarName,Placed Stmt)],
                              BindingState, [TypeError])
uniquenesscheckStmts :: ModSpec -> ProcName -> OptPos -> Typing
                     -> [(Set VarName,Placed Stmt)] -> BindingState -> Determinism
                     -> [Placed Stmt]
                     -> Compiler ([Placed Stmt], BindingState, [TypeError])
