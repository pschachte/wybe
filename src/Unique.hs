--  File     : Unique.hs
--  Purpose  : The unique typing system for Wybe
--  Copyright: (c) 
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
-- This module defines the unique typing system for Wybe.


module Unique (uniquenessCheckProc) where

import AST
import Options
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.List as List
import Data.Set as Set
import Data.Map as Map
import Data.Maybe


-- | Uniqueness error with specs of the variable
data UniquenessError = UniquenessError {
    errVarName  :: VarName,
    errTypeSpec :: TypeSpec,
    errPos      :: OptPos
}

-- | Set used to check correctness of uniqueness of the program
data UniquenessState = UniquenessState {
    uniquenessUsedMap :: Map VarName TypeSpec,
    uniquenessErrors  :: [UniquenessError]
}


-- | Return an initial state for uniqueness checker
initUniquenessState :: UniquenessState
initUniquenessState = UniquenessState Map.empty []


-- | Check correctness of uniqueness for a procedure
uniquenessCheckProc :: [Placed Stmt] -> Compiler ()
uniquenessCheckProc body = do
    logUniqueness $ "Uniqueness checking body: " ++ showBody 4 body
    let state = foldStmts (const . const) uniquenessCheckExp initUniquenessState body
    errs <- filterM (typeIsUnique . errTypeSpec) (uniquenessErrors state)
    mapM_ reportUniquenessError errs


-- | Check correctness of uniqueness for an expression
uniquenessCheckExp :: UniquenessState -> Exp -> OptPos -> UniquenessState
uniquenessCheckExp state (Typed (Var name ParamIn _) ty _) pos =
    let (UniquenessState usedMap errs) = state
    in if Map.member name usedMap
    then state {uniquenessErrors = UniquenessError name ty pos : errs}
    else state {uniquenessUsedMap = Map.insert name ty usedMap}

uniquenessCheckExp state (Typed (Var name ParamOut _) ty _) _ =
    state {uniquenessUsedMap = Map.delete name (uniquenessUsedMap state)}

uniquenessCheckExp state _ _ = state


-- | Check if a type is unique
typeIsUnique :: TypeSpec -> Compiler Bool
typeIsUnique TypeSpec { typeMod = mod, typeName = name } = do
    let mod' = mod ++ [name]
    getSpecModule "typeIsUnique" (tmUniqueness . typeModifiers . modInterface)
                  mod'
typeIsUnique _ = return False
 

-- | Report an error when a unique typed variable is being reused
reportUniquenessError :: UniquenessError -> Compiler ()
reportUniquenessError (UniquenessError name ty pos) = do
    errmsg pos $ "Reuse of unique variable " ++ name ++ ":" ++ show ty


-- | Log a message, if we are logging type checker activity.
logUniqueness :: String -> Compiler ()
logUniqueness = logMsg Uniqueness