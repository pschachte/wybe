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
import GHC.TypeNats (Mod)


-- | Uniqueness error with specs of the variable
data UniquenessError = ReuseUnique {
    errVarName  :: VarName,       -- ^ Variable with a uniqueness error
    errTypeSpec :: TypeSpec,      -- ^ Type of the variable
    errPos      :: OptPos,        -- ^ Source position of the variable or expr
    errFlowType :: ArgFlowType,   -- ^ The flow type (variable or resource)
    errContext  :: Maybe ProcName -- ^ The proc involved if the reuse stems from
                                  --   returning the variable/resource as a 
                                  --   parameter of a proc
} deriving Show

-- | Set used to check correctness of uniqueness of the program
data UniquenessState = UniquenessState {
    uniquenessUsedMap :: VarDict,
    uniquenessErrors  :: [UniquenessError]
} deriving Show


-- | Return an initial state for uniqueness checker
initUniquenessState :: UniquenessState
initUniquenessState = UniquenessState Map.empty []


-- | Check correctness of uniqueness for a procedure
uniquenessCheckProc :: ProcDef -> Int -> Compiler ProcDef
uniquenessCheckProc def _ = do
    let name = procName def
    let pos = procPos def
    logUniqueness $ "Uniqueness checking proc: " ++ name
    let detism = procDetism def
    let params = procProtoParams $ procProto def
    logUniqueness $ "with params: " ++ show params
    someUnique <- elem (Just True) <$>
                  mapM (((tmUniqueness . typeModifiers . modInterface <$>) <$>)
                        <$> getLoadingModule)
                      (catMaybes $ typeModule . paramType <$> params)
    unless (detism `determinismLEQ` Det || not someUnique)
           (errmsg (procPos def)
            $ showProcName name ++ " with unique argument can fail") 
    case procImpln def of
        ProcDefSrc body -> do
            let state = foldStmts (const . const) uniquenessCheckExp
                        initUniquenessState body
            logUniqueness $ "After checking body: " ++ show state
            let state' = List.foldl (uniquenessCheckParam name pos) state params
            logUniqueness $ "After checking params: " ++ show state'
            errs <- filterM (typeIsUnique . errTypeSpec) (uniquenessErrors state')
            mapM_ reportUniquenessError errs
            return def
        _ -> shouldnt $ "Uniqueness check of non-source proc def "
                        ++ show (procName def)


-- | Check correctness of uniqueness for an expression
uniquenessCheckExp :: UniquenessState -> Exp -> OptPos -> UniquenessState
uniquenessCheckExp state (Typed (Var name ParamIn flow) ty _) pos =
    let (UniquenessState usedMap errs) = state
    in if Map.member name usedMap
    then state {uniquenessErrors = ReuseUnique name ty pos flow Nothing : errs}
    else state {uniquenessUsedMap = Map.insert name ty usedMap}
uniquenessCheckExp state (Typed (Var name ParamOut _) ty _) _ =
    state {uniquenessUsedMap = Map.delete name (uniquenessUsedMap state)}
uniquenessCheckExp state _ _ = state


uniquenessCheckParam :: ProcName -> OptPos -> UniquenessState -> Param
                     -> UniquenessState
uniquenessCheckParam name pos state (Param p ty flow flowType)
 |  flowsOut flow && Map.member p (uniquenessUsedMap state) =
     -- error:  producing value as output after using it
     state { uniquenessErrors = ReuseUnique p ty pos flowType (Just name)
                                : uniquenessErrors state}
 |  otherwise = state

-- | Check if a type is unique
typeIsUnique :: TypeSpec -> Compiler Bool
typeIsUnique TypeSpec { typeMod = mod, typeName = name } = do
    let mod' = mod ++ [name]
    getSpecModule "typeIsUnique" (tmUniqueness . typeModifiers . modInterface)
                  mod'
typeIsUnique _ = return False


-- | Report an error when a unique typed variable is being reused
reportUniquenessError :: UniquenessError -> Compiler ()
reportUniquenessError (ReuseUnique name ty pos flow Nothing) = do
    errmsg pos $ "Reuse of unique " ++ flowKind flow name ty
reportUniquenessError (ReuseUnique name ty pos flow (Just proc)) = do
    errmsg pos $ "Unique " ++ flowKind flow name ty ++ " live at end of "
                 ++ showProcName proc


-- | Give a human-readable description of reused variable (may be a resource).
flowKind :: ArgFlowType -> VarName -> TypeSpec -> String
flowKind (Resource res) _ _ = "resource " ++ show res
flowKind _ name ty          = "variable " ++ name ++ ":" ++ show ty


-- | Log a message, if we are logging type checker activity.
logUniqueness :: String -> Compiler ()
logUniqueness = logMsg Uniqueness