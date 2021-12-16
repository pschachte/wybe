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
    -- |The variables used so far in the current scope, with their types.
    uniquenessUsedMap :: VarDict,
    -- |The uniqueness errors seen so far.
    uniquenessErrors  :: [UniquenessError],
    -- |The maximum determinism allowed in the current scope.  Assignment to
    -- unique variables is not allowed outside a deterministic scope.
    uniquenessDetism  :: Determinism
} deriving Show


-- | Return an initial state for uniqueness checker
initUniquenessState :: Determinism -> UniquenessState
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
    -- XXX this only considers whether arguments are unique, ignoring direction
    -- of flow.  When users can declare their own unique types, this won't work.
    someUnique <- elem (Just True) <$>
                  mapM (((tmUniqueness . typeModifiers . modInterface <$>) <$>)
                        <$> getLoadingModule)
                      (catMaybes $ typeModule . paramType <$> params)
    unless (detism `determinismLEQ` Det || not someUnique)
           (errmsg (procPos def)
            $ showProcName name ++ " with unique argument can fail") 
    case procImpln def of
        ProcDefSrc body -> do
            state <- uniquenessCheckDef name pos detism body params
            logUniqueness $ "After checking params: " ++ show state
            mapM_ reportUniquenessError $ reverse $ uniquenessErrors state
            return def
        _ -> shouldnt $ "Uniqueness check of non-source proc def "
                        ++ show (procName def)


----------------------------------------------------------------
--               The Uniqueness Checker Monad
----------------------------------------------------------------

-- |The Uniqueness monad is a state transformer monad carrying the 
--  uniqueness state over the compiler monad.
type Uniqueness = StateT UniquenessState Compiler


uniquenessCheckDef :: ProcName -> OptPos -> Determinism -> [Placed Stmt]
                   -> [Param] -> Compiler UniquenessState
uniquenessCheckDef name pos detism body params =
    execStateT 
    (uniquenessCheckStmts body >> mapM_ (uniquenessCheckParam name pos) params)
    $ initUniquenessState detism


-- | Note a variable use, reporting an error if it has already been used.
variableUsed :: VarName -> OptPos -> TypeSpec -> ArgFlowType -> Uniqueness ()
variableUsed name pos ty flowType = do
    alreadyUsed <- Map.member name <$> gets uniquenessUsedMap
    when alreadyUsed $ uniquenessErr $ ReuseUnique name ty pos flowType Nothing
    isUnique <- lift $ typeIsUnique ty
    when isUnique
     $ modify $ \st -> st {uniquenessUsedMap = Map.insert name ty
                                              $ uniquenessUsedMap st }


-- | Note a variable use, reporting an error if it has already been used.
variableAssigned :: VarName -> Uniqueness ()
variableAssigned name =
    modify $ \st -> st {uniquenessUsedMap = Map.delete name
                                            $ uniquenessUsedMap st }


-- | Report a uniqueness error
uniquenessErr :: UniquenessError -> Uniqueness ()
uniquenessErr err = do
    modify $ \st -> st { uniquenessErrors = err : uniquenessErrors st }


withDetism :: Uniqueness a -> Determinism -> Uniqueness a
withDetism a detism = do
    oldDetism <- gets uniquenessDetism
    modify $ \state -> state { uniquenessDetism = detism }
    result <- a
    modify $ \state -> state { uniquenessDetism = oldDetism }
    return result


joinUniqueness :: Uniqueness () -> Uniqueness () -> Uniqueness ()
joinUniqueness first second = do
    initial <- get
    let start = initial { uniquenessErrors = [] }
    put start
    first
    firstState <- get
    put start
    second
    secondState <- get
    let allErrs = uniquenessErrors secondState ++ uniquenessErrors firstState
                  ++ uniquenessErrors initial
    let joinUsed = uniquenessUsedMap firstState 
                   `Map.intersection` uniquenessUsedMap secondState
    put $ UniquenessState joinUsed allErrs $ uniquenessDetism initial


-- | Uniqueness check a statement sequence
uniquenessCheckStmts :: [Placed Stmt] -> Uniqueness ()
uniquenessCheckStmts = mapM_ $ placedApply uniquenessCheckStmt


-- | Uniqueness check a single statement
uniquenessCheckStmt :: Stmt -> OptPos -> Uniqueness ()
uniquenessCheckStmt (ProcCall _ _ _ _ _ args) pos =
    mapM_ (defaultPlacedApply uniquenessCheckExp pos) args
uniquenessCheckStmt (ForeignCall _ _ _ args) pos =
    mapM_ (defaultPlacedApply uniquenessCheckExp pos) args
uniquenessCheckStmt (Cond tst thn els _ _) pos =
    (defaultPlacedApply uniquenessCheckStmt pos tst `withDetism` SemiDet
     >> uniquenessCheckStmts thn)
    `joinUniqueness` uniquenessCheckStmts els
uniquenessCheckStmt (Case exp cases deflt) pos = do
    defaultPlacedApply uniquenessCheckExp pos exp
    uniquenessCheckCases uniquenessCheckStmts cases deflt
uniquenessCheckStmt (And stmts) _ = uniquenessCheckStmts stmts
uniquenessCheckStmt (Or [] _) pos = return ()
uniquenessCheckStmt (Or [stmt] _) pos =
    defaultPlacedApply uniquenessCheckStmt pos stmt
uniquenessCheckStmt (Or (stmt:stmts) x) pos =
    (defaultPlacedApply uniquenessCheckStmt pos stmt `withDetism` SemiDet)
    `joinUniqueness` uniquenessCheckStmt (Or stmts x) pos
uniquenessCheckStmt (Not negated) pos =
    defaultPlacedApply uniquenessCheckStmt pos negated
uniquenessCheckStmt (TestBool exp) pos = uniquenessCheckExp exp pos
uniquenessCheckStmt Nop pos = return ()
uniquenessCheckStmt Fail pos = return ()
uniquenessCheckStmt (Loop body _) _ = uniquenessCheckStmts body
uniquenessCheckStmt (UseResources _ _ body) _ = uniquenessCheckStmts body
uniquenessCheckStmt (For generators body) pos = do
    mapM_ ((\gen -> do
            placedApply uniquenessCheckExp $ genExp gen
            placedApply uniquenessCheckExp $ loopVar gen
        ) . content) generators
    uniquenessCheckStmts body
uniquenessCheckStmt Break pos = return ()
uniquenessCheckStmt Next pos = return ()


-- | Uniqueness check the cases in a case statement.
uniquenessCheckCases :: (a -> Uniqueness ()) -> [(Placed Exp,a)] -> Maybe a
                     -> Uniqueness ()
uniquenessCheckCases f [] deflt = maybe (return ()) f deflt
uniquenessCheckCases f ((pexp, body):rest) deflt =
    (placedApply uniquenessCheckExp pexp `withDetism` SemiDet >> f body)
    `joinUniqueness` uniquenessCheckCases f rest deflt


-- | Uniqueness check an expression (recursively). When we see a use of a unique
-- variable, we add it to a dictionary (recording its type).  When we see a
-- subsequent use, we report an error.  When we see an assignment of a variable,
-- we remove it from the map, as that means we have not yet seen a use of that
-- value.  For an in/out flow, we treat this as first a use and then an
-- assignment.
uniquenessCheckExp :: Exp -> OptPos -> Uniqueness ()
uniquenessCheckExp (Typed (Var name ParamIn flowType) ty _) pos =
    variableUsed name pos ty flowType
uniquenessCheckExp (Typed (Var name ParamOut _) ty _) _ =
    variableAssigned name
uniquenessCheckExp (Typed (Var name ParamInOut flowType) ty _) pos = do
    variableUsed name pos ty flowType
    variableAssigned name
uniquenessCheckExp (Typed exp _ _) pos = uniquenessCheckExp exp pos
uniquenessCheckExp IntValue{} _ = return ()
uniquenessCheckExp FloatValue{} _ = return ()
uniquenessCheckExp CharValue{} _ = return ()
uniquenessCheckExp StringValue{} _ = return ()
uniquenessCheckExp var@Var{} _ =
    shouldnt $ "Untyped variable " ++ show var ++ " in uniqueness checking"
uniquenessCheckExp (Where stmts exp) pos = do
    uniquenessCheckStmts stmts
    defaultPlacedApply uniquenessCheckExp pos exp
uniquenessCheckExp (DisjExp e1 e2) pos =
    (defaultPlacedApply uniquenessCheckExp pos e1 `withDetism` SemiDet)
    `joinUniqueness` defaultPlacedApply uniquenessCheckExp pos e2
uniquenessCheckExp (CondExp stmt e1 e2) pos =
    (placedApply uniquenessCheckStmt stmt `withDetism` SemiDet
     >> placedApply uniquenessCheckExp e1)
    `joinUniqueness` placedApply uniquenessCheckExp e2
uniquenessCheckExp (Fncall _ _ exps) pos =
    mapM_  (placedApply uniquenessCheckExp) exps
uniquenessCheckExp (ForeignFn _ _ _ exps) pos =
    mapM_  (placedApply uniquenessCheckExp) exps
uniquenessCheckExp (CaseExp exp cases deflt) pos = do
    placedApply uniquenessCheckExp exp
    uniquenessCheckCases (placedApply uniquenessCheckExp) cases deflt


-- -- | Fold over the cases in a case expression
-- foldCaseExp :: (Placed Exp,Placed Exp) -> a
-- foldCaseExp sfn efn val (pexp, pval) =
--     placedApply (foldExp sfn efn (placedApply (foldExp sfn efn val) pexp)) pval


-- | Uniqueness check a parameter (including used resources) following checking
-- of the proc body.  This will catch unique outputs following use of the value.
uniquenessCheckParam :: ProcName -> OptPos -> Param -> Uniqueness ()
uniquenessCheckParam name pos (Param p ty flow flowType) = do
    used <- Map.member p <$> gets uniquenessUsedMap
    when  (flowsOut flow && used)
     $ uniquenessErr $ ReuseUnique p ty pos flowType (Just name)


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