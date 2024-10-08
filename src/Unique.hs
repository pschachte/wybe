--  File     : Unique.hs
--  Purpose  : The unique typing system for Wybe
--  Copyright: (c)
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
-- This module defines the unique typing system for Wybe.


module Unique (uniquenessCheckProc) where

import AST
import Resources
import Util
import Options
import Control.Monad
import Control.Monad.Trans       (lift)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Extra       (whenM)
import Data.List                 as List
import Data.Set                  as Set
import Data.Map                  as Map
import Data.Maybe
import Data.Tuple.HT             (mapFst, swap)
import qualified Data.ByteString.Builder.Prim as Set


-- | Uniqueness error with specs of the variable
data UniquenessError = UniquenessError {
        errVarName  :: VarName,     -- ^ Variable with a uniqueness error
        errTypeSpec :: TypeSpec,    -- ^ Type of the variable
        errPos      :: OptPos,      -- ^ Source position of the variable or expr
        errFlowType :: ArgFlowType, -- ^ The flow type (variable or resource)
        errKind     :: UniquenessErrorKind
                                    -- ^ The kind of error
    }
    | UniqueGenericError {
        errGenMod      :: ModSpec,  -- ^ The module of the callee
        errGenProc     :: ProcName, -- ^ The callee proc
        errGenPos      :: OptPos,   -- ^ Source possiton of the callee
        errGenType     :: TypeSpec, -- ^ The type that is unique
        errGenTypeKind :: UniquenessGenericKind
                                    -- ^ The kind of generic error
    }
 deriving Show


data UniquenessErrorKind
    = ErrorReuse               -- ^ Reuse of variable without intervening assignment
    | ErrorReturn ProcName     -- ^ Variable returned after being used
    | ErrorDetism Determinism  -- ^ Variable assigned in non-deterministic contxt
    | ErrorClosed              -- ^ Closure over a unique variable
  deriving (Eq, Show)

data UniquenessGenericKind
    = ErrorCallBinding Bool TypeVarName -- ^ Call binds type variable to a generic
                                        -- type. The boolean indicates if this is
                                        -- from a partial application
    | ErrorParamType VarName            -- ^ Parameter binds a type parameter to
                                        -- a generic type
  deriving (Eq, Show)

-- | State used to check correctness of uniqueness of the program
data UniquenessState = UniquenessState {
    -- |The variables used so far in the current scope, with their types.
    uniquenessUsedMap :: VarDict,
    -- |The uniqueness errors seen so far.
    uniquenessErrors  :: [UniquenessError],
    -- |Whether to excuse (not report as an error) subsequent uses of a unique
    -- variable.  Uses and assignments are still treated as such, but reuses are
    -- not reported when this is True.
    uniquenessForgive :: Bool,
    -- |The maximum determinism allowed in the current scope.  Assignment to
    -- unique variables is not allowed outside a deterministic scope.
    uniquenessDetism  :: Determinism
} deriving (Show)


-- | Return an initial state for uniqueness checker
initUniquenessState :: Determinism -> UniquenessState
initUniquenessState = UniquenessState Map.empty [] False


-- | Check correctness of uniqueness for a procedure
uniquenessCheckProc :: ProcDef -> Int -> Compiler ProcDef
uniquenessCheckProc def _ = do
    let name = procName def
    let pos = procPos def
    logMsg Uniqueness $ "Uniqueness checking " ++ showProcName name
    let detism = procDetism def
    let params = procProtoParams $ procProto def
    let ress = procProtoResources $ procProto def
    logMsg Uniqueness $ "with params:    " ++ show params
    logMsg Uniqueness $ "with resources: " ++ show ress
    -- XXX this only considers whether arguments are unique, ignoring direction
    -- of flow.  When users can declare their own unique types, this won't work.
    someUniqueParam <- elem (Just True) <$>
                       mapM (((tmUniqueness . typeModifiers . modInterface <$>) <$>)
                             <$> getLoadingModule)
                           (catMaybes $ typeModule . paramType . content <$> params)
    resTys <- mapM (canonicaliseResourceSpec pos "uniqueness checking" . resourceFlowRes) ress
    someUniqueRes <- elem (Just True) <$>
                     mapM (((tmUniqueness . typeModifiers . modInterface <$>) <$>)
                           <$> getLoadingModule)
                         (catMaybes $ typeModule . trustFromJust "unique res ty" . snd 
                            <$> resTys)
    unless (detism `determinismLEQ` Det) $ do
        when someUniqueRes $
            errmsg pos $ name ++ " with unique parameter(s) can fail"
        when someUniqueRes $
            errmsg pos $ name ++ " with unique resource(s) can fail"
    isUnique <- getModule (tmUniqueness . typeModifiers . modInterface)
    when (isConstructorVariant (procVariant def) && not isUnique)
      $ mapM_ (placedApply checkNoNestedUnique) $ procProtoParams $ procProto def
    case procImpln def of
        ProcDefSrc body -> do
            state <- uniquenessCheckDef name pos detism body params ress
            logMsg Uniqueness $ "After checking params: " ++ show state
            mapM_ reportUniquenessError $ reverse $ uniquenessErrors state
            return def
        _ -> shouldnt $ "Uniqueness check of non-source proc def "
                        ++ show (procName def)


-- | Check that the specified parameter is not a unique-typed input.  If it is,
-- report that a member of a non-unique type is unique.
checkNoNestedUnique :: Param -> OptPos -> Compiler ()
checkNoNestedUnique member pos =
    when (flowsIn $ paramFlow member) $ do
        let ty = paramType member
        ty' <- lookupType "uniqueness" pos ty
        case typeModule ty' of
            Nothing -> return ()
            Just mod -> do
                isUnique <- getSpecModule "checkNoNestedUnique"
                            (tmUniqueness . typeModifiers . modInterface) mod
                when isUnique
                  $ errmsg pos $ "Unique constructor argument " ++ paramName member
                                 ++ " of non-unique type"




----------------------------------------------------------------
--               The Uniqueness Checker Monad
----------------------------------------------------------------

-- |The Uniqueness monad is a state transformer monad carrying the
--  uniqueness state over the compiler monad.

type Uniqueness = StateT UniquenessState Compiler


-- | Log a message, if we are logging uniqueness checker activity.
logUniqueness :: String -> Uniqueness ()
logUniqueness msg = do
    detism <- gets uniquenessDetism
    lift $ logMsg Uniqueness $ "(" ++ show detism ++ ") " ++ msg


uniquenessCheckDef :: ProcName -> OptPos -> Determinism -> [Placed Stmt]
                   -> [Placed Param] -> [ResourceFlowSpec] -> Compiler UniquenessState
uniquenessCheckDef name pos detism body params res =
    execStateT (do
        uniquenessCheckStmts body
        mapM_ (placedApply $ uniquenessCheckParam name) params
        mapM_ (uniquenessCheckResourceParam name pos) res
    ) $ initUniquenessState detism


-- | Note a variable use, reporting an error if it has already been used.
variableUsed :: VarName -> OptPos -> TypeSpec -> ArgFlowType -> Uniqueness ()
variableUsed name pos ty flowType = do
    logUniqueness $ "Variable " ++ name ++ " used"
    alreadyUsed <- Map.member name <$> gets uniquenessUsedMap
    when alreadyUsed
      $ uniquenessErr $ UniquenessError name ty pos flowType ErrorReuse
    isUnique <- lift $ typeIsUnique ty
    when isUnique
      $ modify $ \st -> st {uniquenessUsedMap = Map.insert name ty
                                                $ uniquenessUsedMap st }


-- | Note a variable use, reporting an error if it has already been used.
variableAssigned :: VarName -> OptPos -> TypeSpec -> ArgFlowType -> Uniqueness ()
variableAssigned name pos ty fType = do
    logUniqueness $ "Variable " ++ name ++ " assigned"
    modify $ \st -> st {uniquenessUsedMap = Map.delete name
                                            $ uniquenessUsedMap st }
    detism <- gets uniquenessDetism
    isUnique <- lift $ typeIsUnique ty
    unless (detism `determinismLEQ` Det || not isUnique)
      $ uniquenessErr $ UniquenessError name ty pos fType $ ErrorDetism detism


-- | Report a uniqueness error
uniquenessErr :: UniquenessError -> Uniqueness ()
uniquenessErr err = do
    forgive <- gets uniquenessForgive
    if forgive && errKind err == ErrorReuse
        then logUniqueness $ "Forgive error: " ++ show err
        else do
            logUniqueness $ "Recording error: " ++ show err
            modify $ \st -> st { uniquenessErrors = err : uniquenessErrors st }


-- | Run a uniqueness checker in a context with the specified determinism.
withDetism :: Uniqueness a -> Determinism -> Uniqueness a
withDetism checker detism = do
    oldDetism <- gets uniquenessDetism
    logUniqueness $ "setting detism to " ++ show detism
    modify $ \state -> state { uniquenessDetism = detism }
    result <- checker
    logUniqueness $ "setting detism to " ++ show oldDetism
    modify $ \state -> state { uniquenessDetism = oldDetism }
    return result


-- | Run a uniqueness checker without reporting reuse errors.
forgivingly :: Bool -> Uniqueness a  -> Uniqueness a
forgivingly forgive checker = do
    oldForgiving <- gets uniquenessForgive
    let newForgiving = forgive || oldForgiving
    logUniqueness $ "begin forgiving (" ++ show newForgiving
                    ++ ", was " ++ show oldForgiving  ++ ")"
    modify $ \state -> state { uniquenessForgive = newForgiving }
    result <- checker
    logUniqueness $ "returning forgiving to " ++ show oldForgiving
    modify $ \state -> state { uniquenessForgive = oldForgiving }
    return result


-- | Combine two uniqueness computations into a uniqueness computation.
-- The resulting computation includes all the errors from both, and takes
-- the more conservative binding state
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
                   `Map.union` uniquenessUsedMap secondState
    let joinForgiveness = uniquenessForgive firstState
                          && uniquenessForgive secondState
    put $ UniquenessState joinUsed allErrs joinForgiveness
                          $ uniquenessDetism initial


-- | Uniqueness check a statement sequence
uniquenessCheckStmts :: [Placed Stmt] -> Uniqueness ()
uniquenessCheckStmts = mapM_ $ placedApply uniquenessCheckStmt


-- | Uniqueness check a single statement
uniquenessCheckStmt :: Stmt -> OptPos -> Uniqueness ()
uniquenessCheckStmt call@(ProcCall (First mod name mbId) _ _ args) pos = do
    logUniqueness $ "Uniqueness checking call " ++ show call
    mapM_ (defaultPlacedApply uniquenessCheckExp pos) args
    let id = trustFromJust "uniquenessCheckStmt" mbId
    let pspec = ProcSpec mod name id generalVersion
    def <- lift $ getProcDef pspec
    let proto = procProto def
    let params = procProtoParams proto
    zipWithM_ (uniquenessCheckArg mod name pos) (content <$> params) (content <$> args)
    mapM_ (uniquenessCheckResourceArg pos) $ procProtoResources proto
uniquenessCheckStmt call@(ProcCall (Higher fn) _ _ args) pos = do
    logUniqueness $ "Uniqueness checking higher call " ++ show call
    mapM_ (defaultPlacedApply uniquenessCheckExp pos) $ fn:args
uniquenessCheckStmt call@(ForeignCall _ _ flags args) pos = do
    let forgiving = "unique" `elem` flags
    logUniqueness $ "Uniqueness checking foreign call " ++ show call
    forgivingly forgiving
        $ mapM_ (defaultPlacedApply uniquenessCheckExp pos) args
uniquenessCheckStmt stmt@(Cond tst thn els _ _ _) pos = do
    logUniqueness $ "Uniqueness checking conditional " ++ show stmt
    (defaultPlacedApply uniquenessCheckStmt pos tst `withDetism` SemiDet
       >> uniquenessCheckStmts thn)
     `joinUniqueness` uniquenessCheckStmts els
uniquenessCheckStmt (Case exp cases deflt) pos = do
    defaultPlacedApply uniquenessCheckExp pos exp
    uniquenessCheckCases uniquenessCheckStmts cases deflt
uniquenessCheckStmt (And stmts) _ = uniquenessCheckStmts stmts
uniquenessCheckStmt (Or [] _ _) pos = return ()
uniquenessCheckStmt (Or [stmt] _ _) pos =
    defaultPlacedApply uniquenessCheckStmt pos stmt
uniquenessCheckStmt (Or (stmt:stmts) vars res) pos =
    (defaultPlacedApply uniquenessCheckStmt pos stmt `withDetism` SemiDet)
    `joinUniqueness` uniquenessCheckStmt (Or stmts vars res) pos
uniquenessCheckStmt (Not negated) pos =
    defaultPlacedApply uniquenessCheckStmt pos negated
uniquenessCheckStmt (TestBool exp) pos = uniquenessCheckExp exp pos
uniquenessCheckStmt Nop pos = return ()
uniquenessCheckStmt Fail pos = return ()
uniquenessCheckStmt (Loop body _ _) _ = uniquenessCheckStmts body
uniquenessCheckStmt (UseResources res _ body) pos = do
    -- resource is implicitly stored before block
    mapM_ (uniquenessCheckResourceArg pos . (`ResourceFlowSpec` ParamIn)) res 
    uniquenessCheckStmts body
    -- resource is implicitly restored before block
    mapM_ (uniquenessCheckResourceArg pos . (`ResourceFlowSpec` ParamOut)) res 
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
uniquenessCheckExp (Typed (Var name ParamOut flowType) ty _) pos =
    variableAssigned name pos ty flowType
uniquenessCheckExp (Typed (Var name ParamInOut flowType) ty _) pos = do
    variableUsed name pos ty flowType
    variableAssigned name pos ty flowType
uniquenessCheckExp (Typed (Closure pspec clsd) ty _) pos = do
    uniquenessCheckClosure pspec pos clsd ty
uniquenessCheckExp (Typed exp _ _) pos = uniquenessCheckExp exp pos
uniquenessCheckExp IntValue{} _ = return ()
uniquenessCheckExp FloatValue{} _ = return ()
uniquenessCheckExp CharValue{} _ = return ()
uniquenessCheckExp StringValue{} _ = return ()
uniquenessCheckExp var@Var{} _ =
    shouldnt $ "Untyped variable " ++ show var ++ " in uniqueness checking"
uniquenessCheckExp FailExpr _ = return ()
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
uniquenessCheckExp (Fncall _ _ _ exps) pos =
    mapM_  (placedApply uniquenessCheckExp) exps
uniquenessCheckExp (ForeignFn _ _ _ exps) pos =
    mapM_  (placedApply uniquenessCheckExp) exps
uniquenessCheckExp (CaseExp exp cases deflt) pos = do
    placedApply uniquenessCheckExp exp
    uniquenessCheckCases (placedApply uniquenessCheckExp) cases deflt
uniquenessCheckExp var@(AnonParamVar _ _) _ =
    shouldnt $ "AnonParamVar " ++ show var ++ " in uniqueness checking"
uniquenessCheckExp (AnonProc mods params body clsd _) pos = do
    uniquenessCheckClosedMap clsd pos
    errs <- uniquenessErrors 
        <$> lift (uniquenessCheckDef "anonymous procedure" pos
                    (modifierDetism mods) body 
                    ((`maybePlace` pos) <$> params) [])
    mapM_ uniquenessErr errs
uniquenessCheckExp func@(AnonFunc _) _ = 
    shouldnt $ "AnonFunc " ++ show func ++ " in uniqueness checking"
uniquenessCheckExp (Global _) _ = return ()
uniquenessCheckExp ref@(Closure _ clsd) _ =
    shouldnt $ "Untyped Closure " ++ show ref ++ " in uniqueness checking"


-- Uniqueness check an argument of a call, ensuring that no argument binds a
-- unique type to a generic type
uniquenessCheckArg :: ModSpec -> ProcName -> OptPos -> Param -> Exp -> Uniqueness ()
uniquenessCheckArg mod name pos Param{paramType=paramTy} (Typed _ argTy _) =
    uniquenessCheckGeneric False mod name pos argTy paramTy
uniquenessCheckArg _ _ _ _ _ = return ()


uniquenessCheckResourceArg :: OptPos -> ResourceFlowSpec -> Uniqueness ()
uniquenessCheckResourceArg pos (ResourceFlowSpec res flow) = do
    let name = resourceName res
        flowType = Resource res
    ty <- lift $ trustFromJust "uniquenessCheckResource" . snd 
        <$> canonicaliseResourceSpec pos "uniqueness checking" res
    uniquenessCheckExp (Typed (Var name flow flowType) ty Nothing) pos 
    
-- Uniqueness check an argument of a call, ensuring that no argument binds a
-- unique type to a generic type
uniquenessCheckClosure :: ProcSpec -> OptPos -> [Placed Exp] -> TypeSpec -> Uniqueness ()
uniquenessCheckClosure pspec@(ProcSpec mod name _ _) pos clsd (HigherOrderType _ tfs) = do
    params <- lift $ procProtoParams . procProto <$> getProcDef pspec
    zipWithM_ (uncurry $ uniquenessCheckGeneric True mod name) 
          (swap . mapFst paramType . unPlace <$> params)
        $ (fromMaybe AnyType . maybeExpType . content <$> clsd) ++ (typeFlowType <$> tfs)
    mapM_ (placedApply uniquenessCheckClosedVariable) clsd
uniquenessCheckClosure _ _ _ ty =
    shouldnt $ "uniquenessCheckClosure on type " ++ show ty

uniquenessCheckGeneric :: Bool -> ModSpec -> ProcName -> OptPos
                       -> TypeSpec -> TypeSpec -> Uniqueness ()
uniquenessCheckGeneric partial mod name pos ty (TypeVariable var) =
    whenM (lift $ typeIsUnique ty)
        $ uniquenessErr $ UniqueGenericError mod name pos ty
                        $ ErrorCallBinding partial var
uniquenessCheckGeneric partial mod name pos (TypeVariable var) ty =
    whenM (lift $ typeIsUnique ty)
        $ uniquenessErr $ UniqueGenericError mod name pos ty
                        $ ErrorCallBinding partial var
uniquenessCheckGeneric partial mod name pos
        (TypeSpec _ _ tys1) (TypeSpec _ _ tys2) =
    zipWithM_ (uniquenessCheckGeneric partial mod name pos) tys1 tys2
uniquenessCheckGeneric partial mod name pos
        (HigherOrderType _ tfs1) (HigherOrderType _ tfs2) =
    zipWithM_ (uniquenessCheckGeneric partial mod name pos)
        (typeFlowType <$> tfs1) (typeFlowType <$> tfs2)
uniquenessCheckGeneric _ _ _ _ _ _ = return ()

-- | Uniqueness check a parameter (including used resources) following checking
-- of the proc body.  This will catch unique outputs following use of the value.
uniquenessCheckParam :: ProcName -> Param -> OptPos -> Uniqueness ()
uniquenessCheckParam name (Param pName ty flow flowType) pos = do
    used <- Map.member pName <$> gets uniquenessUsedMap
    when (flowsOut flow && used)
        $ uniquenessErr $ UniquenessError pName ty pos flowType (ErrorReturn name)
    uniquenessCheckParamType name pos pName ty

    
uniquenessCheckResourceParam :: ProcName -> OptPos -> ResourceFlowSpec -> Uniqueness ()
uniquenessCheckResourceParam name pos (ResourceFlowSpec res flow) = do
    let rName = resourceName res
        flowType = Resource res
    ty <- lift $ trustFromJust "uniquenessCheckResource" . snd 
        <$> canonicaliseResourceSpec pos "uniqueness checking" res
    uniquenessCheckParam name (Param rName ty flow flowType) pos


-- | Uniqueness check the type of a parameter. This ensures that type parameters
-- are all non-unique
uniquenessCheckParamType :: ProcName -> OptPos -> VarName -> TypeSpec -> Uniqueness ()
uniquenessCheckParamType procName pos paramName TypeSpec{typeParams=params} = do
    mapM_ (uniquenessCheckTypeParam procName pos paramName) params
uniquenessCheckParamType procName pos paramName (HigherOrderType _ tfs) =
    mapM_ (uniquenessCheckParamType procName pos paramName . typeFlowType) tfs
uniquenessCheckParamType _ _ _ _ = return ()


-- | Uniqueness check the type of a type parameter, ensuring the parateter is
-- non-unique
uniquenessCheckTypeParam :: ProcName -> OptPos -> VarName -> TypeSpec -> Uniqueness ()
uniquenessCheckTypeParam procName pos paramName ty@TypeSpec{typeParams=params} = do
    whenM (lift $ typeIsUnique ty)
        $ uniquenessErr $ UniqueGenericError [] procName pos ty (ErrorParamType paramName)
    mapM_ (uniquenessCheckParamType procName pos paramName) params
uniquenessCheckTypeParam procName pos paramName (HigherOrderType _ tfs) =
    mapM_ (uniquenessCheckParamType procName pos paramName . typeFlowType) tfs
uniquenessCheckTypeParam _ _ _ _ = return ()


-- Ensure that no closed Variable contained within the VarDict is unique
uniquenessCheckClosedMap :: Maybe VarDict -> OptPos -> Uniqueness ()
uniquenessCheckClosedMap Nothing _ = return ()
uniquenessCheckClosedMap (Just vars) pos =
    mapM_ (placedApply uniquenessCheckClosedVariable)
        $ (\(nm,ty) -> Typed (Var nm ParamIn Free) ty Nothing `maybePlace` pos)
       <$> Map.toList vars

uniquenessCheckClosedVariable :: Exp -> OptPos -> Uniqueness ()
uniquenessCheckClosedVariable (Typed (Var name fl ft) ty _) pos = do
    whenM (lift $ typeIsUnique ty)
        $ uniquenessErr $ UniquenessError name ty pos ft ErrorClosed
uniquenessCheckClosedVariable _ _ = return ()


-- | Report an error when a unique typed variable is being reused
reportUniquenessError :: UniquenessError -> Compiler ()
reportUniquenessError (UniquenessError name ty pos flow ErrorReuse) = do
    errmsg pos $ "Reuse of unique " ++ flowKind flow name ty
reportUniquenessError (UniquenessError name ty pos flow (ErrorReturn proc)) = do
    errmsg pos $ "Unique " ++ flowKind flow name ty ++ " live at end of "
                 ++ showProcName proc
reportUniquenessError (UniquenessError name ty pos flow (ErrorDetism detism)) = do
    errmsg pos $ "Unique " ++ flowKind flow name ty ++ " assigned in a "
                 ++ determinismName detism ++ " context"
reportUniquenessError (UniquenessError name ty pos flow ErrorClosed) = do
    errmsg pos $ "Cannot close over a unique " ++ flowKind flow name ty
reportUniquenessError (UniqueGenericError mod name pos ty (ErrorCallBinding partial tyVar)) = do
    errmsg pos $ (if partial then "Partial application of "
                  else "Call to ") ++ maybeModPrefix mod ++ name ++ " binds "
                 ++ genericTypeVar tyVar ++ " to unique type " ++ show ty
reportUniquenessError (UniqueGenericError mod name pos ty (ErrorParamType param)) = do
    errmsg pos $ "Parameter " ++ param ++ " of " ++ name
                 ++ " has type with unique type parameter " ++ show ty

-- | Give a human-readable description of reused variable (may be a resource).
flowKind :: ArgFlowType -> VarName -> TypeSpec -> String
flowKind (Resource res) _ _ = "resource " ++ show res
flowKind _ name ty          = "variable " ++ name ++ ":" ++ show ty

-- | Give a human-readable description of type variable name
genericTypeVar :: TypeVarName -> String
genericTypeVar (RealTypeVar var) = "type variable " ++ var
genericTypeVar (FauxTypeVar _)   = "inferred variable type"
