--  File     : Resources.hs
--  Author   : Peter Schachte
--  Purpose  : Resource checker for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Resources (resourceCheckMod, canonicaliseProcResources,
                  transformProcResources, specialResourcesSet) where

import           AST
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.Tuple.HT (mapFst)
import           Data.Graph
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Maybe
import           Data.Set                  as Set
import           Options                   (LogSelection (Resources))
import           Snippets
import           Util


------------------------- Checking resource decls -------------------------

-- |Check a module's resource declarations.
resourceCheckMod :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
resourceCheckMod _ thisMod = do
    logResources $ "**** resource checking module " ++ showModSpec thisMod
    reenterModule thisMod
    resources <- getModuleImplementationField (Map.toAscList . modResources)
    (chg,errs,resources') <-
        unzip3 <$> mapM (uncurry checkResourceDef) resources
    updateModImplementation (\imp -> imp { modResources =
                                              Map.fromAscList resources'})
    reexitModule
    logResources $ "**** finished resource checking module "
                   ++ showModSpec thisMod
    return (or chg,concat errs)


checkResourceDef :: Ident -> ResourceDef 
                 -> Compiler (Bool,[(String,OptPos)],(Ident,ResourceDef))
checkResourceDef name def = do
    (chg,errs,m) <-
        unzip3 <$> mapM (uncurry checkOneResource) (Map.toList def)
    return (or chg, concat errs, (name,Map.fromList m))


checkOneResource :: ResourceSpec -> ResourceImpln 
                 -> Compiler (Bool,[(String,OptPos)],
                              (ResourceSpec,ResourceImpln))
checkOneResource rspec impln@(SimpleResource ty init pos) = do
    logResources $ "Check resource " ++ show rspec
                 ++ " with implementation " ++ show impln
    ty' <- lookupType "resource declaration" pos ty
    logResources $ "Actual type is " ++ show ty'
    return (ty' /= ty,[],(rspec,SimpleResource ty' init pos))
-- checkOneResource rspec Nothing = do
--     -- XXX don't currently handle compound resources
--     nyi "compound resources"


------------- Canonicalising resources in proc definitions ---------

-- |Make sure all resource for the specified proc are module qualified,
--  making them canonical.
canonicaliseProcResources :: ProcDef -> Int -> Compiler ProcDef
canonicaliseProcResources pd _ = do
    logResources $ "Canonicalising resources used by proc " ++ procName pd
    let proto = procProto pd
    let pos = procPos pd
    let resources = Set.elems $ procProtoResources proto
    resourceFlows <- Set.fromList 
                 <$> mapM (canonicaliseResourceFlow pos) resources
    logResources $ "Available resources: " ++ show resourceFlows
    let proto' = proto {procProtoResources = resourceFlows}
    let pd' = pd {procProto = proto'}
    logResources $ "Canonicalising resources results in:"
                    ++ showProcDef 4 pd'
    return pd'


canonicaliseResourceFlow :: OptPos -> ResourceFlowSpec
                         -> Compiler ResourceFlowSpec
canonicaliseResourceFlow pos spec = do
    resTy <- canonicaliseResourceSpec pos "proc declaration"
             $ resourceFlowRes spec
    return $ spec { resourceFlowRes = fst resTy }


--------- Transform resources into variables and parameters ---------

-- | Data type to store the necessary data for adding resources to a proc
data ResourceState = ResourceState {
    resTmpCtr  :: Int,
    resTmpVars :: VarDict
}


-- | Initial ResourceState given a tmpCtr
initResourceState :: Int -> ResourceState
initResourceState tmp = ResourceState tmp Map.empty


-- | State transformer using a ResourceState
type Resourcer = StateT ResourceState Compiler


-- |Transform resources into ordinary variables in a single procedure
--  definition.  Also check that calls to procs that use resources are
--  annotated with a ! to indicate resource usage.  This transformation
--  just blindly transforms resources into variables and parameters,
--  counting on the later variable use/def analysis to ensure that
--  resources are defined before they're used or returned.
--
-- Note that type checking of all called procedures must have been completed
-- before this can be done, because called procs are only resolved when this
-- proc is type checked.
transformProcResources :: ProcDef -> Int -> Compiler ProcDef
transformProcResources pd _ = do
    logResources "--------------------------------------\n"
    logResources $ "Adding resources to:" ++ showProcDef 4 pd
    let proto = procProto pd
    let pos = procPos pd
    let tmp = procTmpCount pd
    let resFlows = procProtoResources proto
    let params = procProtoParams proto
    let (ProcDefSrc body) = procImpln pd
    (body', resParams, tmp')
        <- evalStateT (transformProc resFlows body pos)
            $ initResourceState tmp
    let proto' = proto { procProtoParams = params ++ resParams}
    let pd' = pd { procProto = proto', procTmpCount = tmp',
                   procImpln = ProcDefSrc body' }
    logResources $ "Adding resources results in:" ++ showProcDef 4 pd'
    return pd'


-- | Transform a given procedure's body and resources, producing the body with
-- resources transformed into arguments, the additional parameters for resources
-- and the new tmpCtr 
transformProc :: Set ResourceFlowSpec -> [Placed Stmt] -> OptPos
              -> Resourcer ([Placed Stmt], [Param], Int)
transformProc resourceFlows body pos = do
    resFlows <- concat <$> mapM (simpleResourceFlows pos)
                           (Set.elems resourceFlows)
    lift $ logResources 
         $ "Declared resources: " ++ show resFlows
    body' <- transformStmts body
    resParams <- concat <$> mapM (resourceParams pos) resFlows
    tmp' <- gets resTmpCtr
    return (body', resParams, tmp')


-- | Transform a ResourceFlowSpec with a type into a Param
resourceParams :: OptPos -> (ResourceFlowSpec,TypeSpec) -> Resourcer [Param]
resourceParams pos (ResourceFlowSpec res flow, typ) = do
    varName <- resourceVar res
    let inParam  = [Param varName typ ParamIn (Resource res) | flowsIn flow]
    let outParam = [Param varName typ ParamOut (Resource res) | flowsOut flow]
    return $ inParam ++ outParam


-- | Transform a statement sequence, turning resources into arguments.
transformStmts :: [Placed Stmt] -> Resourcer [Placed Stmt]
transformStmts stmts = concat <$> mapM (placedApply transformStmt) stmts


-- | Transform a single statement, turning resources into arguments.
transformStmt :: Stmt -> OptPos -> Resourcer [Placed Stmt]
transformStmt stmt@(ProcCall m n id detism resourceful args) pos = do
    let procID = trustFromJust "transformStmt" id
    callResources <- procProtoResources . procProto
                 <$> lift (getProcDef $ ProcSpec m n procID generalVersion)
    unless (resourceful || Set.null callResources)
        $ lift $ errmsg pos
               $ "Call to resourceful proc without ! resource marker: "
                    ++ showStmt 4 stmt
    lift $ logResources 
         $ "Checking call to " ++ n ++ " using " ++ show callResources
    resArgs <- concat <$> mapM (resourceArgs pos) (Set.elems callResources)
    return [maybePlace
            (ProcCall m n (Just procID) detism False (args++resArgs)) pos]
transformStmt (ForeignCall lang name flags args) pos =
    return [maybePlace (ForeignCall lang name flags args) pos]
transformStmt stmt@(TestBool var) pos =
    return [maybePlace stmt pos]
transformStmt (And stmts) pos = do
    stmts' <- transformStmts stmts
    return [maybePlace (And stmts') pos]
transformStmt (Or [] _) pos =
    return [failTest]
transformStmt (Or [stmt] _) pos = do
    placedApplyM transformStmt stmt
transformStmt (Or (stmt:stmts) vars) pos = do
    stmt'  <- placedApplyM transformStmt stmt
    stmt'' <- transformStmt (Or stmts vars) pos
    tmpVars <- gets resTmpVars
    let vars' = Map.union tmpVars <$> vars
    return [maybePlace (Or [seqToStmt stmt', seqToStmt stmt''] vars') pos]
transformStmt (Not stmt) pos = do
    stmt' <- placedApplyM transformStmt stmt
    return [maybePlace (Not $ seqToStmt stmt') pos]
transformStmt Nop _ =
    return []
transformStmt Fail pos =
    return [maybePlace Fail pos]
transformStmt (Cond test thn els condVars defVars) pos = do
    test' <- placedApplyM transformStmt test
    thn'  <- transformStmts thn
    els'  <- transformStmts els
    tmpVars <- gets resTmpVars
    let condVars' = Map.union tmpVars <$> condVars
    let defVars'  = Map.union tmpVars <$> defVars
    return [maybePlace (Cond (Unplaced $ And test') thn' els'
                        condVars' defVars') pos]
transformStmt (Case expr cases deflt) pos = do
    cases' <- transformCases cases
    deflt' <- forM deflt transformStmts
    return [maybePlace (Case expr cases' deflt') pos]
transformStmt (Loop body defVars) pos = do
    body' <- transformStmts body
    tmpVars <- gets resTmpVars
    let defVars' = Map.union tmpVars <$> defVars
    return [maybePlace (Loop body' defVars') pos]
transformStmt (For generators body) pos = do
    body' <- transformStmts body
    return [maybePlace (For generators body') pos]
transformStmt (UseResources allRes oldRes body) pos = do
    let resVars = trustFromJust "use stmt without var list after type check"
                  oldRes
    resTypes <- List.filter ((`elem` resVars) . resourceName . fst)
            <$> lift (mapM (canonicaliseResourceSpec pos "use statement") allRes)
    toSave <- mapM (resourceVar . fst) resTypes
    tmp <- gets resTmpCtr
    let types = fromJust . snd <$> resTypes
    let tmpNames = mkTempName <$> [tmp..]
    let ress = zip3 toSave tmpNames types
    let get v ty = varGet v `withType` ty
    let set v ty = varSet v `withType` ty
    let saves = (\(r,t,ty) -> rePlace pos (move (get r ty) (set t ty))) <$> ress
    let restores = (\(r,t,ty) -> rePlace pos (move (get t ty) (set r ty)))
                   <$> ress
    let tmpVars = Map.fromList $ zip tmpNames types
    body' <- transformWithTmpVars (tmp + length toSave) tmpVars
           $ transformStmts body
    return $ saves ++ body' ++ restores
transformStmt Break pos =
    return [maybePlace Break pos]
transformStmt Next pos =
    return [maybePlace Next pos]


-- | Perform some action with additional tmp vars for resources.
-- This modifies the tmpCtr, but leaves the old tmp vars in tact. 
transformWithTmpVars :: Int -> VarDict -> Resourcer a -> Resourcer a
transformWithTmpVars tmp newVars action = do
    oldVars <- gets resTmpVars
    modify $ \s -> s{ resTmpCtr = tmp,
                      resTmpVars = Map.union newVars oldVars }
    result <- action
    modify $ \s -> s{ resTmpVars = oldVars }
    return result


-- Transform a list of cases, transforming resources into arguments
transformCases :: [(Placed Exp,[Placed Stmt])]
               -> Resourcer [(Placed Exp, [Placed Stmt])]
transformCases [] = return []
transformCases ((guard,body):rest) = do
    body' <- transformStmts body
    rest' <- transformCases rest
    return $ (guard,body'):rest'


-- |Returns the list of args corresponding to the specified resource
-- flow spec.  This produces up to two arguments for each simple
-- resource, multiplied by all the simple resources a single resource
-- flow spec might refer to.
resourceArgs :: OptPos -> ResourceFlowSpec -> Resourcer [Placed Exp]
resourceArgs pos rflow = do
    simpleSpecs <- simpleResourceFlows pos rflow
    -- XXX make separate exps for each direction
    concat <$>
         mapM (\(ResourceFlowSpec res flow,ty) -> do
                   var <- resourceVar res
                   let ftype = Resource res
                   let inExp = [Unplaced $
                                  Typed (Var var ParamIn ftype) ty Nothing
                               | flowsIn flow]
                   let outExp = [Unplaced $
                                 Typed (Var var ParamOut ftype) ty Nothing
                                | flowsOut flow]
                   return $ inExp ++ outExp)
         simpleSpecs


-- | The set of VarNames that correspond to sepcial resources
specialResourcesSet :: Set VarName
specialResourcesSet = keysSet specialResources


------------------------- General support code -------------------------

-- |Canonicalise a single resource spec, based on visible modules.  Report
-- unknown resource error in the specified context if resource or its type is
-- unknown.
canonicaliseResourceSpec :: OptPos -> String -> ResourceSpec
                         -> Compiler (ResourceSpec, Maybe TypeSpec)
canonicaliseResourceSpec pos context spec = do
    logResources $ "canonicalising resource " ++ show spec
    resDef <- lookupResource spec
    case resDef of
        Nothing -> do
            errmsg pos $ "Unknown resource " ++ show spec ++ " in " ++ context
            return (spec,Nothing)
        Just def ->
            case Map.assocs def of
                [(spec,impln)] -> do
                    let resType = resourceType impln
                    logResources $ "    to --> " ++ show resType
                    return (spec,Just resType)
                [] -> shouldnt $ "Empty resource " ++ show spec
                _ -> nyi $ "compound resource " ++ show spec


-- |Get a list of all the SimpleResources, and their types, referred
-- to by a ResourceFlowSpec.  This is necessary because a resource spec
-- may refer to a compound resource.
simpleResourceFlows :: OptPos -> ResourceFlowSpec ->
                       Resourcer [(ResourceFlowSpec,TypeSpec)]
simpleResourceFlows pos (ResourceFlowSpec spec flow) = do
    resDef <- lift $ lookupResource spec
    case resDef of
        Nothing -> do
            lift $ errmsg pos $ "Unknown resource " ++ show spec
                             ++ " in called proc"
            return []
        Just def ->
            return [(ResourceFlowSpec spec flow,resourceType impln)
                    | (spec,impln) <- Map.toList def]


-- | The local variable name to use for a resource.  This assumes the resource
-- spec has already been canonicalised (fully module qualified).
resourceVar :: ResourceSpec -> Resourcer Ident
resourceVar (ResourceSpec [] name) = return name
resourceVar (ResourceSpec mod name) = do
    -- Always use resource name as variable name, regardless of module
    -- XXX This could cause collisions!
    return name


-- |Log a message, if we are logging resource transformation activity.
logResources :: String -> Compiler ()
logResources s = logMsg Resources s
