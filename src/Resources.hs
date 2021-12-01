--  File     : Resources.hs
--  Author   : Peter Schachte
--  Purpose  : Resource checker for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Resources (resourceCheckMod, canonicaliseProcResources, 
                  canonicaliseResourceSpec, transformProcResources,
                  specialResourcesSet) where

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
import           Data.Tuple.HT             (mapFst, mapSnd)
import           Options                   (LogSelection (Resources))
import           Snippets
import           Util
import Debug.Trace


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
    -- let errs = [("Higher-order resource cannot have '" 
    --              ++ resourcefulName Resourceful++ "' modifier", pos)
    --            | isResourcefulHigherOrder ty']
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
    resTypes         :: Set ResType,
    resTmpVars       :: VarDict,
    resIsResourceful :: Bool,
    resTmpCtr        :: Int
}


-- | Initial ResourceState given a tmpCtr
initResourceState :: Int -> ResourceState
initResourceState = ResourceState Set.empty Map.empty  False 


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
    let ProcDefSrc body = procImpln pd
    let hasHigherResources = any (isResourcefulHigherOrder . paramType) params
    logResources $ "Declared resources: " ++ show resFlows
    (body', resFlows', resParams, tmp')
        <- evalStateT (transformProc hasHigherResources resFlows body pos)
            $ initResourceState tmp
    thisMod <- getModuleSpec
    pd' <- if List.null thisMod && procName pd == "" 
           then do 
                let inRes = List.filter (flowsIn . resourceFlowFlow . fst) resFlows'
                let body'' = (storeResource . mapFst resourceFlowRes <$> inRes)
                          ++ dropWhile (isGlobalLoad . content) 
                             (takeWhile (not . isGlobalStore . content) body')
                let params' = concatMap resourceParams resFlows'
                let proto' = proto { procProtoParams=params' ++ [globalsParam]}
                return $ pd { procProto=proto', procTmpCount=tmp',
                              procImpln=ProcDefSrc body'' }
           else do 
                let proto' = proto { procProtoParams=params ++ resParams }
                return pd { procProto=proto', procTmpCount=tmp',
                            procImpln=ProcDefSrc body' }
    logResources $ "Adding resources results in:" ++show tmp' ++ showProcDef 4 pd'
    return pd'

partitionSpecials :: (a -> ResourceFlowSpec) -> [a] 
                  -> ([a],[a])
partitionSpecials toResFlowSpec = 
    List.partition ((List.null . resourceMod 
                     &&& (`Set.member` specialResourcesSet) . resourceName) 
                    . resourceFlowRes . toResFlowSpec)

isGlobalLoad :: Stmt -> Bool
isGlobalLoad (ForeignCall "lpvm" "load" _ _) = True
isGlobalLoad _                               = False

isGlobalStore :: Stmt -> Bool
isGlobalStore (ForeignCall "lpvm" "store" _ _) = True
isGlobalStore _                                = False


-- | Transform a ResourceFlowSpec with a type into a Param
resourceParams :: (ResourceFlowSpec,TypeSpec) -> [Param]
resourceParams (ResourceFlowSpec res flow, typ) = 
    let varName  = resourceVar res
        inParam  = [Param varName typ ParamIn (Resource res) | flowsIn flow]
        outParam = [Param varName typ ParamOut (Resource res) | flowsOut flow]
    in  inParam ++ outParam


globalsResType :: (Ident,TypeSpec) 
globalsResType = (globalsName,phantomType) 


-- | Transform a given procedure's body and resources, producing the body with
-- resources transformed into arguments, the additional parameters for resources
-- and the new tmpCtr 
transformProc :: Bool -> Set ResourceFlowSpec -> [Placed Stmt] -> OptPos
              -> Resourcer ([Placed Stmt], [(ResourceFlowSpec,TypeSpec)], [Param], Int)
transformProc hasHigher resourceFlows body pos = do
    resFlows <- concat <$> mapM (simpleResourceFlows pos)
                           (Set.elems resourceFlows)
    let (specials, resFlows') = partitionSpecials fst resFlows
    let isResourceful = hasHigher || not (List.null resFlows')
    modify $ \s -> s{resTypes=Set.fromList $ mapFst resourceFlowRes <$> resFlows',
                     resIsResourceful=isResourceful}
    lift $ logResources $ "Declared resources: " ++ show resFlows
    body' <- transformStmts body
    tmp' <- gets resTmpCtr
    return (body', resFlows, concatMap resourceParams specials
                             ++ [globalsParam | isResourceful], tmp')

type ResType = (ResourceSpec, TypeSpec)

    
-- | Transform a statement sequence, turning resources into arguments.
transformStmts :: [Placed Stmt] -> Resourcer [Placed Stmt]
transformStmts stmts = concat <$> mapM (placedApply transformStmt) stmts


-- | Transform a single statement, turning resources into arguments.
transformStmt :: Stmt -> OptPos -> Resourcer [Placed Stmt]
transformStmt stmt@(ProcCall func@(First m n mbId) detism resourceful args) pos = do
    let procID = trustFromJust "transformStmt" mbId
    callResFlows <-
        Set.toList . procProtoResources . procProto 
        <$> lift (getProcDef $ ProcSpec m n procID generalVersion)
    let argTys = fromMaybe AnyType . maybeExpType . content <$> args
    let hasResfulHigherArgs = any isResourcefulHigherOrder argTys
    let usesResources = not (List.null callResFlows) || hasResfulHigherArgs
    unless (resourceful || not usesResources)
        $ lift $ errmsg pos
               $ "Call to resourceful proc without ! resource marker: "
                    ++ showStmt 4 stmt
    lift $ logResources $ "Checking call to " ++ n ++ " using " ++ show callResFlows
    (args', inRes, outRes) <- transformExps args 
    let (specialRes,globalRes) = partitionSpecials id callResFlows
    specialArgs <- concat <$> mapM (resourceArgs pos) specialRes
    let usesGlobals = not (List.null globalRes) || hasResfulHigherArgs
    let stmt' = [maybePlace (ProcCall func detism False 
                             $ args' ++ specialArgs 
                                     ++ if usesGlobals then globalsGetSet else []) pos]
    return $ loadStoreResources inRes outRes stmt'
transformStmt stmt@(ProcCall (Higher func) detism resourceful args) pos = do
    (func':args', inRes, outRes) <- transformExps $ func:args 
    case content func' of
        Typed _ (HigherOrderType ProcModifiers{modifierResourceful=Resourceful} _) _ -> do
            unless resourceful
                $ lift $ errmsg pos
                    $ "Resourceful higher order call without ! resource marker: "
                            ++ showStmt 4 stmt
            return $ loadStoreResources inRes outRes 
                        [maybePlace (ProcCall (Higher func') detism False 
                                    $ args' ++ globalsGetSet) pos]
        Typed _ (HigherOrderType _ _) _ ->
            return $ loadStoreResources inRes outRes 
                      [maybePlace (ProcCall (Higher func') detism False args') pos]
        _ -> shouldnt $ "bad resource higher call type" ++ show stmt 
transformStmt (ForeignCall lang name flags args) pos = do
    (args', inRes, outRes) <- transformExps args
    return (loadStoreResources inRes outRes 
            [maybePlace (ForeignCall lang name flags args') pos])
transformStmt (TestBool var) pos = do
    (var', inRes, outRes) <- transformExp AnyType var Nothing
    return $ loadStoreResources inRes outRes 
              [maybePlace (TestBool $ content var') pos]
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
    vars'  <- forM vars resourcelessVarDict
    return $ [maybePlace (Or [seqToStmt stmt',seqToStmt stmt''] vars')
              pos]
transformStmt (Not stmt) pos = do
    stmt' <- placedApplyM transformStmt stmt
    return [maybePlace (Not $ seqToStmt stmt') pos]
transformStmt Nop _ =
    return []
transformStmt Fail pos =
    return [maybePlace Fail pos]
transformStmt (Cond test thn els condVars defVars) pos = do
    test' <- placedApplyM transformStmt test
    thn' <- transformStmts thn
    els' <- transformStmts els
    condVars'  <- forM condVars resourcelessVarDict
    defVars'  <- forM defVars resourcelessVarDict
    return [maybePlace
             (Cond (Unplaced $ And test') thn' els' condVars' defVars') pos]
transformStmt (Case expr cases deflt) pos = do
    cases' <- transformCases cases
    deflt' <- forM deflt transformStmts
    return [maybePlace (Case expr cases' deflt') pos]
transformStmt (Loop body vars) pos = do
    body' <- transformStmts body
    vars'  <- forM vars resourcelessVarDict
    return [maybePlace (Loop body' vars') pos]
transformStmt (For generators body) pos = do
    body' <- transformStmts body
    return [maybePlace (For generators body') pos]
transformStmt (UseResources allRes oldRes body) pos = do
    resMbTypes <- lift (mapM (canonicaliseResourceSpec pos "use statement") allRes)
    let resTypes = mapSnd (trustFromJust "transformStmt UseResources")
               <$> resMbTypes 
    (saves, restores, tmpVars) <- saveRestoreResourcesTmp resTypes
    body' <- transformWithTmpVars tmpVars $ transformStmts body
    return $ saves ++ body' ++ restores
transformStmt Break pos =
    return [maybePlace Break pos]
transformStmt Next pos =
    return [maybePlace Next pos]


-- | Get a var as a resource of the given type
getResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
getResource nm (rs, ty) = varGet nm `withType` ty `setExpFlowType` Resource rs


-- | Set a var as a resource of the given type
setResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
setResource nm (rs, ty) = varSet nm `withType` ty `setExpFlowType` Resource rs


-- | Save and restore the given resources in tmp variables
saveRestoreResourcesTmp :: [ResType] 
                        -> Resourcer ([Placed Stmt], [Placed Stmt], VarDict)
saveRestoreResourcesTmp resTys = do
    tmp <- gets resTmpCtr
    let tmpVars = mkTempName <$> [tmp..]
        ress = zip tmpVars resTys
        save (t,(rs,ty)) = globalLoad rs ty $ setResource t (rs,ty)
        restore (t,(rs,ty)) = globalStore rs ty $ getResource t (rs,ty)
    modify $ \s -> s{resTmpCtr=tmp + length ress}
    return (save <$> ress, restore <$> ress, 
            Map.fromList $ zip tmpVars (snd <$> resTys))


-- | Store the given resource in globals
storeResource :: (ResourceSpec, TypeSpec) -> Placed Stmt
storeResource rsTy@(rs,ty) = 
    globalStore rs ty (getResource (resourceName rs) rsTy)


-- | Load the given resource from globals
loadResource :: (ResourceSpec, TypeSpec) -> Placed Stmt
loadResource rsTy@(rs,ty) = 
    globalLoad rs ty (setResource (resourceName rs) rsTy)


-- | Surround a given list of statements with loads/stores to the given 
-- resourcces 
loadStoreResources :: Set ResType -> Set ResType 
                   -> [Placed Stmt] -> [Placed Stmt]
loadStoreResources inRes outRes stmts =
    (loadResource <$> Set.toList inRes)
    ++ stmts ++ 
    (storeResource <$> Set.toList outRes)


-- | Remove the variables corresponding to 
resourcelessVarDict :: VarDict -> Resourcer VarDict
resourcelessVarDict vDict = do
    resVars <- Set.map (resourceVar . fst) <$> gets resTypes
    tmpVars <- gets resTmpVars
    let filter nm _ = nm `Set.notMember` resVars
    return $ Map.filterWithKey filter vDict
             `Map.union` Map.fromList [(globalsName,phantomType) 
                                      | not $ Set.null resVars]
             `Map.union` tmpVars


-- | Transform a list of expressions, collecting sets of in-flowing and out-flowing 
-- resource variables.
transformExps :: [Placed Exp] 
              -> Resourcer ([Placed Exp],Set ResType, Set ResType)
transformExps [] = return ([],Set.empty,Set.empty)
transformExps (exp:exps) = do
    (exp,inRes',outRes') <- placedApply (transformExp AnyType) exp
    (exps,inRes'',outRes'') <- transformExps exps
    return (exp:exps, inRes' `Set.union` inRes'',outRes' `Set.union` outRes'')

-- | Transform a given expressions, collecting sets of in-flowing and out-flowing 
-- resource variables.
transformExp :: TypeSpec -> Exp -> OptPos 
             -> Resourcer (Placed Exp, Set ResType, Set ResType)
transformExp _ (Typed exp ty cast) pos = do
    (pexp', inRes, outRes) <- transformExp ty exp pos
    return (maybePlace (Typed (content pexp') ty cast) pos, inRes, outRes)
transformExp _ (AnonProc mods@ProcModifiers{modifierResourceful=Resourceful} 
                    params body) pos = do
    body' <- transformStmts body
    return (maybePlace (AnonProc mods{modifierResourceful=Resourceless}
                               (params ++ [globalsParam]) body') pos, 
            Set.empty, Set.empty)
transformExp  _ (AnonProc mods params body) pos = do
    body' <- transformStmts body
    return (maybePlace (AnonProc mods params body') pos, Set.empty, Set.empty)
transformExp ty exp@(Var name flow _) pos = do
    res <- (fst <$>) . Set.toList <$> gets resTypes
    let resMap = Map.fromList $ (\r -> (resourceVar r, r)) <$> res
    case Map.lookup name resMap of
        Just spec -> 
            let inRes = Set.fromList [(spec, ty) | flowsIn flow]
                outRes = Set.fromList [(spec, ty) | flowsOut flow]
            in return (maybePlace (setExpFlowType exp (Resource spec)) pos, 
                       inRes, outRes)
        Nothing -> return (maybePlace exp pos, Set.empty, Set.empty)
transformExp _ exp pos = return (maybePlace exp pos, Set.empty, Set.empty)


-- | Perform some action with additional tmp vars for resources.
-- This modifies the tmpCtr, but leaves the old tmp vars in tact. 
transformWithTmpVars :: Map VarName TypeSpec 
                     -> Resourcer a -> Resourcer a
transformWithTmpVars newVars action = do
    oldVars <- gets resTmpVars
    modify $ \s -> s{ resTmpVars = Map.union newVars oldVars }
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


-- -- | Transform a single statement, turning resources into arguments.
-- transformStmt :: Stmt -> OptPos -> Resourcer [Placed Stmt]
-- transformStmt stmt@(ProcCall m n id detism resourceful args) pos = do
--     let procID = trustFromJust "transformStmt" id
--     callResources <- procProtoResources . procProto
--                  <$> lift (getProcDef $ ProcSpec m n procID generalVersion)
--     unless (resourceful || Set.null callResources)
--         $ lift $ errmsg pos
--                $ "Call to resourceful proc without ! resource marker: "
--                     ++ showStmt 4 stmt
--     lift $ logResources 
--          $ "Checking call to " ++ n ++ " using " ++ show callResources
--     resArgs <- concat <$> mapM (resourceArgs pos) (Set.elems callResources)
--     return [maybePlace
--             (ProcCall m n (Just procID) detism False (args++resArgs)) pos]
-- transformStmt (ForeignCall lang name flags args) pos =
--     return [maybePlace (ForeignCall lang name flags args) pos]
-- transformStmt stmt@(TestBool var) pos =
--     return [maybePlace stmt pos]
-- transformStmt (And stmts) pos = do
--     stmts' <- transformStmts stmts
--     return [maybePlace (And stmts') pos]
-- transformStmt (Or [] _) pos =
--     return [failTest]
-- transformStmt (Or [stmt] _) pos = do
--     placedApplyM transformStmt stmt
-- transformStmt (Or (stmt:stmts) vars) pos = do
--     stmt'  <- placedApplyM transformStmt stmt
--     stmt'' <- transformStmt (Or stmts vars) pos
--     tmpVars <- gets resTmpVars
--     let vars' = Map.union tmpVars <$> vars
--     return [maybePlace (Or [seqToStmt stmt', seqToStmt stmt''] vars') pos]
-- transformStmt (Not stmt) pos = do
--     stmt' <- placedApplyM transformStmt stmt
--     return [maybePlace (Not $ seqToStmt stmt') pos]
-- transformStmt Nop _ =
--     return []
-- transformStmt Fail pos =
--     return [maybePlace Fail pos]
-- transformStmt (Cond test thn els condVars defVars) pos = do
--     test' <- placedApplyM transformStmt test
--     thn'  <- transformStmts thn
--     els'  <- transformStmts els
--     tmpVars <- gets resTmpVars
--     let condVars' = Map.union tmpVars <$> condVars
--     let defVars'  = Map.union tmpVars <$> defVars
--     return [maybePlace (Cond (Unplaced $ And test') thn' els'
--                         condVars' defVars') pos]
-- transformStmt (Case expr cases deflt) pos = do
--     cases' <- transformCases cases
--     deflt' <- forM deflt transformStmts
--     return [maybePlace (Case expr cases' deflt') pos]
-- transformStmt (Loop body defVars) pos = do
--     body' <- transformStmts body
--     tmpVars <- gets resTmpVars
--     let defVars' = Map.union tmpVars <$> defVars
--     return [maybePlace (Loop body' defVars') pos]
-- transformStmt (For generators body) pos = do
--     body' <- transformStmts body
--     return [maybePlace (For generators body') pos]
-- transformStmt (UseResources allRes oldRes body) pos = do
--     let resVars = trustFromJust "use stmt without var list after type check"
--                   oldRes
--     resTypes <- List.filter ((`elem` resVars) . resourceName . fst)
--             <$> lift (mapM (canonicaliseResourceSpec pos "use statement") allRes)
--     toSave <- mapM (resourceVar . fst) resTypes
--     tmp <- gets resTmpCtr
--     let types = fromJust . snd <$> resTypes
--     let tmpNames = mkTempName <$> [tmp..]
--     let ress = zip3 toSave tmpNames types
--     let get v ty = varGet v `withType` ty
--     let set v ty = varSet v `withType` ty
--     let saves = (\(r,t,ty) -> move (get r ty) (set t ty)) <$> ress
--     let restores = (\(r,t,ty) -> move (get t ty) (set r ty)) <$> ress
--     let tmpVars = Map.fromList $ zip tmpNames types
--     body' <- transformWithTmpVars (tmp + length toSave) tmpVars
--            $ transformStmts body
--     return $ saves ++ body' ++ restores
-- transformStmt Break pos =
--     return [maybePlace Break pos]
-- transformStmt Next pos =
--     return [maybePlace Next pos]



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
                   let var = resourceVar res
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
resourceVar :: ResourceSpec -> Ident
resourceVar (ResourceSpec [] name) = name
resourceVar (ResourceSpec mod name) = 
    -- Always use resource name as variable name, regardless of module
    -- XXX This could cause collisions!
    name


-- |Log a message, if we are logging resource transformation activity.
logResources :: String -> Compiler ()
logResources s = logMsg Resources s
