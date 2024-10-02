--  File     : Resources.hs
--  Author   : Peter Schachte
--  Purpose  : Resource checker for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE TupleSections #-}

module Resources (resourceCheckMod, canonicaliseProcResources,
                  canonicaliseResourceSpec,
                  transformProcResources) where

import           AST
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.Graph
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Maybe
import           Data.Set                  as Set
import           Data.Either               as Either
import           Data.Either.Extra         (mapLeft)
import           Data.Tuple.HT             (mapFst, mapSnd)
import           Data.Tuple.Extra          ((***))
import           LLVM.Prelude              (ifM)
import           Options                   (LogSelection (Resources))
import           Snippets
import           Util
import           Debug.Trace
import Control.Monad.Extra (unlessM, concatMapM)
import Data.List.Extra (nubOrd, groupOn, groupSortOn)



----------------------------------------------------------------
-- BEGIN MAJOR DOC
-- ###                 Resource Transformations.
--
-- There are two passes related to resources within the Wybe compiler.
--
-- The first pass canonicalises the `use` declarations in procedure prototypes.
-- This resolves the module which each resource refers to.
--
-- The second, performed after type checking, transforms resource usage into
-- references to global variables. Each reference to an in scope resource by 
-- name is transformed into a load (input) or a store (output), or both (in/out). 
-- Finally, `use` blocks are also transformed to save (load) and then restore
-- (store) each out-of-scope resource.
--
-- The final pass assume that type and mode checking has occured. Type
-- checking ensures that resources have the correct types, and mode checking
-- ensures that resources, where applicable are in scope.
--
-- END MAJOR DOC
----------------------------------------------------------------


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

-- |Check a resource definition
checkResourceDef :: Ident -> ResourceDef
                 -> Compiler (Bool,[(String,OptPos)],(Ident,ResourceDef))
checkResourceDef name def = do
    (chg,errs,m) <-
        unzip3 <$> mapM (uncurry checkResourceImpln) (Map.toList def)
    return (or chg, concat errs, (name,Map.fromList m))

-- |Check a resource implementation
checkResourceImpln :: ResourceSpec -> ResourceImpln
                 -> Compiler (Bool,[(String,OptPos)],
                              (ResourceSpec,ResourceImpln))
checkResourceImpln rspec impln@(SimpleResource ty mbPInit pos) = do
    logResources $ "Check resource " ++ show rspec
                 ++ " with implementation " ++ show impln
    ty' <- lookupType "resource declaration" pos ty
    logResources $ "Actual type is " ++ show ty'

    (initChg, mbPInit') <-
        if maybe False (isTyped . content) mbPInit
        then do
            let pInit = trustFromJust "checkResourceImpln" mbPInit
            let initTy = typedTy $ content pInit
            let pInitExp = contentApply typedExp pInit
            initTy' <- lookupType "resource initialisation" pos initTy
            return (initTy /= initTy',
                    Just $ contentApply (`withType` initTy') pInitExp)
        else do
            return (False, mbPInit)
    logResources $ "Actual initialisation is " ++ show mbPInit'

    return (ty' /= ty || initChg, [],
            (rspec,SimpleResource ty' mbPInit' pos))
    where
        isTyped Typed{} = True
        isTyped _ = False

        typedTy (Typed _ t _) = t
        typedTy _ = shouldnt "typedTy on a non-Typed exp"

        typedExp (Typed e _ _) = e
        typedExp _ = shouldnt "typedExp on a non-Typed exp"

-- checkOneResource rspec Nothing = do
--     -- XXX don't currently handle compound resources
--     nyi "compound resources"


------------- Canonicalising resources in proc definitions ---------

-- |Make sure all resource for the specified proc are module qualified,
--  making them canonical.
canonicaliseProcResources :: ProcDef -> Int -> Compiler ProcDef
canonicaliseProcResources pd _ = do
    let name = procName pd
    logResources $ "Canonicalising resources used by " ++ showProcName name
    let proto = procProto pd
    let pos = procPos pd
    let resources = procProtoResources proto
    resourceFlows <- List.map collapseResourceFlows 
                   . groupSortOn resourceFlowRes 
                 <$> mapM (canonicaliseResourceFlow pos name) resources
    logResources $ "Available resources: " ++ show resourceFlows
    let proto' = proto {procProtoResources = resourceFlows}
    let pd' = pd {procProto = proto'}
    logResources $ "Canonicalising resources results in:"
                    ++ showProcDef 4 pd'
    return pd'

-- |Ensure a resource flow is fully module qualified, canonicalising the resource
-- spec
canonicaliseResourceFlow :: OptPos -> ProcName -> ResourceFlowSpec
                         -> Compiler ResourceFlowSpec
canonicaliseResourceFlow pos name (ResourceFlowSpec res flow) = do
    res' <- fst 
        <$> canonicaliseResourceSpec pos 
                ("declaration of " ++ showProcName name) 
                res
    return $ ResourceFlowSpec res' flow


collapseResourceFlows :: [ResourceFlowSpec] -> ResourceFlowSpec
collapseResourceFlows [] = shouldnt "empty resource group"
collapseResourceFlows ress@(ResourceFlowSpec res flow:_) 
    = ResourceFlowSpec res
        $ case nubOrd ress of 
            [_] -> flow
            _ -> ParamInOut
        

--------- Transform resources into global variables ---------

-- | Data type to store the necessary data for adding resources to a proc
data ResourceState = ResourceState {
    -- | The set of resources and their types that are currently in scope
    resResources      :: Map ResourceSpec TypeSpec,
    -- | Tmp variables for resources that have been generated so far
    resTmpVars        :: VarDict,
    -- | The current tmp variable counter
    resTmpCtr         :: Int,
    -- | The set of resources that flow into the current stmt
    resIn             :: Map ResourceSpec TypeSpec,
    -- | The set of resources that flow out of the current stmt
    resOut            :: Map ResourceSpec TypeSpec,
    -- | The set of resources that have been mentioned anywhere in this proc
    resMentioned      :: Map ResourceSpec TypeSpec,
    -- | The tmp vars that are used to restore resources when breaking a loop
    resLoopTmps       :: Map ResourceSpec (VarName, TypeSpec),
    -- | Are we currently transforming the executable main procedure?
    resIsExecMain     :: Bool
}

-- | Initial ResourceState given a tmpCtr
initResourceState :: Int -> ResourceState
initResourceState tmp = ResourceState{resResources=Map.empty,
                                      resTmpVars=Map.empty,
                                      resTmpCtr=tmp,
                                      resIn=Map.empty,
                                      resOut=Map.empty,
                                      resMentioned=Map.empty,
                                      resLoopTmps=Map.empty,
                                      resIsExecMain=False}


-- | State transformer using a ResourceState
type Resourcer = StateT ResourceState Compiler

-- | Transform a given ProcDef, transforming resource usage into loads/stores of
-- global variables, and threads the global variable state through calls. 
-- Also check that calls to procs that use resources are annotated with a ! 
-- to indicate resource usage. 
--
-- Note that this is the final pass of resource transformation, and must be
-- performed after uniqueness checking, as the loads/stores cause all resource
-- usage to appear as though it obeys uniquness checking
--
-- Note that type checking of all called procedures must have been completed
-- before this can be done, because called procs are only resolved when this
-- proc is type checked.
--
-- XXX this may interfere with uniqueness inference and/or destructive updates
transformProcResources :: ProcDef -> Int -> Compiler ProcDef
transformProcResources pd _ = do
    logResources "--------------------------------------\n"
    logResources $ "Transforming resources in:" ++ showProcDef 4 pd
    let name = procName pd
    let proto = procProto pd
    let detism = procDetism pd
    let pos = procPos pd
    let tmp = procTmpCount pd
    let variant = procVariant pd
    let params = procProtoParams proto
    let res = procProtoResources proto
    let ProcDefSrc body = procImpln pd
    (params', body', tmp') <- evalStateT (transformProc pos (Just name) variant
                                            detism params res body)
                                $ initResourceState tmp
    let proto' = proto { procProtoParams=params' }
    let pd' = pd { procProto=proto', procTmpCount=tmp',
                   procImpln=ProcDefSrc body' }
    logResources "--------------------------------------\n"
    logResources $ "Transforming results in:" ++ showProcDef 4 pd'
    return pd'


-- Transform a proc, transforming resources into globals.
-- This returns an updated list of Params, transformed list of Stmts (body),
-- and the value of the tmpCtr after transforming the proc
transformProc :: OptPos -> Maybe ProcName -> ProcVariant
              -> Determinism -> [Placed Param] -> [ResourceFlowSpec]
              -> [Placed Stmt] -> Resourcer ([Placed Param], [Placed Stmt], Int)
transformProc pos name variant detism params ress body = do
    logResourcer $ "Transforming proc " ++ fromMaybe "un-named (anon)" name
    resTys <- concat <$> mapM (simpleResourceFlows pos) ress
    let allParams = params ++ List.map resourceParams resTys
    let hasHigherResources = any (paramIsResourceful . content) allParams
    let (resFlows, realParams) = partitionEithers $ eitherResourceParam <$> allParams
    let needsGlobalParam = hasHigherResources || not (List.null resFlows)
    thisMod <- lift getModuleSpec
    let isExecMain = List.null thisMod && name == Just ""
    ResourceState{resResources=oldResources,
                  resMentioned=oldMentioned,
                  resTmpVars=oldTmpVars,
                  resLoopTmps=oldLoopTmps,
                  resIsExecMain=oldIsExecMain} <- get
    let res = Map.fromList $ mapFst resourceFlowRes <$> resFlows
    modify $ \s -> s{resResources=res,
                     resMentioned=res,
                     resLoopTmps=Map.empty,
                     resIsExecMain=isExecMain}
    -- we must save and restore any non-out-flowing resources, as we cannot be
    -- sure theyre not mutated
    let ress' = [res | ResourceFlowSpec res flow <- ress
                , not $ flowsOut flow
                , not $ isSpecialResource res ]
    body' <- fst <$> transformStmts [UseResources ress' (Just Map.empty) body
                                        `maybePlace` pos]
    -- In the case of a proc that may fail, we need to roll back the state of
    -- resources we can if we fail. We can do this with the following
    -- transformation
    --  <stmts>
    -- ... into ...
    --  <loads>
    --  if { <stmts> :: <nop> | else :: <stores>; fail }
    -- Unbranching will then force the stores to be executed in the case of
    -- failure, ensuring the global variables are unmoddified
    newMentioned <- gets resMentioned
    body'' <- if not (determinismCanFail detism) || Map.null newMentioned
              then return body'
              else do
                (saves, restores, tmpVars, _) <- saveRestoreResourcesTmp pos
                                            $ Map.toList newMentioned
                -- re-transform the body so we have the right tmp variables
                -- accounting for the resources we need to save and restore
                body''' <- fst <$> transformStmts
                     [UseResources ress' (Just Map.empty) body `maybePlace` pos]
                -- XXX (Just tmpVars) is wrong here:  it should include ALL
                -- variables assigned by body', but we don't have that
                return $ saves
                      ++ [Unplaced $ Cond (seqToStmt body''')
                            []
                            (restores ++ [Unplaced Fail])
                            (Just tmpVars) (Just Map.empty) (Just Set.empty)]
    modify $ \s -> s{resResources=oldResources,
                     resTmpVars=oldTmpVars,
                     resLoopTmps=oldLoopTmps,
                     resIsExecMain=oldIsExecMain,
                     resMentioned=oldMentioned `Map.union` newMentioned}
    tmp <- gets resTmpCtr
    -- executable main gets special treatment
    -- in-flowing resources must be stored, and parameters are unmodified
    return $
        if isExecMain
        then let inRes = List.filter (flowsIn . resourceFlowFlow . fst) resFlows
                 stores = storeResource pos . mapFst resourceFlowRes <$> inRes
             in (allParams, stores ++ body'', tmp)
        else (realParams, body'', tmp)


-- Transform a list of Stmts, tranforming resources into globals
-- The returned bool indicates if any of the Stmts could modify globals
transformStmts :: [Placed Stmt] -> Resourcer ([Placed Stmt], Bool)
transformStmts pstmts = (concat *** or) . unzip
                     <$> mapM (placedApply transformStmt) pstmts


-- Transform a Stmt, tranforming resources into globals
-- The returned bool indicates if the Stmt could modify a global
transformStmt :: Stmt -> OptPos -> Resourcer ([Placed Stmt], Bool)
transformStmt stmt@(ProcCall fn@(First m n mbId) d resourceful args) pos = do
    let procID = trustFromJust "transformStmt" mbId
    procDef <- lift (getProcDef $ ProcSpec m n procID generalVersion)
    let proto = procProto procDef
    let (res, args') = partitionEithers $ placedApply eitherResourceExp <$> args
    unless (List.null res) $ shouldnt $ "statement with resource args " ++ show stmt
    (args'', ins, outs) <- transformExps args'
    let callResFlows = procProtoResources proto
    let callParamTys = paramType . content <$> procProtoParams proto
    let hasResfulHigherArgs = any isResourcefulHigherOrder callParamTys
    let usesResources = not (List.null callResFlows) || hasResfulHigherArgs
    let usesOrdinaryResources =
            hasResfulHigherArgs
            || not (all (isSpecialResource . resourceFlowRes) callResFlows)
    unless (resourceful || not usesOrdinaryResources)
        $ lift $ errmsg pos
               $ "Call to resourceful proc without ! resource marker: "
                    ++ showStmt 4 stmt
    resArgs <- concat <$> mapM (resourceArgs pos)
        (List.filter (isSpecialResource . resourceFlowRes) callResFlows)
    return (loadStoreResources pos ins outs
                [ProcCall fn d False (args'' ++ resArgs) `maybePlace` pos],
            usesResources || not (Map.null outs))
transformStmt (ProcCall (Higher fn) d r args) pos = do
    (fn':args', ins, outs) <- transformExps $ fn:args
    let globals = case maybeExpType $ content fn' of
                    Just (HigherOrderType mods _) -> modifierResourceful mods
                    _ -> shouldnt "glabalise badly typed higher"
    return (loadStoreResources pos ins outs
                [ProcCall (Higher fn') d False args' `maybePlace` pos],
            globals)
transformStmt (ForeignCall lang name flags args) pos = do
    (args', ins, outs) <- transformExps args
    return (loadStoreResources pos ins outs
                [ForeignCall lang name flags args' `maybePlace` pos],
            not $ Map.null outs)
transformStmt (Cond tst thn els condVars exitVars _) pos = do
    oldResTmpVars <- gets resTmpVars
    (tst', tstGlobals) <- placedApply transformStmt tst
    (saves, restores) <- loadStoreResourcesIf pos tstGlobals
    condVars' <- fixVarDict condVars
    exitVars' <- fixVarDict exitVars
    logResourcer $ "Transforming conditional:"
    logResourcer $ "resTmpVars = " ++ showVarMap oldResTmpVars
    logResourcer $ "     saves = " ++ showBody 13 saves
    logResourcer $ "  restores = " ++ showBody 13 restores
    logResourcer $ "  condVars = " ++ showVarMap (fromJust condVars')
    logResourcer $ "  exitVars = " ++ showVarMap (fromJust exitVars')
    (thn', thnGlobals) <- transformStmts thn
    (els', elsGlobals) <- transformStmts els
    res <- gets resResources
    modify $ \s -> s { resTmpVars = oldResTmpVars }
    return (saves ++ [Cond (seqToStmt tst') thn' (restores ++ els')
                            condVars' exitVars' (Just $ Map.keysSet res)
                        `maybePlace` pos],
            thnGlobals || elsGlobals)
transformStmt (And stmts) pos = do
    (stmts', globals) <- transformStmts stmts
    return ([And stmts' `maybePlace` pos], globals)
transformStmt (Or disjs vars _) pos =
    shouldnt "Disjunction should have been flattened into conditional."
transformStmt (Not stmt) pos = do
    ([stmt'], globals) <- transformStmts [stmt]
    return ([Not stmt' `maybePlace` pos], globals)
transformStmt (TestBool exp) pos = do
    ([exp'], ins, outs) <- transformExps [exp `maybePlace` pos]
    -- TestBool cannot modify a resource
    unless (Map.null outs) $ shouldnt "transform TestBool with out flowing resource"
    return (loadStoreResources pos ins outs [TestBool (content exp') `maybePlace` pos],
            False)
transformStmt (Loop stmts vars _) pos = do
    loopTmps <- gets resLoopTmps
    modify $ \s -> s{resLoopTmps=Map.empty}
    (stmts',usesGlobals) <- transformStmts stmts
    vars' <- fixVarDict vars
    res <- gets resResources
    modify $ \s -> s{resLoopTmps=loopTmps}
    return ([Loop stmts' vars' (Just $ Map.keysSet res) `maybePlace` pos], usesGlobals)
transformStmt (UseResources res vars stmts) pos = do
    let (special, res') = List.partition isSpecialResource res
    let vars' = trustFromJust "transform use with no vars" vars
    resTypes <- (mapSnd (trustFromJust "transform use") <$>)
            <$> lift (mapM (canonicaliseResourceSpec pos "use block") res')
    ResourceState{resResources=resources,
                  resMentioned=mentioned,
                  resTmpVars=tmpVars,
                  resLoopTmps=loopTmps,
                  resIsExecMain=isExecMain} <- get
    -- save/restore local variables that have been selected to be
    (saves, restores, localTmpVars) <- saveRestoreLocalsTmp pos
                                    $ Map.toList vars'
    (loads, stores, newVars, newLoopTmps) <- saveRestoreResourcesTmp pos resTypes
    let resources' = Map.fromList resTypes
    modify $ \s -> s {resResources=resources `Map.union` resources',
                      resMentioned=mentioned `Map.union` resources',
                      resLoopTmps=loopTmps `Map.union` newLoopTmps}
    unless isExecMain $
        modify $ \s -> s {resTmpVars=resTmpVars s `Map.union` localTmpVars
                                     `Map.union` newVars}
    -- saves/restores may manipulate globals
    stmts' <- fst <$> transformStmts (saves ++ stmts ++ restores)
    modify $ \s -> s {resResources=resources,
                      resLoopTmps=loopTmps,
                      resTmpVars=tmpVars}
    -- no need to load and store resources in executable main
    (, not $ List.null res') <$> if isExecMain
    then return stmts'
    else return
            -- load the old values of the resources
        (loads
            -- store the values of the new resources,
            -- if theyve been assigned before the use block
         ++ [storeResource pos (res, ty)
            | (res, ty) <- resTypes
            , resourceVar res `Map.member` vars'
            , res `Map.notMember` resources]
         ++ stmts'
            -- store the old values of the resources
         ++ stores)
transformStmt Nop pos = return ([Nop `maybePlace` pos], False)
transformStmt Fail pos = return ([Fail `maybePlace` pos], False)
transformStmt Break pos = do
    restores <- restoreLoopGlobals pos
    return (restores ++ [Break `maybePlace` pos], False)
transformStmt Next pos = do
    restores <- restoreLoopGlobals pos
    return (restores ++ [Next `maybePlace` pos], False)
transformStmt Case{} _ = shouldnt "case in transform"
transformStmt For{} _ = shouldnt "for in transform"


-- | Restore global variables for a loop
restoreLoopGlobals :: OptPos -> Resourcer [Placed Stmt]
restoreLoopGlobals pos = do
    loopTmps <- gets resLoopTmps
    return [rePlace pos $ globalStore res ty
                        $ Typed (Var tmp ParamIn Ordinary) ty Nothing
           | (res, (tmp, ty)) <- Map.toList loopTmps]


-- | transform a list of expressions.
-- This returns a list of inflowing and outflowing resources, and keeps the
-- Resourcer monad's in and out resources in tact
transformExps :: [Placed Exp]
              -> Resourcer ([Placed Exp], Map ResourceSpec TypeSpec,
                                          Map ResourceSpec TypeSpec)
transformExps exps = do
    ResourceState{resIn=oldIn, resOut=oldOut} <- get
    modify $ \s -> s{resIn=Map.empty, resOut=Map.empty}
    exps' <- transformExps' exps
    state' <- get
    modify $ \s -> s{resIn=oldIn, resOut=oldOut}
    return (exps', resIn state', resOut state')


-- | transform a list of expresstions
transformExps' :: [Placed Exp] -> Resourcer [Placed Exp]
transformExps' = mapM (placedApply $ transformExp AnyType)


-- | transform a single expression, adding any in flowing or out flowing
-- resources to the Resourcer monad as necessary.
transformExp :: TypeSpec -> Exp -> OptPos -> Resourcer (Placed Exp)
transformExp _ (Typed exp ty cast) pos = do
    exp' <- transformExp ty exp pos
    return $ Typed (content exp') ty cast `maybePlace` pos
transformExp ty exp@(Var nm fl _) pos = do
    addResourceInOuts fl nm ty
    return $ exp `maybePlace` pos
transformExp _ (Closure pspec exps) pos = do
    exps' <- transformExps' exps
    return $ Closure pspec exps' `maybePlace` pos
transformExp _ (AnonProc mods@(ProcModifiers detism _ _ _ resful)
                params body clsd _) pos = do
    res <- List.map (`ResourceFlowSpec` ParamInOut)
         . List.filter (not . isSpecialResource)
         . Map.keys
        <$> gets resResources
    let res' = if resful then res else []
    (params', body', _) <- transformProc pos Nothing AnonymousProc
                                detism (Unplaced <$> params) res' body
    let clsd' = trustFromJust "gloablise anon proc without clsd" clsd
    clsd'' <- if resful
              then (clsd' `Map.difference`) . resourceNameMap <$> gets resResources
              else do
                  mapM_ (uncurry $ addResourceInOuts ParamIn) $ Map.toList clsd'
                  return clsd'
    return $ AnonProc mods (content <$> params') body' (Just clsd'') (Just res') `maybePlace` pos
transformExp _ exp pos = return $ exp `maybePlace` pos


-- |Add the specified variable and type to the list of in or out resources if
-- the variable refers to a resource
addResourceInOuts :: FlowDirection -> VarName -> TypeSpec -> Resourcer ()
addResourceInOuts fl nm ty = do
    ress <- resourceNameMap <$> gets resResources
    forM_ (Map.lookup nm ress)
        $ \res -> modify (\s -> s{resIn=resIn s `Map.union`
                                            Map.fromList [(res,ty) | flowsIn fl],
                                  resOut=resOut s `Map.union`
                                            Map.fromList [(res,ty) | flowsOut fl]})

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
                    logResources $ "    to --> " ++ show spec
                                    ++ ":" ++ show impln
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


-- |Returns the list of args corresponding to the specified resource
-- flow spec.  This produces up to two arguments for each simple
-- resource, multiplied by all the simple resources a single resource
-- flow spec might refer to.
resourceArgs :: OptPos -> ResourceFlowSpec -> Resourcer [Placed Exp]
resourceArgs pos rflow = do
    simpleSpecs <- simpleResourceFlows pos rflow
    mapM (\(ResourceFlowSpec res flow,ty) -> do
                   let var = resourceVar res
                   let ftype = Resource res
                   return $ Unplaced $ Typed (Var var flow ftype) ty Nothing)
         simpleSpecs


-- | The local variable name to use for a resource.  This assumes the resource
-- spec has already been canonicalised (fully module qualified).
resourceVar :: ResourceSpec -> Ident
resourceVar (ResourceSpec [] name) = name
resourceVar (ResourceSpec mod name) =
    -- Always use resource name as variable name, regardless of module
    -- XXX This could cause collisions!
    name


-- | Transform a ResourceFlowSpec with a type into a Param
resourceParams :: (ResourceFlowSpec,TypeSpec) -> Placed Param
resourceParams (ResourceFlowSpec res flow, typ) =
    Unplaced $ Param (resourceVar res) typ flow (Resource res)


-- | Given a ResourceSpec and something, return Right of something if the
-- resource is a special resource, else Left of that resource
eitherResource :: ResourceSpec -> a -> Either ResourceSpec a
eitherResource res a =
    if isSpecialResource res
    then Right a
    else Left res


-- | Given a Param, return either the (ResourceFlowSpec, TypeSpec) associated
-- with the parameter or the param itself
eitherResourceParam :: Placed Param -> Either (ResourceFlowSpec, TypeSpec) (Placed Param)
eitherResourceParam param =
    case content param of
        Param _ ty fl (Resource res) ->
            mapLeft ((,ty) . (`ResourceFlowSpec` fl))
            $ eitherResource res param
        _ -> Right param


-- | Given an Exp, return either the ResourceSpec associated with a Var, else
-- the Exp itself
eitherResourceExp :: Exp -> OptPos -> Either ResourceSpec (Placed Exp)
eitherResourceExp var@(Typed (Var _ _ (Resource res)) ty _) pos =
    eitherResource res $ var `maybePlace` pos
eitherResourceExp exp pos = Right $ exp `maybePlace` pos


-- | Add tmp variables into a resource dictionary. If we are transforming, we
-- remove resources from the dict, and if the flag is true, we also
-- add the #globals variable
fixVarDict :: Maybe VarDict -> Resourcer (Maybe VarDict)
fixVarDict Nothing = return Nothing
fixVarDict (Just vars) = do
    ress <- resourceNameMap <$> gets resResources
    tmpVars <- gets resTmpVars
    let filter res _ = not $ res `Map.member` ress
    return $ Just $ Map.filterWithKey filter vars `Map.union` tmpVars


-- | Get a var as a resource of the given type
getResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
getResource nm (rs, ty) = varGetTyped nm ty `setExpFlowType` Resource rs


-- | Set a var as a resource of the given type
setResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
setResource nm (rs, ty) = varSetTyped nm ty `setExpFlowType` Resource rs


-- | Generate code to save and restore the given resources in tmp variables.
-- Also save the tmp variables in the Resourcer resTmpVars state.
saveRestoreResourcesTmp :: OptPos -> [(ResourceSpec, TypeSpec)]
                        -> Resourcer ([Placed Stmt], [Placed Stmt], VarDict,
                                      Map ResourceSpec (VarName, TypeSpec))
saveRestoreResourcesTmp pos resTys = do
    tmp <- gets resTmpCtr
    modify $ \s -> s{resTmpCtr=tmp + length resTys}
    let tmpVars = mkTempName <$> [tmp..]
        (res, tys) = unzip resTys
        ress = zip tmpVars resTys
        globalSave (t,(rs,ty)) = globalLoad rs ty $ setResource t (rs,ty)
        globalRestore (t,(rs,ty)) = globalStore rs ty $ getResource t (rs,ty)
    modify $ \s -> s{resTmpVars = List.foldr (\(k,v) m -> Map.insert k v m)
                                        (resTmpVars s) $ zip tmpVars tys}
    return (rePlace pos . globalSave <$> ress, rePlace pos . globalRestore <$> ress,
            Map.fromList $ zip tmpVars (snd <$> resTys),
            Map.fromList $ zip res $ zip tmpVars tys)


-- | Save and restore the given local variables in tmp variables
saveRestoreLocalsTmp :: OptPos -> [(VarName, TypeSpec)]
                   -> Resourcer ([Placed Stmt], [Placed Stmt], VarDict)
saveRestoreLocalsTmp pos varTys = do
    tmp <- gets resTmpCtr
    modify $ \s -> s{resTmpCtr=tmp + length varTys}
    let tmpVars = mkTempName <$> [tmp..]
        vars = zip tmpVars varTys
        save (t,(v,ty)) = move (varGetTyped v ty)
                               (varSetTyped t ty)
        restore (t,(v,ty)) = move (varGetTyped t ty)
                                  (varSetTyped v ty)
    return (rePlace pos . save <$> vars, rePlace pos . restore <$> vars,
            Map.fromList $ zip tmpVars (snd <$> varTys))


-- | Store the given resource in globals
storeResource :: OptPos -> (ResourceSpec, TypeSpec) -> Placed Stmt
storeResource pos rsTy@(rs,ty) =
    rePlace pos $ globalStore rs ty (getResource (resourceName rs) rsTy)


-- | Store the given resource in globals
storeResources :: OptPos -> Map ResourceSpec TypeSpec -> [Placed Stmt]
storeResources pos = (storeResource pos <$>) . Map.toList


-- | Load the given resource from globals
loadResource :: OptPos -> (ResourceSpec, TypeSpec) -> Placed Stmt
loadResource pos rsTy@(rs,ty) =
    rePlace pos $ globalLoad rs ty (setResource (resourceName rs) rsTy)


-- | Load the given resource from globals
loadResources :: OptPos -> Map ResourceSpec TypeSpec -> [Placed Stmt]
loadResources pos = (loadResource pos <$>) . Map.toList


-- | Surround a given list of statements with loads/stores to the given
-- resources
loadStoreResources :: OptPos
                   -> Map ResourceSpec TypeSpec -> Map ResourceSpec TypeSpec
                   -> [Placed Stmt] -> [Placed Stmt]
loadStoreResources pos inRes outRes stmts =
    loadResources pos inRes ++ stmts ++ storeResources pos outRes

-- | Surround a given list of statements with loads/stores to the given
-- resources, iff the flag is True
loadStoreResourcesIf :: OptPos -> Bool
                     -> Resourcer ([Placed Stmt],[Placed Stmt])
loadStoreResourcesIf pos False = return ([], [])
loadStoreResourcesIf pos True = do
    res <- gets resResources
    (saves, restores, _, _) <- saveRestoreResourcesTmp pos $ Map.toList res
    return (saves, restores)


-- Build a map of resource names to their respective resource specs
resourceNameMap :: Map ResourceSpec TypeSpec -> Map VarName ResourceSpec
resourceNameMap = Map.fromList . ((((,) =<< resourceName) . fst) <$>)
                               . Map.toList


-- |Log a message in the Compiler monad,
-- if we are logging resource transformation activity.
logResources :: String -> Compiler ()
logResources s = logMsg Resources s


-- |Log a message in the Resourcer monad,
-- if we are logging resource transformation activity.
logResourcer :: String -> Resourcer ()
logResourcer = lift . logResources
