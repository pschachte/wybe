--  File     : Resources.hs
--  Author   : Peter Schachte
--  Purpose  : Resource checker for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE TupleSections #-}

module Resources (resourceCheckMod, canonicaliseProcResources,
                  canonicaliseResourceSpec,
                  transformProcResources, transformProcGlobals) where

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
import Control.Monad.Extra (unlessM)



----------------------------------------------------------------
-- BEGIN MAJOR DOC
-- ###                 Resource Transformations.
--
-- There are three passes related to resources within the Wybe compiler.
--
-- The first pass canonicalises the `use` declarations in procedure prototypes.
-- This resolves the module which each resource refers to.
--
-- The second, performed after type checking, transforms resource usage into
-- regular parameters/arguments. Here, each procedure is modifed to include
-- parameters corresponding to each resource and respective flow.
-- Each call is also transformed to include the resources as arguments.
-- The order of arguments is dictated by the ordering of the `ResourceSpec`
-- type, ordering by module then name. `use` blocks are also transformed to
-- contain LPVM `move` instructions of respectively used resources, to save
-- and subsequently restore the value of each resource variable.
--
-- The final pass tranforms resource into global variables. This pass must be
-- performed after uniqueness checking, as uniqueness checking assumes only the
-- second pass has been performed. The additional parameters and arguments
-- introduced in the second pass are removed here, as they are now passed in
-- global variables. Each reference to an in scope resource by name is
-- transformed into a load (input) or a store (output), or both (in/out).
-- Finally, `use` blocks are also transformed to save (load) and then restore
-- (store) each out-of-scope resource.
--
-- The final two passes assume that type and mode checking has occured. Type
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

-- |Check a resource implmentation
checkResourceImpln :: ResourceSpec -> ResourceImpln
                 -> Compiler (Bool,[(String,OptPos)],
                              (ResourceSpec,ResourceImpln))
checkResourceImpln rspec impln@(SimpleResource ty init pos) = do
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

-- |Ensure a resource flow is fully module qualified, canonicalising the resource
-- spec
canonicaliseResourceFlow :: OptPos -> ResourceFlowSpec
                         -> Compiler ResourceFlowSpec
canonicaliseResourceFlow pos spec = do
    resTy <- canonicaliseResourceSpec pos "proc declaration"
             $ resourceFlowRes spec
    return $ spec { resourceFlowRes = fst resTy }


--------- Transform resources into variables and parameters ---------

-- | Data type to store the necessary data for adding resources to a proc
data ResourceState = ResourceState {
    resResources      :: Map ResourceSpec TypeSpec,
    -- ^ The set of resources and their types that are currently in scope
    resTmpVars        :: VarDict,
    -- ^ Tmp variables that have been generated so far
    resTmpCtr         :: Int,
    -- ^ The current tmp variable counter
    resHaveGlobals    :: Maybe Bool,
    -- ^ Do we currently have a #globals variable?
    -- Nothing if we arent globalising

    -- The following are only used when globalising
    resIn             :: Map ResourceSpec TypeSpec,
    -- ^ The set of resources that flow into the current stmt
    resOut            :: Map ResourceSpec TypeSpec,
    -- ^ The set of resources that flow out of the current stmt
    resMentioned      :: Map ResourceSpec TypeSpec,
    -- ^ The set of resources that have been mentioned anywhere
    -- in this procedure
    resLoopTmps       :: Map ResourceSpec (VarName, TypeSpec),
    -- ^ The tmp vars that are used to restore resources when breaking a loop
    resIsExecMain     :: Bool
    -- ^ Are we currently globalising the executable main procedure
}

-- | Initial ResourceState given a tmpCtr
initResourceState :: Maybe Bool -> Int -> ResourceState
initResourceState globals tmp = ResourceState{resResources=Map.empty,
                                              resTmpVars=Map.empty,
                                              resTmpCtr=tmp,
                                              resHaveGlobals=globals,
                                              resIn=Map.empty,
                                              resOut=Map.empty,
                                              resMentioned=Map.empty,
                                              resLoopTmps=Map.empty,
                                              resIsExecMain=False}


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
    logResources $ "Declared resources: " ++ show resFlows
    (body', resParams, tmp')
        <- evalStateT (transformProc resFlows body pos)
            $ initResourceState Nothing tmp
    let proto' = proto { procProtoParams=params ++ resParams }
    let pd' = pd { procProto=proto', procTmpCount=tmp',
                   procImpln=ProcDefSrc body' }
    logResources $ "Adding resources results in:" ++ showProcDef 4 pd'
    return pd'

-- | Transform a ResourceFlowSpec with a type into a Param
resourceParams :: (ResourceFlowSpec,TypeSpec) -> Param
resourceParams (ResourceFlowSpec res flow, typ) =
    Param (resourceVar res) typ flow (Resource res)


-- | Transform a given procedure's body and resources, producing the body with
-- resources transformed into arguments, the additional parameters for resources
-- and the new tmpCtr
transformProc :: Set ResourceFlowSpec -> [Placed Stmt] -> OptPos
              -> Resourcer ([Placed Stmt], [Param], Int)
transformProc resourceFlows body pos = do
    resFlows <- concat <$> mapM (simpleResourceFlows pos)
                           (Set.elems resourceFlows)
    modify $ \s -> s{resResources=Map.fromList $ mapFst resourceFlowRes <$> resFlows}
    logResourcer $ "Declared resources: " ++ show resFlows
    body' <- transformStmts body
    tmp' <- gets resTmpCtr
    return (body', resourceParams <$> resFlows, tmp')


-- | Transform a statement sequence, turning resources into arguments.
transformStmts :: [Placed Stmt] -> Resourcer [Placed Stmt]
transformStmts stmts = concat <$> mapM (placedApply transformStmt) stmts


-- | Transform a single statement, turning resources into arguments.
transformStmt :: Stmt -> OptPos -> Resourcer [Placed Stmt]
transformStmt stmt@(ProcCall func@(First m n mbId) detism resourceful args) pos = do
    let procID = trustFromJust "transformStmt" mbId
    procDef <- lift (getProcDef $ ProcSpec m n procID generalVersion)
    let callResFlows = Set.toList $ procProtoResources $ procProto procDef
    let variant = procVariant procDef
    let argTys = fromMaybe AnyType . maybeExpType . content <$> args
    let hasResfulHigherArgs = any isResourcefulHigherOrder argTys
    let usesResources = not (List.null callResFlows) || hasResfulHigherArgs
    unless (resourceful || not usesResources)
        $ lift $ errmsg pos
               $ "Call to resourceful proc without ! resource marker: "
                    ++ showStmt 4 stmt
    args' <- transformExps args
    resArgs <- concat <$> mapM (resourceArgs pos) callResFlows
    return [maybePlace (ProcCall func detism False $ args' ++ resArgs) pos]
transformStmt stmt@(ProcCall (Higher func) detism resourceful args) pos = do
    (func':args') <- transformExps $ func:args
    case content func' of
        Typed _ (HigherOrderType ProcModifiers{modifierResourceful=True} _) _ -> do
            unless resourceful
                $ lift $ errmsg pos
                $ "Resourceful higher order call without ! resource marker: "
                    ++ showStmt 4 stmt
        Typed _ (HigherOrderType _ _) _ -> nop
        _ -> shouldnt $ "bad resource higher call type" ++ show stmt
    return [maybePlace (ProcCall (Higher func') detism False args') pos]
transformStmt (ForeignCall lang name flags args) pos = do
    args' <- transformExps args
    return [maybePlace (ForeignCall lang name flags args') pos]
transformStmt (TestBool var) pos = do
    var' <- transformExp var pos
    return [maybePlace (TestBool $ content var') pos]
transformStmt (And stmts) pos = do
    stmts' <- transformStmts stmts
    return [maybePlace (And stmts') pos]
transformStmt (Or [] _ _) pos =
    return [failTest]
transformStmt (Or [stmt] _ _) pos = do
    placedApplyM transformStmt stmt
transformStmt (Or (stmt:stmts) vars res) pos = do
    stmt'  <- placedApplyM transformStmt stmt
    stmt'' <- transformStmt (Or stmts vars res) pos
    vars' <- fixVarDict vars
    return [maybePlace (Or [seqToStmt stmt',seqToStmt stmt''] vars' res) pos]
transformStmt (Not stmt) pos = do
    stmt' <- placedApplyM transformStmt stmt
    return [maybePlace (Not $ seqToStmt stmt') pos]
transformStmt (Cond test thn els condVars exitVars res) pos = do
    test' <- placedApplyM transformStmt test
    thn' <- transformStmts thn
    els' <- transformStmts els
    condVars' <- fixVarDict condVars
    exitVars' <- fixVarDict exitVars
    return [maybePlace (Cond (seqToStmt test')
            thn' els' condVars' exitVars' res) pos]
transformStmt (Case exp cases deflt) pos = do
    exp' <- placedApply transformExp exp
    cases' <- transformCases cases
    deflt' <- forM deflt transformStmts
    return [maybePlace (Case exp' cases' deflt') pos]
transformStmt (Loop body vars res) pos = do
    body' <- transformStmts body
    vars' <- fixVarDict vars
    return [maybePlace (Loop body' vars' res) pos]
transformStmt (For generators body) pos = do
    body' <- transformStmts body
    return [maybePlace (For generators body') pos]
transformStmt (UseResources res vars body) pos = do
    let vars' = trustFromJust "globalise use with no vars" vars
    resMbTypes <- lift $ mapM (canonicaliseResourceSpec pos "use statement")
                              res
    let resTys = mapSnd (trustFromJust "transformStmt UseResources")
               <$> resMbTypes
    let vars' = trustFromJust "globalise use with no before" vars
    s@ResourceState{resResources=oldResTypes,
                    resTmpVars=oldTmp} <- get
    (saves, restores, tmpVars) <- saveRestoreLocalsTmp pos $ Map.toList vars'
    modify $ \s -> s{resTmpVars=tmpVars `Map.union` oldTmp,
                     resResources=oldResTypes `Map.union` Map.fromList resTys}
    body' <- transformStmts body
    modify $ \s -> s{ resTmpVars=oldTmp }
    return $ saves
          ++ [UseResources res vars body' `maybePlace` pos]
          ++ restores
transformStmt Nop pos = return [maybePlace Nop pos]
transformStmt Fail pos = return [maybePlace Fail pos]
transformStmt Break pos = return [maybePlace Break pos]
transformStmt Next pos = return [maybePlace Next pos]


-- | Transform a list of expressions
transformExps :: [Placed Exp] -> Resourcer [Placed Exp]
transformExps exps = mapM (placedApply transformExp) exps


-- | Transform a given expression
transformExp :: Exp -> OptPos -> Resourcer (Placed Exp)
transformExp (Typed exp ty cast) pos = do
    exp' <- content <$> transformExp exp pos
    return $ maybePlace (Typed exp' ty cast) pos
transformExp (AnonProc mods params body clsd _) pos = do
    body' <- transformStmts body
    res <- (mapFst (`ResourceFlowSpec` ParamInOut) <$>) . Map.toList <$> gets resResources
    let (params', res') = if modifierResourceful mods
                  then (params ++ (resourceParams <$> res),
                        Set.fromList $ fst <$> res)
                  else (params, Set.empty)
    return $ AnonProc mods params' body' clsd (Just res')
                `maybePlace` pos
transformExp exp pos = return $ maybePlace exp pos


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
    mapM (\(ResourceFlowSpec res flow,ty) -> do
                   let var = resourceVar res
                   let ftype = Resource res
                   return $ Unplaced $ Typed (Var var flow ftype) ty Nothing)
         simpleSpecs


------------------------- Globalisation --------------------------------

-- | Transform a givn ProcDef, transforming resource usage into loads/stores of
-- global variables, and threads a global variable state through calls instead
-- of passing resources as parameters
--
-- Note that this is the final pass of resource transformation, and must be
-- performed after uniqueness checking, as the loads/stores cause all resource
-- usage to appear as though it obeys uniquness checking
--
-- XXX this may interfere with uniqueness inference and/or destructive updates
transformProcGlobals :: ProcDef -> Int -> Compiler ProcDef
transformProcGlobals pd _ = do
    logResources "--------------------------------------\n"
    logResources $ "Globalising resources in:" ++ showProcDef 4 pd
    let name = procName pd
    let proto = procProto pd
    let detism = procDetism pd
    let pos = procPos pd
    let tmp = procTmpCount pd
    let variant = procVariant pd
    let params = procProtoParams proto
    let res = procProtoResources proto
    let ProcDefSrc body = procImpln pd
    (params', body', tmp') <- evalStateT (globaliseProc pos (Just name) variant
                                            detism params res body)
                                $ initResourceState (Just False) tmp
    let proto' = proto { procProtoParams=params' }
    let pd' = pd { procProto=proto', procTmpCount=tmp',
                   procImpln=ProcDefSrc body' }
    logResources "--------------------------------------\n"
    logResources $ "Globalising results in:" ++ showProcDef 4 pd'
    return pd'


-- Globalise a proc, tranforming resources into globals.
-- This returns an updated list of Params, transofrmed list of Stmts (body),
-- and the value of the tmpCtr after globalising the proc
globaliseProc :: OptPos -> Maybe ProcName -> ProcVariant
              -> Determinism -> [Param] -> Set ResourceFlowSpec
              -> [Placed Stmt] -> Resourcer ([Param], [Placed Stmt], Int)
globaliseProc pos name variant detism params ress body = do
    logResourcer $ "Globalising proc " ++ fromMaybe "un-named (anon)" name
    let hasHigherResources = any paramIsResourceful params
    let (resFlows, realParams) = partitionEithers $ eitherResourceParam <$> params
    let needsGlobalParam = hasHigherResources || not (List.null resFlows)
    thisMod <- lift getModuleSpec
    let isExecMain = List.null thisMod && name == Just ""
    ResourceState{resResources=oldResources,
                  resMentioned=oldMentioned,
                  resHaveGlobals=oldHaveGlobals,
                  resTmpVars=oldTmpVars,
                  resLoopTmps=oldLoopTmps,
                  resIsExecMain=oldIsExecMain} <- get
    let res = Map.fromList $ mapFst resourceFlowRes <$> resFlows
    modify $ \s -> s{resResources=res,
                     resMentioned=res,
                     resHaveGlobals=Just needsGlobalParam,
                     resLoopTmps=Map.empty,
                     resIsExecMain=isExecMain}
    -- we must save and restore any non-out-flowing resources, as we cannot be
    -- sure theyre not mutated
    let ress' = [res | ResourceFlowSpec res flow <- Set.toList ress
                , not $ flowsOut flow
                , not $ isSpecialResource res ]
    body' <- fst <$> globaliseStmts [UseResources ress' (Just Map.empty) body
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
    body'' <- if detism /= SemiDet && detism /= Failure
                || Map.null newMentioned
              then return body'
              else do
                (saves, restores, tmpVars, _) <- saveRestoreResourcesTmp pos
                                            $ Map.toList newMentioned
                return $ saves
                      ++ [Unplaced $ Cond (seqToStmt body')
                            []
                            (restores ++ [Unplaced Fail])
                            (Just tmpVars) (Just tmpVars) (Just Set.empty)]
    modify $ \s -> s{resResources=oldResources,
                     resHaveGlobals=oldHaveGlobals,
                     resTmpVars=oldTmpVars,
                     resLoopTmps=oldLoopTmps,
                     resIsExecMain=oldIsExecMain,
                     resMentioned=oldMentioned `Map.union` newMentioned}
    tmp <- gets resTmpCtr
    -- executable main gets special treatment
    -- in-flowing resources must be stored, and parameters are unmodified
    return $ if isExecMain
    then let inRes = List.filter (flowsIn . resourceFlowFlow . fst) resFlows
             stores = storeResource pos . mapFst resourceFlowRes <$> inRes
         in (params, stores ++ body'', tmp)
    else (realParams, body'', tmp)


-- Globalise a list of Stmts, tranforming resources into globals
-- The returned bool indicates if any of the Stmts could modify globals
globaliseStmts :: [Placed Stmt] -> Resourcer ([Placed Stmt], Bool)
globaliseStmts pstmts = (concat *** or) . unzip
                     <$> mapM (placedApply globaliseStmt) pstmts


-- Globalise a Stmt, tranforming resources into globals
-- The returned bool indicates if the Stmt could modify a global
globaliseStmt :: Stmt -> OptPos -> Resourcer ([Placed Stmt], Bool)
globaliseStmt (ProcCall fn@(First m n mbId) d r args) pos = do
    let procID = trustFromJust "transformStmt" mbId
    let (res, args') = partitionEithers $ placedApply eitherResourceExp <$> args
    (args'', ins, outs) <- globaliseExps args'
    let argTys = fromMaybe AnyType . maybeExpType . content <$> args''
    let hasResfulHigherArgs = any isResourcefulHigherOrder argTys
    let needsGlobals = not (List.null res) || hasResfulHigherArgs
    unlessM ((not needsGlobals ||) . trustFromJust "globaliseStmt first"
                <$> gets resHaveGlobals)
        $ lift $ errmsg pos $ "Cannot make resourceful call to " ++ showProcName n
                           ++ " in current context"
    proto <- procProto <$> lift (getProcDef $ ProcSpec m n procID generalVersion)
    let paramTys = paramType <$> procProtoParams proto
    let globals = any isResourcefulHigherOrder paramTys || not (List.null res)
    return (loadStoreResources pos ins outs
                [ProcCall fn d r args'' `maybePlace` pos],
            globals || not (Map.null outs))
globaliseStmt (ProcCall (Higher fn) d r args) pos = do
    (fn':args', ins, outs) <- globaliseExps $ fn:args
    let globals = case maybeExpType $ content fn' of
                    Just (HigherOrderType mods _) -> modifierResourceful mods
                    _ -> shouldnt "glabalise badly typed higher"
    unlessM ((not globals ||) . trustFromJust "globaliseStmt higher"
                <$> gets resHaveGlobals)
        $ lift $ errmsg pos $ "Cannot make resourceful call to " ++ show (content fn')
                           ++ " in current context"
    return (loadStoreResources pos ins outs
                [ProcCall (Higher fn') d r args' `maybePlace` pos],
            globals)
globaliseStmt (ForeignCall lang name flags args) pos = do
    (args', ins, outs) <- globaliseExps args
    return (loadStoreResources pos ins outs
                [ForeignCall lang name flags args' `maybePlace` pos],
            not $ Map.null outs)
globaliseStmt (Cond tst thn els condVars exitVars _) pos = do
    (tst', tstGlobals) <- placedApply globaliseStmt tst
    (thn', thnGlobals) <- globaliseStmts thn
    (els', elsGlobals) <- globaliseStmts els
    (saves, restores) <- loadStoreResourcesIf pos tstGlobals
    condVars' <- fixVarDict condVars
    exitVars' <- fixVarDict exitVars
    res <- gets resResources
    return (saves ++ [Cond (seqToStmt tst') thn' (restores ++ els')
                            condVars' exitVars' (Just $ Map.keysSet res)
                        `maybePlace` pos],
            thnGlobals || elsGlobals)
globaliseStmt (And stmts) pos = do
    (stmts', globals) <- globaliseStmts stmts
    return ([And stmts' `maybePlace` pos], globals)
globaliseStmt (Or disjs vars _) pos = do
    (disjs', globals) <- unzip <$> mapM (placedApply globaliseStmt) disjs
    -- we only need to save resources, and restore before each disj if
    -- any of the init use globals
    -- the last's restoration is handled implicity
    (saves, restores) <- loadStoreResourcesIf pos $ or $ init globals
    let disjs'' = seqToStmt (head disjs')
                : (seqToStmt . (restores ++) <$> tail disjs')
    vars' <- fixVarDict vars
    res <- gets resResources
    return (saves ++ [Or disjs'' vars' (Just $ Map.keysSet res) `maybePlace` pos],
            or globals)
globaliseStmt (Not stmt) pos = do
    ([stmt'], globals) <- globaliseStmts [stmt]
    return ([Not stmt' `maybePlace` pos], globals)
globaliseStmt (TestBool exp) pos = do
    ([exp'], ins, outs) <- globaliseExps [exp `maybePlace` pos]
    -- TestBool cannot modify a resource
    unless (Map.null outs) $ shouldnt "globalise TestBool with out flowing resource"
    return (loadStoreResources pos ins outs [TestBool (content exp') `maybePlace` pos],
            False)
globaliseStmt (Loop stmts vars _) pos = do
    loopTmps <- gets resLoopTmps
    modify $ \s -> s{resLoopTmps=Map.empty}
    (stmts',usesGlobals) <- globaliseStmts stmts
    vars' <- fixVarDict vars
    res <- gets resResources
    modify $ \s -> s{resLoopTmps=loopTmps}
    return ([Loop stmts' vars' (Just $ Map.keysSet res) `maybePlace` pos], usesGlobals)
globaliseStmt (UseResources res vars stmts) pos =
    case List.filter (not . isSpecialResource) res of
        [] -> globaliseStmts stmts
        newRes' -> do
            -- this handles the resources that were previously out-of-scope
            let vars' = trustFromJust "globalise use with no vars" vars
            resTypes <- (mapSnd (trustFromJust "globalise use") <$>)
                    <$> lift (mapM (canonicaliseResourceSpec pos "use block") res)
            ResourceState{resHaveGlobals=haveGlobals,
                          resResources=resources,
                          resMentioned=mentioned,
                          resTmpVars=tmpVars,
                          resLoopTmps=loopTmps,
                          resIsExecMain=isExecMain} <- get
            let resources' = Map.fromList resTypes
            let haveGlobals' = trustFromJust "use resources with Nothing" haveGlobals
            (loads, stores, newVars, newLoopTmps) <- saveRestoreResourcesTmp pos resTypes
            modify $ \s -> s {resHaveGlobals=Just True,
                              resResources=resources `Map.union` resources',
                              resMentioned=mentioned `Map.union` resources',
                              resLoopTmps=loopTmps `Map.union` newLoopTmps}
            unless isExecMain $ modify $ \s -> s {resTmpVars=tmpVars `Map.union` newVars}
            stmts' <- fst <$> globaliseStmts stmts
            modify $ \s -> s {resHaveGlobals=haveGlobals,
                              resResources=resources,
                              resLoopTmps=loopTmps,
                              resTmpVars=tmpVars}
            -- no need to load and store resources in executable main
            if isExecMain
            then return (stmts', True)
            else return
                    -- load the old values of the resources
                (loads
                    -- store the values of the new resources,
                    -- if theyve been assigned before the use block
                ++ [storeResource pos (res, ty)
                   | (res, ty) <- resTypes
                   , resourceVar res `Map.member` vars' ]
                ++ stmts'
                    -- store the old values of the resources
                ++ stores,
                    True)
globaliseStmt Nop pos = return ([Nop `maybePlace` pos], False)
globaliseStmt Fail pos = return ([Fail `maybePlace` pos], False)
globaliseStmt Break pos = do
    restores <- restoreLoopGlobals pos
    return (restores ++ [Break `maybePlace` pos], False)
globaliseStmt Next pos = do
    restores <- restoreLoopGlobals pos
    return (restores ++ [Next `maybePlace` pos], False)
globaliseStmt Case{} _ = shouldnt "case in globalise"
globaliseStmt For{} _ = shouldnt "for in globalise"


-- | Restore global variables for a loop
restoreLoopGlobals :: OptPos -> Resourcer [Placed Stmt]
restoreLoopGlobals pos = do
    loopTmps <- gets resLoopTmps
    return [rePlace pos $ globalStore res ty
                        $ Typed (Var tmp ParamIn Ordinary) ty Nothing
           | (res, (tmp, ty)) <- Map.toList loopTmps]


-- | Globalise a list of expressions.
-- This returns a list of inflowing and outflowing resources, and keeps the
-- Resourcer monad's in and out resources in tact
globaliseExps :: [Placed Exp]
              -> Resourcer ([Placed Exp], Map ResourceSpec TypeSpec,
                                          Map ResourceSpec TypeSpec)
globaliseExps exps = do
    ResourceState{resIn=oldIn, resOut=oldOut} <- get
    modify $ \s -> s{resIn=Map.empty, resOut=Map.empty}
    exps' <- globaliseExps' exps
    state' <- get
    modify $ \s -> s{resIn=oldIn, resOut=oldOut}
    return (exps', resIn state', resOut state')


-- | Globalise a list of expresstions
globaliseExps' :: [Placed Exp] -> Resourcer [Placed Exp]
globaliseExps' = mapM (placedApply $ globaliseExp AnyType)


-- | Globalise a single expression, adding any in flowing or out flowing
-- resources to the Resourcer moand as necessary.
globaliseExp :: TypeSpec -> Exp -> OptPos -> Resourcer (Placed Exp)
globaliseExp _ (Typed exp ty cast) pos = do
    exp' <- globaliseExp ty exp pos
    return $ Typed (content exp') ty cast `maybePlace` pos
globaliseExp ty exp@(Var nm fl _) pos = do
    addResourceInOuts fl nm ty
    return $ exp `maybePlace` pos
globaliseExp _ (Closure pspec exps) pos = do
    exps' <- globaliseExps' exps
    return $ Closure pspec exps' `maybePlace` pos
globaliseExp _ (AnonProc mods@(ProcModifiers detism _ _ _ resful _ _)
                params body clsd res) pos = do
    (params', body', _) <- globaliseProc pos Nothing AnonymousProc
                                detism params Set.empty body
    let clsd' = trustFromJust "gloablise anon proc without clsd" clsd
    clsd'' <- if resful
              then (clsd' `Map.difference`) . resourceNameMap <$> gets resResources
              else do
                  mapM_ (uncurry $ addResourceInOuts ParamIn) $ Map.toList clsd'
                  return clsd'
    return $ AnonProc mods params' body' (Just clsd'') res `maybePlace` pos
globaliseExp _ exp pos = return $ exp `maybePlace` pos


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


-- | Given a ResourceSpec and something, return Right of something if the
-- resource is a special resource, else Left of that resource
eitherResource :: ResourceSpec -> a -> Either ResourceSpec a
eitherResource res a =
    if isSpecialResource res
    then Right a
    else Left res


-- | Given a Param, return either the (ResourceFlowSpec, TypeSpec) associated
-- with the parameter or the param itself
eitherResourceParam :: Param -> Either (ResourceFlowSpec, TypeSpec) Param
eitherResourceParam param@(Param _ ty fl (Resource res)) =
    mapLeft ((,ty) . (`ResourceFlowSpec` fl))
    $ eitherResource res param
eitherResourceParam param = Right param


-- | Given an Exp, return either the ResourceSpec associated with a Var, else
-- the Exp itself
eitherResourceExp :: Exp -> OptPos -> Either ResourceSpec (Placed Exp)
eitherResourceExp var@(Typed (Var _ _ (Resource res)) ty _) pos =
    eitherResource res $ var `maybePlace` pos
eitherResourceExp exp pos = Right $ exp `maybePlace` pos


-- | Add tmp variables into a resource dictionary. If we are globalising, we
-- remove resources from the dict, and if the flag is true, we also
-- add the #globals variable
fixVarDict :: Maybe VarDict -> Resourcer (Maybe VarDict)
fixVarDict Nothing = return Nothing
fixVarDict (Just vars) = do
    ress <- resourceNameMap <$> gets resResources
    tmpVars <- gets resTmpVars
    haveGlobals <- gets resHaveGlobals
    let filter res _ = not $ res `Map.member` ress
    Just <$> if isJust haveGlobals
    then return $ Map.filterWithKey filter vars `Map.union` tmpVars
    else return $ vars `Map.union` tmpVars


-- | Get a var as a resource of the given type
getResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
getResource nm (rs, ty) = varGetTyped nm ty `setExpFlowType` Resource rs


-- | Set a var as a resource of the given type
setResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
setResource nm (rs, ty) = varSetTyped nm ty `setExpFlowType` Resource rs


-- | Save and restore the given resources in tmp variables
saveRestoreResourcesTmp :: OptPos -> [(ResourceSpec, TypeSpec)]
                        -> Resourcer ([Placed Stmt], [Placed Stmt], VarDict,
                                      Map ResourceSpec (VarName, TypeSpec))
saveRestoreResourcesTmp pos resTys = do
    tmp <- gets resTmpCtr
    modify $ \s -> s{resTmpCtr=tmp + length resTys}
    global <- isJust <$> gets resHaveGlobals
    let tmpVars = mkTempName <$> [tmp..]
        (res, tys) = unzip resTys
        ress = zip tmpVars resTys
        localSave (t,(rs,ty)) = move (getResource (resourceVar rs) (rs,ty))
                                     (setResource t (rs,ty))
        localRestore (t,(rs,ty)) = move (getResource t (rs,ty))
                                        (setResource (resourceVar rs) (rs,ty))
        globalSave (t,(rs,ty)) = globalLoad rs ty $ setResource t (rs,ty)
        globalRestore (t,(rs,ty)) = globalStore rs ty $ getResource t (rs,ty)
        (save, restore) = if global
                          then (globalSave, globalRestore)
                          else (localSave, localRestore)
    return (rePlace pos . save <$> ress, rePlace pos . restore <$> ress,
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
loadStoreResourcesIf :: OptPos -> Bool -> Resourcer ([Placed Stmt],[Placed Stmt])
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
