--  File     : Resources.hs
--  Author   : Peter Schachte
--  Purpose  : Resource checker for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


{-# LANGUAGE TupleSections #-}


module Resources (resourceCheckMod, canonicaliseProcResources,
                  canonicaliseResourceSpec,
                  transformProcResources, transformProcGlobals,
                  specialResourcesSet, isSpecialResource) where

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
    resResources      :: Set ResType,
    resTmpVars        :: VarDict,
    resIn             :: Set ResType,
    resOut            :: Set ResType,
    resHaveGlobals    :: Maybe Bool,
    resTmpCtr         :: Int
}

-- | Initial ResourceState given a tmpCtr
initResourceState :: Maybe Bool -> Int -> ResourceState
initResourceState globals tmp = ResourceState{resResources=Set.empty,
                                              resTmpVars=Map.empty,
                                              resIn=Set.empty,
                                              resOut=Set.empty,
                                              resHaveGlobals=globals,
                                              resTmpCtr=tmp}


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
    modify $ \s -> s{resResources=Set.fromList $ mapFst resourceFlowRes <$> resFlows}
    logResourcer $ "Declared resources: " ++ show resFlows
    body' <- transformStmts body
    tmp' <- gets resTmpCtr
    return (body', resourceParams <$> resFlows, tmp')


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
    args' <- transformExps args
    resArgs <- concat <$> mapM (resourceArgs pos) callResFlows
    return [maybePlace (ProcCall func detism False $ args' ++ resArgs) pos]
transformStmt stmt@(ProcCall (Higher func) detism resourceful args) pos = do
    (func':args') <- transformExps $ func:args
    case content func' of
        Typed _ (HigherOrderType ProcModifiers{modifierResourceful=Resourceful} _) _ -> do
            unless resourceful
                $ lift $ errmsg pos
                $ "Resourceful higher order call without ! resource marker: "
                    ++ showStmt 4 stmt
            return [maybePlace (ProcCall (Higher func') detism False args') pos]
        Typed _ (HigherOrderType _ _) _ ->
            return [maybePlace (ProcCall (Higher func') detism False args') pos]
        _ -> shouldnt $ "bad resource higher call type" ++ show stmt
transformStmt (ForeignCall lang name flags args) pos = do
    args' <- transformExps args
    return [maybePlace (ForeignCall lang name flags args') pos]
transformStmt (TestBool var) pos = do
    var' <- transformExp var pos
    return [maybePlace (TestBool $ content var') pos]
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
    vars' <- forM vars fixVarDict
    return [maybePlace (Or [seqToStmt stmt',seqToStmt stmt''] vars') pos]
transformStmt (Not stmt) pos = do
    stmt' <- placedApplyM transformStmt stmt
    return [maybePlace (Not $ seqToStmt stmt') pos]
transformStmt (Cond test thn els condVars defVars) pos = do
    test' <- placedApplyM transformStmt test
    thn' <- transformStmts thn
    els' <- transformStmts els
    condVars' <- forM condVars fixVarDict
    defVars' <- forM defVars fixVarDict
    return [maybePlace (Cond (Unplaced $ And test')
            thn' els' condVars' defVars') pos]
transformStmt (Case exp cases deflt) pos = do
    exp' <- placedApply transformExp exp
    cases' <- transformCases cases
    deflt' <- forM deflt transformStmts
    return [maybePlace (Case exp' cases' deflt') pos]
transformStmt (Loop body vars) pos = do
    body' <- transformStmts body
    vars' <- forM vars fixVarDict
    return [maybePlace (Loop body' vars') pos]
transformStmt (For generators body) pos = do
    body' <- transformStmts body
    return [maybePlace (For generators body') pos]
transformStmt (UseResources res beforeVars afterVars body) pos = do
    resMbTypes <- lift $ mapM (canonicaliseResourceSpec pos "use statement")
                              res
    let resTys = mapSnd (trustFromJust "transformStmt UseResources")
               <$> resMbTypes
    s@ResourceState{resResources=oldResTypes,
                    resTmpVars=oldTmp} <- get
    let (saving, postponing) = List.partition (`Set.member` oldResTypes) resTys
    (saves, restores, tmpVars) <- saveRestoreResourcesTmp saving
    modify $ \s -> s{resTmpVars=Map.union tmpVars oldTmp,
                     resResources=oldResTypes `Set.union` Set.fromList saving}
    body' <- transformStmts body
    modify $ \s -> s{ resTmpVars=oldTmp }
    let body'' = if List.null postponing
                 then body'
                 else [UseResources (fst <$> postponing) beforeVars afterVars body'
                        `maybePlace` pos]
    return $ saves ++ body'' ++ restores
transformStmt Nop pos = return [maybePlace Nop pos]
transformStmt Fail pos = return [maybePlace Fail pos]
transformStmt Break pos = return [maybePlace Break pos]
transformStmt Next pos = return [maybePlace Next pos]


-- | Get a var as a resource of the given type
getResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
getResource nm (rs, ty) = varGet nm `withType` ty `setExpFlowType` Resource rs


-- | Set a var as a resource of the given type
setResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
setResource nm (rs, ty) = varSet nm `withType` ty `setExpFlowType` Resource rs


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
    res <- Set.map (mapFst (`ResourceFlowSpec` ParamInOut)) <$> gets resResources
    let (params', res') = if modifierResourceful mods == Resourceful
                  then (params ++ (resourceParams <$> Set.toList res), 
                        Set.map fst res)
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

transformProcGlobals :: ProcDef -> Int -> Compiler ProcDef
transformProcGlobals pd _ = do
    logResources "--------------------------------------\n"
    logResources $ "Globalising resources in:" ++ showProcDef 4 pd
    let name = procName pd
    let proto = procProto pd
    let detism = procDetism pd
    let pos = procPos pd
    let tmp = procTmpCount pd
    let params = procProtoParams proto
    let res = procProtoResources proto
    let ProcDefSrc body = procImpln pd
    (params', body', tmp') <- evalStateT
                                (globaliseProc (Just name) detism params res body)
                                $ initResourceState (Just False) tmp
    let proto' = proto { procProtoParams=params' }
    let pd' = pd { procProto=proto', procTmpCount=tmp',
                   procImpln=ProcDefSrc body' }
    logResources "--------------------------------------\n"
    logResources $ "Globalising results in:" ++ showProcDef 4 pd'
    return pd'

eitherResource :: ResourceSpec -> a -> Either ResourceSpec a
eitherResource res a =
    if isSpecialResource res
    then Right a
    else Left res


eitherResourceParam :: Param -> Either (ResourceFlowSpec, TypeSpec) Param
eitherResourceParam param@(Param _ ty fl (Resource res)) =
    mapLeft ((,ty) . (`ResourceFlowSpec` fl))
    $ eitherResource res param
eitherResourceParam param = Right param


eitherResourceExp :: Exp -> OptPos -> Either ResourceSpec (Placed Exp)
eitherResourceExp var@(Typed (Var _ _ (Resource res)) ty _) pos =
    eitherResource res $ var `maybePlace` pos
eitherResourceExp exp pos = Right $ exp `maybePlace` pos


globaliseProc :: Maybe ProcName -> Determinism -> [Param] -> Set ResourceFlowSpec
              -> [Placed Stmt] -> Resourcer ([Param], [Placed Stmt], Int)
globaliseProc name detism params ress body = do
    let hasHigherResources = any paramIsResourceful params
    let (resFlows, realParams) = partitionEithers $ eitherResourceParam <$> params
    let needsGlobalParam = hasHigherResources || not (List.null resFlows)
    ResourceState{resResources=oldResources,
                  resHaveGlobals=oldHaveGlobals,
                  resTmpVars=oldTmpVars} <- get
    modify $ \s -> s{resResources=oldResources `Set.union`
                                    Set.fromList (mapFst resourceFlowRes <$> resFlows),
                     resHaveGlobals=Just needsGlobalParam }
    let ress' = [res | ResourceFlowSpec res flow <- Set.toList ress
                     , not $ flowsOut flow
                     , not $ isSpecialResource res ]
    body' <- fst <$> globaliseStmts (if List.null ress'
                                     then body
                                     else [Unplaced $ UseResources ress'
                                                        (Just Map.empty)
                                                        (Just Map.empty) body])
    tmp' <- gets resTmpCtr
    modify $ \s -> s{resResources=oldResources,
                     resHaveGlobals=oldHaveGlobals,
                     resTmpVars=oldTmpVars}
    mod <- lift getModuleSpec
    let (body'', params')
         = if List.null mod && name == Just ""
           then let inRes = List.filter (flowsIn . resourceFlowFlow . fst) resFlows
                    -- executable main gets special treatment
                    -- any initial loads, and subsequent stores are redundant
                    body'' = (storeResource . mapFst resourceFlowRes <$> inRes)
                          ++ takeWhile (not . isGlobalStore . content)
                             (dropWhile (isGlobalLoad . content) body')
                in (body'', params)
           else (body', realParams)
    return (params' ++ [globalsParam | needsGlobalParam], body'', tmp')

globaliseStmts :: [Placed Stmt] -> Resourcer ([Placed Stmt], Bool)
globaliseStmts pstmts = (concat *** or) . unzip
                     <$> mapM (placedApply globaliseStmt) pstmts

globaliseStmt :: Stmt -> OptPos -> Resourcer ([Placed Stmt], Bool)
globaliseStmt (ProcCall fn@First{} d r args) pos = do
    let (res, args') = partitionEithers $ placedApply eitherResourceExp <$> args
    (args'', ins, outs) <- globaliseExps args'
    let argTys = fromMaybe AnyType . maybeExpType . content <$> args''
    let hasResfulHigherArgs = any isResourcefulHigherOrder argTys
    let globals = not (List.null res) || hasResfulHigherArgs
    let args''' = if globals then args'' ++ globalsGetSet else args''
    return (loadStoreResources ins outs
                [ProcCall fn d r args''' `maybePlace` pos],
            globals || not (Set.null ins) || not (Set.null outs))
globaliseStmt (ProcCall (Higher fn) d r args) pos = do
    (fn':args', ins, outs) <- globaliseExps $ fn:args
    let globals = case content fn' of
            Typed _ (HigherOrderType mods _) _ ->
                modifierResourceful mods == Resourceful
            _ -> shouldnt "globalise untyped higher"
    let args'' = if globals then args' ++ globalsGetSet else args'
    return (loadStoreResources ins outs
                [ProcCall (Higher fn) d r args'' `maybePlace` pos],
            globals)
globaliseStmt (ForeignCall lang name flags args) pos = do
    (args', ins, outs) <- globaliseExps args
    return (loadStoreResources ins outs
                [ForeignCall lang name flags args' `maybePlace` pos],
            not $ Set.null outs)
globaliseStmt (Cond tst thn els condVars exitVars) pos = do
    (tst', tstGlobals) <- placedApply globaliseStmt tst
    (thn', thnGlobals) <- globaliseStmts thn
    (els', elsGlobals) <- globaliseStmts els
    (saves, restores)
        <- if tstGlobals
            then do
                res <- gets resResources
                (saves, restores, _) <- saveRestoreResourcesTmp $ Set.toList res
                return (saves, restores)
            else return ([], [])
    condVars' <- forM condVars fixVarDict
    exitVars' <- forM exitVars fixVarDict
    return (saves ++ [Cond (seqToStmt tst') thn' (restores ++ els')
                                    condVars' exitVars' `maybePlace` pos],
            thnGlobals || elsGlobals)
globaliseStmt (And stmts) pos = do
    (stmts', globals) <- globaliseStmts stmts
    return ([And stmts' `maybePlace` pos], globals)
globaliseStmt (Or disjs vars) pos = do
    (disjs', globals) <- unzip <$> mapM (placedApply globaliseStmt) disjs
    let globals' = or $ init globals
    (saves, restores)
        <- if globals'
            then do
                res <- gets resResources
                (saves, restores, _) <- saveRestoreResourcesTmp $ Set.toList res
                return (saves, restores)
            else return ([], [])
    -- only need to restore globals in tail of disjs'
    let disjs'' = seqToStmt (head disjs')
                : (seqToStmt . (restores ++) <$> tail disjs')
    vars' <- forM vars fixVarDict
    return (saves ++ [Or disjs'' vars' `maybePlace` pos],
            or globals)
globaliseStmt (Not stmt) pos = do
    ([stmt'], globals) <- globaliseStmts [stmt]
    return ([Not stmt' `maybePlace` pos], globals)
globaliseStmt (TestBool exp) pos = do
    ([exp'], ins, outs) <- globaliseExps [exp `maybePlace` pos]
    -- TestBool cannot modify a resource 
    unless (Set.null outs)
        $ shouldnt "globalise TestBool with out flowing resource"
    return (loadStoreResources ins outs [TestBool (content exp') `maybePlace` pos],
            False)
globaliseStmt (Loop stmts vars) pos = do
    (stmts',usesGlobals) <- globaliseStmts stmts
    vars' <- forM vars fixVarDict
    return ([Loop stmts' vars' `maybePlace` pos], usesGlobals)
globaliseStmt (UseResources newRes beforeVars afterVars stmts) pos = do
    -- this handles the reosurces that were previously out-of-scope
    let beforeVars' = trustFromJust "globalise use with no before" beforeVars
    let afterVars' = trustFromJust "globalise use with no after" afterVars
    newResTypes <- lift $ mapM (canonicaliseResourceSpec pos "use block") newRes
    let newResTypes' = mapSnd (trustFromJust "globalise use") <$> newResTypes
    let newResTypesSet = Set.fromList newResTypes'
    state@ResourceState{resHaveGlobals=haveGlobals,
                        resResources=resources,
                        resTmpVars=tmpVars} <- get
    let haveGlobals' = trustFromJust "use resources with Nothing" haveGlobals
    (loads, stores, newVars) <- saveRestoreResourcesTmp newResTypes'
    modify $ \s -> s {resHaveGlobals=Just True,
                      resResources=resources `Set.union` newResTypesSet,
                      resTmpVars=tmpVars `Map.union` newVars}
    stmts' <- fst <$> globaliseStmts stmts
    modify $ \s -> s {resHaveGlobals=haveGlobals,
                      resResources=resources,
                      resTmpVars=tmpVars}
    return  -- initialise a "new" global variable, if we need to
            ([move (iVal 0 `withType` phantomType)
                   (varSet globalsName `withType` phantomType)
             | not haveGlobals' ]
             -- load the old values of the resources
          ++ loads
             -- store the values of the new resources, 
             -- if theyve been assigned before the use block
          ++ [storeResource (res,ty)
             | (res, ty) <- newResTypes'
             , resourceVar res `Map.member` beforeVars' ]
          ++ stmts'
             -- load the new values of the new resources, 
             -- if theyve been assigned in or before the use block
          ++ [loadResource (res,ty)
             | (res, ty) <- newResTypes'
             , resourceVar res `Map.member` afterVars' ]
             -- store the old values of the resources
          ++ stores
             -- ensure the "new" global (if any) cannot get optimised away
          ++ [lpvmVoid [varGet globalsName `withType` phantomType `maybePlace` pos]
             | not haveGlobals' ],
            True)
globaliseStmt Nop pos = return ([Nop `maybePlace` pos], False)
globaliseStmt Fail pos = return ([Fail `maybePlace` pos], False)
globaliseStmt Break pos = return ([Break `maybePlace` pos], False)
globaliseStmt Next pos = return ([Next `maybePlace` pos], False)
globaliseStmt (Case _ _ _) _ = shouldnt "case in globalise"
globaliseStmt (For _ _) _ = shouldnt "for in globalise"


globaliseExps :: [Placed Exp]
              -> Resourcer ([Placed Exp], Set ResType, Set ResType)
globaliseExps exps = do
    ResourceState{resIn=oldIn, resOut=oldOut} <- get
    modify $ \s -> s{resIn=Set.empty, resOut=Set.empty}
    exps' <- globaliseExps' exps
    state' <- get
    modify $ \s -> s{resIn=oldIn, resOut=oldOut}
    return (exps', resIn state', resOut state')

globaliseExps' :: [Placed Exp] -> Resourcer [Placed Exp]
globaliseExps' = mapM (placedApply $ globaliseExp AnyType)

globaliseExp :: TypeSpec -> Exp -> OptPos -> Resourcer (Placed Exp)
globaliseExp _ (Typed exp ty cast) pos = do
    exp' <- globaliseExp ty exp pos
    return $ Typed (content exp') ty cast `maybePlace` pos
globaliseExp ty exp@(Var nm fl _) pos = do
    addResourceInOuts fl nm ty
    return $ exp `maybePlace` pos
globaliseExp _ (ProcRef pspec exps) pos = do
    exps' <- globaliseExps' exps
    return $ ProcRef pspec exps' `maybePlace` pos
globaliseExp _ (AnonProc mods@(ProcModifiers detism _ _ resful _ _)
                params body clsd res) pos = do
    (params', body', _) <- globaliseProc Nothing detism params Set.empty body
    clsd' <- if resful == Resourceful
             then forM clsd fixVarDict
             else do
                 return clsd
    return $ AnonProc mods params' body' clsd res `maybePlace` pos
globaliseExp _ exp pos = return $ exp `maybePlace` pos


addResourceInOuts :: FlowDirection -> VarName -> TypeSpec -> Resourcer ()
addResourceInOuts fl nm ty = do
    ress <- resourceNameMap <$> gets resResources
    forM_ (Map.lookup nm ress)
        $ \res -> modify (\s -> s{resIn=resIn s `Set.union` 
                                            Set.fromList [(res,ty) | flowsIn fl],
                                  resOut=resOut s `Set.union` 
                                            Set.fromList [(res,ty) | flowsOut fl]})

fixVarDict :: VarDict -> Resourcer VarDict
fixVarDict vars = do
    ress <- resourceNameMap <$> gets resResources
    tmpVars <- gets resTmpVars
    haveGlobals <- gets resHaveGlobals
    let filter res _ = not $ res `Map.member` ress
    if isJust haveGlobals
    then return $ Map.filterWithKey filter vars
                  `Map.union` tmpVars
                  `Map.union` Map.fromList [ (globalsName, phantomType)
                                           | haveGlobals == Just True ]
    else return $ vars `Map.union` tmpVars

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


-- | The set of VarNames that correspond to sepcial resources
specialResourcesSet :: Set VarName
specialResourcesSet = keysSet specialResources


-- | Test if ResourceSpec refers to a special resource
isSpecialResource :: ResourceSpec -> Bool
isSpecialResource (ResourceSpec [] nm) = nm `Set.member` specialResourcesSet
isSpecialResource _                    = False



-- | Save and restore the given resources in tmp variables
saveRestoreResourcesTmp :: [ResType]
                        -> Resourcer ([Placed Stmt], [Placed Stmt], VarDict)
saveRestoreResourcesTmp resTys = do
    tmp <- gets resTmpCtr
    modify $ \s -> s{resTmpCtr=tmp + length resTys}
    global <- isJust <$> gets resHaveGlobals
    let tmpVars = mkTempName <$> [tmp..]
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
    return (save <$> ress, restore <$> ress,
            Map.fromList $ zip tmpVars (snd <$> resTys))


-- | Store the given resource in globals
storeResource :: ResType -> Placed Stmt
storeResource rsTy@(rs,ty) =
    globalStore rs ty (getResource (resourceName rs) rsTy)


-- | Store the given resource in globals
storeResources :: Set ResType -> [Placed Stmt]
storeResources = (storeResource <$>) . Set.toList


-- | Load the given resource from globals
loadResource :: ResType -> Placed Stmt
loadResource rsTy@(rs,ty) =
    globalLoad rs ty (setResource (resourceName rs) rsTy)


-- | Load the given resource from globals
loadResources :: Set ResType -> [Placed Stmt]
loadResources = (loadResource <$>) . Set.toList


-- | Surround a given list of statements with loads/stores to the given 
-- resourcces 
loadStoreResources :: Set ResType -> Set ResType
                   -> [Placed Stmt] -> [Placed Stmt]
loadStoreResources inRes outRes stmts =
    loadResources inRes ++ stmts ++ storeResources outRes


resourceNameMap :: Set ResType -> Map VarName ResourceSpec
resourceNameMap = Map.fromList . Set.toList
                               . Set.map (((,) =<< resourceName) . fst)


-- |Log a message, if we are logging resource transformation activity.
logResources :: String -> Compiler ()
logResources s = logMsg Resources s

logResourcer :: String -> Resourcer ()
logResourcer s = lift $ logMsg Resources s

logGlobals :: String -> Resourcer ()
logGlobals s = lift $ logMsg Resources s