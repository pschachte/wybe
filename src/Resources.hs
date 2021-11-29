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


checkResourceDef :: Ident -> ResourceDef ->
                    Compiler (Bool,[(String,OptPos)],(Ident,ResourceDef))
checkResourceDef name def = do
    (chg,errs,m) <-
        fmap unzip3 $ mapM (uncurry checkOneResource) $ Map.toList def
    return (or chg, concat errs, (name,Map.fromList m))


checkOneResource :: ResourceSpec -> ResourceImpln ->
                    Compiler (Bool,[(String,OptPos)],
                              (ResourceSpec,ResourceImpln))
checkOneResource rspec impln@(SimpleResource ty init pos) = do
    logResources $ "Check resource " ++ show rspec ++
           " with implementation " ++ show impln
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
    let lst = Set.elems $ procProtoResources proto
    resourceFlows <- Set.fromList <$>
                     mapM (canonicaliseResourceFlow pos) lst
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
    return $ spec { resourceFlowRes = fst resTy}


--------- Transform resources into variables and parameters ---------

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
    logResources $ "--------------------------------------\n"
    logResources $ "Adding resources to:" ++ showProcDef 4 pd
    let proto = procProto pd
    let pos = procPos pd
    let tmp = procTmpCount pd
    let resourceFlows = procProtoResources proto
    let params = procProtoParams proto
    let (ProcDefSrc body) = procImpln pd
    resFlows <- concat <$> mapM (simpleResourceFlows pos)
                           (Set.elems resourceFlows)
    let (specials, resFlows') = partitionSpecials fst resFlows
    logResources $ "Declared resources: " ++ show resFlows
    (body',tmp') <- transformBody tmp (mapFst resourceFlowRes <$> resFlows') body
    let isResFul = any (isResourcefulHigherOrder . paramType) params 
                || not (List.null resFlows') 
    specialParams <- concat <$> mapM (resourceParams pos) specials
    thisMod <- getModuleSpec
    pd' <- if List.null thisMod && procName pd == "" 
           then do 
                let inRes = List.filter (flowsIn . resourceFlowFlow . fst) resFlows
                let body'' = (storeResource . mapFst resourceFlowRes <$> inRes)
                          ++ dropWhile (isGlobalLoad . content) 
                             (takeWhile (not . isGlobalStore . content) body')
                params' <- concat <$> mapM (resourceParams pos) resFlows'
                let proto' = proto { procProtoParams=params' ++ [globalsParam]}
                return $ pd { procProto=proto', procTmpCount=tmp',
                              procImpln=ProcDefSrc body'' }
           else do 
                let proto' = proto { procProtoParams=params ++ specialParams
                                                            ++ [globalsParam | isResFul]}
                return pd { procProto=proto', procTmpCount=tmp',
                            procImpln=ProcDefSrc body' }
    logResources $ "Adding resources results in:" ++ showProcDef 4 pd'
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


resourceParams :: OptPos -> (ResourceFlowSpec,TypeSpec) -> Compiler [Param]
resourceParams pos (ResourceFlowSpec res flow, typ) = do
    varName <- resourceVar res
    let inParam  = [Param varName typ ParamIn (Resource res) | flowsIn flow]
    let outParam = [Param varName typ ParamOut (Resource res) | flowsOut flow]
    return $ inParam ++ outParam

type ResType = (ResourceSpec, TypeSpec)

-- | Transform a statement sequence, turning resources into arguments.
transformBody :: Int -> [ResType] -> [Placed Stmt]
              -> Compiler ([Placed Stmt],Int)
transformBody tmp _ [] = return ([],tmp)
transformBody tmp resources (stmt:stmts) = do
    (stmts1,tmp') <- placedApply (transformStmt tmp resources) stmt
    (stmts2,tmp'') <- transformBody tmp' resources stmts
    return (stmts1 ++ stmts2, tmp'')


-- | Transform a single statement, turning resources into arguments.
transformStmt :: Int -> [ResType] -> Stmt -> OptPos
              -> Compiler ([Placed Stmt], Int)
transformStmt tmp res stmt@(ProcCall func@(First m n pid) detism resourceful args) pos = do
    let procID = trustFromJust "transformStmt" pid
    callResFlows <-
        Set.toList . procProtoResources . procProto <$> getProcDef
                (ProcSpec m n procID generalVersion)
    let argTys = fromMaybe AnyType . maybeExpType . content <$> args
    let hasResfulHigherArgs = any isResourcefulHigherOrder argTys
    let usesResources = not (List.null callResFlows) || hasResfulHigherArgs
    unless (resourceful || not usesResources)
      $ message Error
        ("Call to resourceful proc without ! resource marker: "
         ++ showStmt 4 stmt)
        pos
    logResources $ "Checking call to " ++ n ++ " using " ++ show callResFlows
    (args', tmp', inRes, outRes) <- transformExps tmp res args 
    let (specialRes,globalRes) = partitionSpecials id callResFlows
    specialArgs <- concat <$> mapM (resourceArgs pos) specialRes
    let usesGlobals = not (List.null globalRes) || hasResfulHigherArgs
    let stmt' = [maybePlace (ProcCall func detism False 
                             $ args' ++ specialArgs 
                                     ++ if usesGlobals then globalsGetSet else []) pos]
    return (loadStoreResources inRes outRes stmt', tmp')
transformStmt tmp res stmt@(ProcCall (Higher func) detism resourceful args) pos = do
    (func':args', tmp', inRes, outRes) <- transformExps tmp res (func:args) 
    case content func' of
        Typed _ (HigherOrderType ProcModifiers{modifierResourceful=Resourceful} _) _ -> do
            unless resourceful
                $ message Error
                    ("Resourceful higher order call without ! resource marker: "
                    ++ showStmt 4 stmt)
                    pos
            return (loadStoreResources inRes outRes 
                        [maybePlace (ProcCall (Higher func') detism False 
                                    $ args' ++ globalsGetSet) pos], tmp')
        Typed _ (HigherOrderType _ _) _ ->
            return (loadStoreResources inRes outRes 
                    [maybePlace (ProcCall (Higher func') detism False args') pos], tmp')
        _ -> shouldnt $ "bad resource higher call type" ++ show stmt 
transformStmt tmp res (ForeignCall lang name flags args) pos = do
    (args', tmp', inRes, outRes) <- transformExps tmp res args
    return (loadStoreResources inRes outRes 
            [maybePlace (ForeignCall lang name flags args') pos], tmp')
transformStmt tmp res (TestBool var) pos = do
    (var', tmp', inRes, outRes) <- transformExp tmp res AnyType var Nothing
    return (loadStoreResources inRes outRes 
            [maybePlace (TestBool $ content var') pos], tmp)
transformStmt tmp res (And stmts) pos = do
    (stmts',tmp') <- transformBody tmp res stmts
    return ([maybePlace (And stmts') pos], tmp')
transformStmt tmp res (Or [] _) pos =
    return ([failTest], tmp)
transformStmt tmp res (Or [stmt] _) pos = do
    placedApplyM (transformStmt tmp res) stmt
transformStmt tmp res (Or (stmt:stmts) vars) pos = do
    (stmt',tmp')  <- placedApplyM (transformStmt tmp res) stmt
    (stmt'',tmp'') <- transformStmt tmp' res (Or stmts vars) pos
    resVars <- Set.fromList <$> mapM resourceVar (fst <$> res)
    let vars' = resourcelessVarDict resVars <$> vars
    return ([maybePlace (Or [makeSingleStmt stmt',makeSingleStmt stmt''] vars')
              pos], tmp'')
transformStmt tmp res (Not stmt) pos = do
    (stmt',tmp') <- placedApplyM (transformStmt tmp res) stmt
    return ([maybePlace (Not $ makeSingleStmt stmt') pos], tmp')
transformStmt tmp res Nop _ =
    return ([], tmp)
transformStmt tmp res Fail pos =
    return ([maybePlace Fail pos], tmp)
transformStmt tmp res (Cond test thn els condVars defVars) pos = do
    (test',tmp1) <- placedApplyM (transformStmt tmp res) test
    (thn',tmp2) <- transformBody tmp1 res thn
    (els',tmp3) <- transformBody tmp2 res els
    resVars <- Set.fromList <$> mapM resourceVar (fst <$> res)
    let condVars' = resourcelessVarDict resVars <$> condVars
    let defVars'  = resourcelessVarDict resVars <$> defVars
    return ([maybePlace
             (Cond (Unplaced $ And test') thn' els' condVars' defVars') pos],
            tmp3)
transformStmt tmp res (Case expr cases deflt) pos = do
    (cases',tmp1) <- transformCases tmp res cases
    (deflt',tmp2) <- case deflt of
        Nothing -> return (Nothing, tmp1)
        Just def -> mapFst Just <$> transformBody tmp1 res def
    return ([maybePlace
             (Case expr cases' deflt') pos],
            tmp2)
transformStmt tmp res (Loop body defVars) pos = do
    (body',tmp') <- transformBody tmp res body
    resVars <- Set.fromList <$> mapM resourceVar (fst <$> res)
    let defVars' = resourcelessVarDict resVars <$> defVars
    return ([maybePlace (Loop body' defVars') pos], tmp')
transformStmt tmp res (For generators body) pos = do
    (body', tmp') <- transformBody tmp res body
    return ([maybePlace (For generators body') pos], tmp')
transformStmt tmp res (UseResources allRes oldRes body) pos = do
    resTypes <- mapM ((mapSnd fromJust <$>) 
                         <$> canonicaliseResourceSpec pos "use statement") allRes
    let (saves, restores, tmp') = saveRestoreResourcesTmp tmp resTypes
    (body',tmp'') <- transformBody tmp' (List.nub $ res ++ resTypes) body
    return (saves ++ body' ++ restores, tmp'')
transformStmt tmp res Break pos =
    return ([maybePlace Break pos], tmp)
transformStmt tmp res Next pos =
    return ([maybePlace Next pos], tmp)


-- | Get a var as a resource of the given type
getResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
getResource nm (rs, ty) = varGet nm `withType` ty `setExpFlowType` Resource rs


-- | Set a var as a resource of the given type
setResource :: Ident -> (ResourceSpec, TypeSpec) -> Exp
setResource nm (rs, ty) = varSet nm `withType` ty `setExpFlowType` Resource rs


-- | Save and restore the given resources in tmp variables
saveRestoreResourcesTmp :: Int -> [ResType] 
                        -> ([Placed Stmt], [Placed Stmt], Int)
saveRestoreResourcesTmp tmp resTys =
    let ress = zip (mkTempName <$> [tmp..]) resTys
        save (t,(rs,ty)) = globalLoad rs ty $ setResource t (rs,ty)
        restore (t,(rs,ty)) = globalStore rs ty $ getResource t (rs,ty)
    in (save <$> ress, restore <$> ress, tmp + length resTys)


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
resourcelessVarDict :: Set VarName -> VarDict -> VarDict
resourcelessVarDict resVars vDict = 
    Map.filterWithKey (const . (not . (`Set.member` resVars))) vDict
    `Map.union` (Map.fromList [(globalsName,phantomType) | not $ Set.null resVars])

-- | Transform a list of expressions, collecting sets of in-flowing and out-flowing 
-- resource variables.
transformExps :: Int -> [ResType] -> [Placed Exp]
              -> Compiler ([Placed Exp],Int,Set ResType, Set ResType)
transformExps tmp _ [] = return ([],tmp,Set.empty,Set.empty)
transformExps tmp resources (exp:exps) = do
    (exp,tmp',inRes',outRes') <- placedApply (transformExp tmp resources AnyType) exp
    (exps,tmp'',inRes'',outRes'') <- transformExps tmp' resources exps
    return (exp:exps, tmp'',
            inRes' `Set.union` inRes'',outRes' `Set.union` outRes'')

-- | Transform a given expressions, collecting sets of in-flowing and out-flowing 
-- resource variables.
transformExp :: Int -> [ResType] -> TypeSpec -> Exp -> OptPos 
             -> Compiler (Placed Exp, Int, Set ResType, Set ResType)
transformExp tmp res _ (Typed exp ty cast) pos = do
    (pexp', tmp', inRes, outRes) <- transformExp tmp res ty exp pos
    return (maybePlace (Typed (content pexp') ty cast) pos, tmp', inRes, outRes)
transformExp tmp res _ (AnonProc mods@ProcModifiers{modifierResourceful=Resourceful} 
                            params body) pos = do
    (body',tmp') <- transformBody tmp res body
    return (maybePlace (AnonProc mods{modifierResourceful=Resourceless}
                               (params ++ [globalsParam]) body') pos, 
            tmp', Set.empty, Set.empty)
transformExp tmp _ _ (AnonProc mods params body) pos = do
    (body', tmp') <- transformBody tmp [] body
    return (maybePlace (AnonProc mods params body') pos, 
            tmp', Set.empty, Set.empty)
transformExp tmp res ty exp@(Var name flow _) pos = do
    resNames <- mapM (resourceVar . fst) res
    let resMap = Map.fromList $ zip resNames (fst <$> res)
    case Map.lookup name resMap of
        Just spec -> 
            let inRes = Set.fromList [(spec, ty) | flowsIn flow]
                outRes = Set.fromList [(spec, ty) | flowsOut flow]
            in return (maybePlace (setExpFlowType exp (Resource spec)) pos, 
                       tmp, inRes, outRes)
        Nothing -> return (maybePlace exp pos, tmp, Set.empty, Set.empty)
transformExp tmp _ _ exp pos = return (maybePlace exp pos, tmp, Set.empty, Set.empty)


transformCases :: Int -> [(ResourceSpec,TypeSpec)] -> [(Placed Exp,[Placed Stmt])]
              -> Compiler ([(Placed Exp, [Placed Stmt])], Int)
transformCases tmp res [] = return ([], tmp)
transformCases tmp res ((guard,body):rest) = do
    (body1,tmp1) <- transformBody tmp res body
    (rest1,tmp2) <- transformCases tmp1 res rest
    return $ ((guard,body1):rest1, tmp2)


makeSingleStmt :: [Placed Stmt] -> Placed Stmt
makeSingleStmt []       = succeedTest
makeSingleStmt [single] = single
makeSingleStmt stmts    = Unplaced $ And stmts

-- |Returns the list of args corresponding to the specified resource
-- flow spec.  This produces up to two arguments for each simple
-- resource, multiplied by all the simple resources a single resource
-- flow spec might refer to.
resourceArgs ::  OptPos -> ResourceFlowSpec -> Compiler [Placed Exp]
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
                       Compiler [(ResourceFlowSpec,TypeSpec)]
simpleResourceFlows pos (ResourceFlowSpec spec flow) = do
    resDef <- lookupResource spec
    case resDef of
        Nothing -> do
            errmsg pos $ "Unknown resource " ++ show spec
                         ++ " in called proc"
            return []
        Just def ->
            return [(ResourceFlowSpec spec flow,resourceType impln)
                    | (spec,impln) <- Map.toList def]

-- | The local variable name to use for a resource.  This assumes the resource
-- spec has already been canonicalised (fully module qualified).
resourceVar :: ResourceSpec -> Compiler Ident
resourceVar (ResourceSpec [] name) = return name
resourceVar (ResourceSpec mod name) = do
    -- Always use resource name as variable name, regardless of module
    -- XXX This could cause collisions!
    return name


-- |Log a message, if we are logging resource transformation activity.
logResources :: String -> Compiler ()
logResources s = logMsg Resources s
