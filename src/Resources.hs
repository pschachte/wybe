--  File     : Resources.hs
--  Author   : Peter Schachte
--  Purpose  : Resource checker for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Resources (resourceCheckMod, canonicaliseProcResources, canonicaliseResourceSpec,
                  transformProcResources, specialResourcesSet) where

import           AST
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.Graph
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Maybe
import           Data.Set                  as Set
import           Data.Tuple.HT             (mapFst)
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
        fmap unzip3 $ mapM (uncurry checkResourceDef) resources
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
    logResources $ "Declared resources: " ++ show resFlows
    (body',tmp') <- transformBody tmp resFlows body
    resParams <- concat <$> mapM (resourceParams pos) resFlows
    let proto' = proto { procProtoParams = params ++ resParams}
    let pd' = pd { procProto = proto', procTmpCount = tmp',
                   procImpln = ProcDefSrc body' }
    logResources $ "Adding resources results in:" ++ showProcDef 4 pd'
    return pd'


resourceParams :: OptPos -> (ResourceFlowSpec,TypeSpec) -> Compiler [Param]
resourceParams pos (ResourceFlowSpec res flow, typ) = do
    varName <- resourceVar res
    let inParam  = [Param varName typ ParamIn (Resource res) | flowsIn flow]
    let outParam = [Param varName typ ParamOut (Resource res) | flowsOut flow]
    return $ inParam ++ outParam

-- | Transform a statement sequence, turning resources into arguments.
transformBody :: Int -> [(ResourceFlowSpec, TypeSpec)] -> [Placed Stmt]
              -> Compiler ([Placed Stmt],Int)
transformBody tmp _ [] = return ([],tmp)
transformBody tmp resources (stmt:stmts) = do
    (stmts1,tmp') <- placedApply (transformStmt tmp resources) stmt
    (stmts2,tmp'') <- transformBody tmp' resources stmts
    return (stmts1 ++ stmts2, tmp'')


-- | Transform a single statement, turning resources into arguments.
transformStmt :: Int -> [(ResourceFlowSpec, TypeSpec)] -> Stmt -> OptPos
              -> Compiler ([Placed Stmt], Int)
transformStmt tmp res stmt@(ProcCall func@(First m n id) detism resourceful args) pos = do
    let procID = trustFromJust "transformStmt" id
    callResources <-
        procProtoResources . procProto <$> getProcDef
                (ProcSpec m n procID generalVersion)
    let argTys = fromMaybe AnyType . maybeExpType . content <$> args
    unless (resourceful || (Set.null callResources 
                            && not (any isResourcefulHigherOrder argTys) ))
      $ message Error
        ("Call to resourceful proc without ! resource marker: "
         ++ showStmt 4 stmt)
        pos
    logResources $ "Checking call to " ++ n ++ " using " ++ show callResources
    resArgs <- concat <$> mapM (resourceArgs pos) (Set.elems callResources)
    (args', tmp') <- transformExps tmp res args 
    return ([maybePlace
            (ProcCall func detism False (args'++resArgs)) pos], tmp')
transformStmt tmp res stmt@(ProcCall (Higher func) detism resourceful args) pos = 
    case content func of
        Typed _ (HigherOrderType ProcModifiers{modifierResourceful=resfulMod} _) _ -> do
            unless (resourceful || resfulMod == Resourceless)
                $ message Error
                    ("Resourceful higher order call without ! resource marker: "
                    ++ showStmt 4 stmt)
                    pos
                    
            (args', tmp') <- transformExps tmp res args 
            return ([maybePlace (ProcCall (Higher func) detism False args') pos], tmp')
        _ -> shouldnt $ "bad resoruce higher call type" ++ show stmt 
transformStmt tmp res (ForeignCall lang name flags args) pos = do
    (args', tmp') <- transformExps tmp res args
    return ([maybePlace (ForeignCall lang name flags args') pos], tmp')
transformStmt tmp res (TestBool var) pos = do
    (var', tmp') <- transformExp tmp res var Nothing
    return ([maybePlace (TestBool $ content var') pos], tmp)
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
    return ([maybePlace (Or [makeSingleStmt stmt',makeSingleStmt stmt''] vars)
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
    return ([maybePlace
             (Cond (Unplaced $ And test') thn' els' condVars defVars) pos],
            tmp3)
transformStmt tmp res (Loop body defVars) pos = do
    (body',tmp') <- transformBody tmp res body
    return ([maybePlace (Loop body' defVars) pos], tmp')
transformStmt tmp res (For generators body) pos = do
    (body', tmp') <- transformBody tmp res body
    return ([maybePlace (For generators body') pos], tmp')
transformStmt tmp res (UseResources allRes oldRes body) pos = do
    let resVars = trustFromJust "use stmt without var list after type check"
                  oldRes
    canonAllRes <- mapM (canonicaliseResourceSpec pos "use statement") allRes
    let resTypes = List.filter ((`elem` resVars) . resourceName . fst) canonAllRes
    toSave <- mapM (resourceVar . fst) resTypes
    let types = fromJust . snd <$> resTypes
    let resCount = length toSave
    let tmp' = tmp + resCount
    let ress = zip4 toSave (mkTempName <$> [tmp..]) types (fst <$> resTypes)
    let get v ty rs = varGet v `withType` ty
    let set v ty rs = varSet v `withType` ty
    let saves = (\(r,t,ty,rs) -> move (get r ty rs `setExpFlowType` Resource rs ) (set t ty rs `setExpFlowType` Ordinary )) <$> ress
    let restores = (\(r,t,ty,rs) -> move (get t ty rs `setExpFlowType` Ordinary ) (set r ty rs `setExpFlowType` Resource rs )) <$> ress
    resFlows <- concat <$> mapM (simpleResourceFlows pos) 
                                ((`ResourceFlowSpec` ParamInOut). fst <$> canonAllRes)
    (body',tmp'') <- transformBody tmp' (List.nub $ res ++ resFlows) body
    return (saves ++ body' ++ restores, tmp'')
-- transformStmt tmp res (For itr gen) pos =
--     return ([maybePlace (For itr gen) pos], tmp)
transformStmt tmp res Break pos =
    return ([maybePlace Break pos], tmp)
transformStmt tmp res Next pos =
    return ([maybePlace Next pos], tmp)

transformExps :: Int -> [(ResourceFlowSpec, TypeSpec)] -> [Placed Exp]
              -> Compiler ([Placed Exp],Int)
transformExps tmp _ [] = return ([],tmp)
transformExps tmp resources (exp:exps) = do
    (exp,tmp') <- placedApply (transformExp tmp resources) exp
    (exps,tmp'') <- transformExps tmp' resources exps
    return (exp:exps, tmp'')

transformExp :: Int -> [(ResourceFlowSpec, TypeSpec)] -> Exp -> OptPos 
             -> Compiler (Placed Exp, Int)
transformExp tmp res (Typed exp ty cast) pos = do
    (pexp', tmp') <- transformExp tmp res exp Nothing
    return (maybePlace (Typed (content pexp') ty cast) pos, tmp')
transformExp tmp res (Lambda mods@ProcModifiers{modifierResourceful=Resourceful} params body) pos = do
    (body',tmp') <- transformBody tmp res body
    resParams <- concat <$> mapM (resourceParams pos) 
                                 (mapFst (\r -> r{resourceFlowFlow=ParamInOut}) <$> res)
    return (maybePlace (Lambda mods{modifierResourceful=Resourceless}
                               (params ++ resParams) body') pos, tmp')
transformExp tmp _ (Lambda mods params body) pos = do
    (body', tmp') <- transformBody tmp [] body
    return (maybePlace (Lambda mods params body') pos, tmp')
transformExp tmp res exp@(Var name _ _) pos = do
    resNames <- mapM (resourceVar . resourceFlowRes . fst) res
    let resMap = Map.fromList $ zip resNames (resourceFlowRes . fst <$> res)
    case Map.lookup name resMap of
        Just spec -> return (maybePlace (setExpFlowType exp (Resource spec)) pos, tmp)
        Nothing -> return (maybePlace exp pos, tmp)
transformExp tmp _ exp pos = return (maybePlace exp pos, tmp)


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
