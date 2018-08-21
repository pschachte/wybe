--  File     : Resources.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Resource checker for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

module Resources (resourceCheckMod, canonicaliseProcResources,
                  resourceCheckProc) where

import AST
import Options (LogSelection(Resources))
import Util
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Monad
import Data.Maybe
import Data.Graph

import Debug.Trace

-- |Check a module's resource declarations.
resourceCheckMod :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
resourceCheckMod modSCC thisMod = do
    logResources $ "**** resource checking module " ++ showModSpec thisMod
    reenterModule thisMod
    resources <- getModuleImplementationField (Map.toAscList . modResources)
    (chg,errs,resources') <-
        fmap unzip3 $ mapM (uncurry checkResourceDef) resources
    updateModImplementation (\imp -> imp { modResources =
                                              Map.fromAscList resources'})
    finishModule
    logResources $ "**** finished resource checking module "
                   ++ showModSpec thisMod
    return (or chg,concat errs)


checkResourceDef :: Ident -> ResourceDef ->
                    Compiler (Bool,[(String,OptPos)],(Ident,ResourceDef))
checkResourceDef name def = do
    (chg,errs,m) <-
        fmap unzip3 $ mapM (uncurry checkOneResource) $ Map.toList $ content def
    return (or chg, concat errs, (name,rePlace (Map.fromList m) def))


checkOneResource :: ResourceSpec -> Maybe ResourceImpln ->
                    Compiler (Bool,[(String,OptPos)],
                              (ResourceSpec,Maybe ResourceImpln))
checkOneResource rspec impln@(Just (SimpleResource ty init pos)) = do
    logResources $ "Check resource " ++ show rspec ++
           " with implementation " ++ show impln
    ty' <- lookupType ty pos
    logResources $ "Actual type is " ++ show ty'
    case ty' of
        -- lookupType reports any undefined types
        Nothing -> return (False,[],(rspec,impln))
        Just ty'' ->
          return (ty'' /= ty,[],(rspec,Just (SimpleResource ty'' init pos)))
checkOneResource rspec Nothing = do
    -- XXX don't currently handle compound resources
    nyi "compound resources"


-- |Make sure all resource for the specified proc are module qualified,
--  making them canonical.
canonicaliseProcResources :: ProcDef -> Compiler ProcDef
canonicaliseProcResources pd = do
    logResources $ "Canonicalising resources used by proc " ++ procName pd
    let proto = procProto pd
    let pos = procPos pd
    let lst = Set.elems $ procProtoResources proto
    resourceFlows <- Set.fromList <$>
                     mapM (canonicaliseResourceFlow pos) lst
    logResources $ "Available resources: " ++ show resourceFlows
    let proto' = proto {procProtoResources = resourceFlows}
    let pd' = pd {procProto = proto'}
    logResources $ "Adding resources results in:" ++ showProcDef 4 pd'
    return pd'



-- |Check use of resources in a single procedure definition, updating
-- parameters and body to thread extra arguments as needed.
resourceCheckProc :: ProcDef -> Compiler ProcDef
resourceCheckProc pd = do
    logResources $ "--------------------------------------\n"
    logResources $ "Adding resources to:" ++ showProcDef 4 pd
    let proto = procProto pd
    let pos = procPos pd
    let resourceFlows = procProtoResources proto
    let params = procProtoParams proto
    let (ProcDefSrc body) = procImpln pd
    resFlows <- fmap concat $ mapM (simpleResourceFlows pos)
                            $ Set.elems resourceFlows
    body' <- transformBody resourceFlows body
    -- let params' = List.filter (not . resourceParam)
    --               params
    resParams <- fmap concat $ mapM (resourceParams pos) resFlows
    let proto' = proto { procProtoParams = params ++ resParams}
    let pd' = pd { procProto = proto', procImpln = ProcDefSrc body' }
    logResources $ "Adding resources results in:" ++ showProcDef 4 pd'
    return pd'



canonicaliseResourceFlow :: OptPos -> ResourceFlowSpec
                         -> Compiler ResourceFlowSpec
canonicaliseResourceFlow pos spec = do
    let res = resourceFlowRes spec
    logResources $ "canonicalising resource " ++ show res
    mbRes <- (fst <$>) <$> lookupResource res pos
    let res' = fromMaybe res mbRes
    logResources $ "    to --> " ++ show mbRes
    return $ spec { resourceFlowRes = res'}


-- |Get a list of all the SimpleResources, and their types, referred 
-- to by a ResourceFlowSpec.  This is necessary because a resource spec
-- may refer to a compound resource.
simpleResourceFlows :: OptPos -> ResourceFlowSpec ->
                       Compiler [(ResourceFlowSpec,TypeSpec)]
simpleResourceFlows pos (ResourceFlowSpec spec flow) = do
    maybeIFace <- lookupResource spec pos
    case maybeIFace of
        Nothing -> return []
        Just (_,iface) ->
            return $
            [(ResourceFlowSpec sp flow,ty) |
             (sp,ty) <- Map.toList iface]


resourceParams :: OptPos -> (ResourceFlowSpec,TypeSpec) -> Compiler [Param]
resourceParams pos (ResourceFlowSpec res flow, typ) = do
    varName <- resourceVar res
    inParam <- do
        if flowsIn flow
        then return [Param varName typ ParamIn (Resource res)]
        else return []
    outParam <- do
        if flowsOut flow
        then return [Param varName typ ParamOut (Resource res)]
        else return []
    return $ inParam ++ outParam


resourceVar :: ResourceSpec -> Compiler String
resourceVar (ResourceSpec [] name) = return name
resourceVar (ResourceSpec mod name) = do
    currMod <- getModuleSpec
    if currMod == mod
    then return name -- ensure we can use local resources in code
    else return $ intercalate "." mod ++ "$" ++ name


transformBody :: Set.Set ResourceFlowSpec -> [Placed Stmt]
              -> Compiler [Placed Stmt]
transformBody resources body =
    mapM (placedApply (transformStmt resources)) body



transformStmt :: Set.Set ResourceFlowSpec -> Stmt -> OptPos
              -> Compiler (Placed Stmt)
transformStmt resources (ProcCall m n id detism args) pos = do
    let procID = trustFromJust "transformStmt" id
    callResources <-
        procProtoResources . procProto <$> getProcDef (ProcSpec m n procID)
    logResources $ "Checking call to " ++ n ++ " using " ++ show callResources
    logResources $ "    with available resources " ++ show resources
    unless (callResources `isSubsetOf` resources)
      $ message Error
        ("Proc " ++ n ++ " uses unavailable resources "
         ++ List.intercalate ", "
         (List.map show $ Set.elems $ Set.difference callResources resources))
        pos
    resArgs <- concat <$> mapM (resourceArgs pos) (Set.elems callResources)
    return $ maybePlace (ProcCall m n (Just procID) detism (args++resArgs)) pos
transformStmt resources (ForeignCall lang name flags args) pos = do
    return $ maybePlace (ForeignCall lang name flags args) pos
-- transformStmt resources (Test stmts) pos = do
--     stmts' <- transformBody resources stmts
--     return $ maybePlace (Test stmts') pos
transformStmt resources stmt@(TestBool var) pos = do
    return $ maybePlace stmt pos
transformStmt resources (And stmts) pos = do
    stmts' <- transformBody resources stmts
    return $ maybePlace (And stmts') pos
transformStmt resources (Or stmts) pos = do
    stmts' <- transformBody resources stmts
    return $ maybePlace (Or stmts') pos
transformStmt resources (Not stmt) pos = do
    stmt' <- placedApplyM (transformStmt resources) stmt
    return $ maybePlace (Not stmt') pos
transformStmt _ Nop pos =
    return $ maybePlace Nop pos
transformStmt resources (Cond test thn els) pos = do
    test' <- placedApplyM (transformStmt resources) test
    thn' <- transformBody resources thn
    els' <- transformBody resources els
    return $ maybePlace (Cond test' thn' els') pos
transformStmt resources (Loop body) pos = do
    body' <- transformBody resources body
    return $ maybePlace (Loop body') pos
transformStmt _ (For itr gen) pos = return $ maybePlace (For itr gen) pos
transformStmt _ Break pos = return $ maybePlace Break pos
transformStmt _ Next pos = return $ maybePlace Next pos


-- |Returns the list of args corresponding to the specified resource
-- flow spec.  This produces up to two arguments for each simple
-- resource, multiplied by all the simple resources a single resource
-- flow spec might refer to.
resourceArgs ::  OptPos -> ResourceFlowSpec -> Compiler [Placed Exp]
resourceArgs pos rflow = do
    simpleSpecs <- simpleResourceFlows pos rflow
    -- XXX make separate exps for each direction
    fmap concat $
         mapM (\((ResourceFlowSpec res flow),ty) -> do
                   var <- resourceVar res
                   let ftype = Resource res
                   let inExp = if flowsIn flow
                            then [Unplaced $ 
                                  Typed (Var var ParamIn ftype) ty False]
                            else []
                   let outExp = if flowsOut flow
                                then [Unplaced $ 
                                      Typed (Var var ParamOut ftype) ty False]
                                else []
                   return $ inExp ++ outExp)
         simpleSpecs


-- |Log a message, if we are logging resource transformation activity.
logResources :: String -> Compiler ()
logResources s = logMsg Resources s
