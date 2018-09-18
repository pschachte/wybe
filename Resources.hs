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
import Snippets
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
    let tmp = procTmpCount pd
    let resourceFlows = procProtoResources proto
    let params = procProtoParams proto
    let (ProcDefSrc body) = procImpln pd
    resFlows <- fmap concat $ mapM (simpleResourceFlows pos)
                            $ Set.elems resourceFlows
    (body',tmp') <- transformBody resourceFlows tmp body
    resParams <- fmap concat $ mapM (resourceParams pos) resFlows
    let proto' = proto { procProtoParams = params ++ resParams}
    let pd' = pd { procProto = proto', procTmpCount = tmp',
                   procImpln = ProcDefSrc body' }
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


transformBody :: Set.Set ResourceFlowSpec -> Int -> [Placed Stmt]
              -> Compiler ([Placed Stmt],Int)
transformBody resources tmp [] = return ([],tmp)
transformBody resources tmp (stmt:stmts) = do
    (stmts1,tmp') <- placedApply (transformStmt resources tmp) stmt
    (stmts2,tmp'') <- transformBody resources tmp' stmts
    return (stmts1 ++ stmts2, tmp'')



transformStmt :: Set.Set ResourceFlowSpec -> Int
              -> Stmt -> OptPos -> Compiler ([Placed Stmt], Int)
transformStmt resources tmp
              stmt@(ProcCall m n id detism resourceful args) pos = do
    let procID = trustFromJust "transformStmt" id
    callResources <-
        procProtoResources . procProto <$> getProcDef (ProcSpec m n procID)
    unless (resourceful || Set.null callResources)
      $ message Error
        ("Call to resourceful proc without ! resource marker: "
         ++ showStmt 4 stmt)
        pos
    logResources $ "Checking call to " ++ n ++ " using " ++ show callResources
    logResources $ "    with available resources " ++ show resources
    unless (callResources `isSubsetOf` resources)
      $ message Error
        ("Call to " ++ n ++ " needs unavailable resource(s) "
         ++ List.intercalate ", "
         (List.map show $ Set.elems $ Set.difference callResources resources))
        pos
    resArgs <- concat <$> mapM (resourceArgs pos) (Set.elems callResources)
    return ([maybePlace
            (ProcCall m n (Just procID) detism False (args++resArgs)) pos],
            tmp)
transformStmt resources tmp (ForeignCall lang name flags args) pos = do
    return ([maybePlace (ForeignCall lang name flags args) pos], tmp)
transformStmt resources tmp stmt@(TestBool var) pos = do
    return ([maybePlace stmt pos], tmp)
transformStmt resources tmp (And stmts) pos = do
    (stmts',tmp') <- transformBody resources tmp stmts
    return ([maybePlace (And stmts') pos], tmp')
transformStmt resources tmp (Or stmts) pos = do
    (stmts',tmp') <- transformBody resources tmp stmts
    return ([maybePlace (Or stmts') pos], tmp')
transformStmt resources tmp (Not stmt) pos = do
    (stmt',tmp') <- placedApplyM (transformStmt resources tmp) stmt
    case stmt' of
      []       -> return ([failTest], tmp') -- shouldn't happen
      [single] -> return ([maybePlace (Not single) pos], tmp')
      stmts    -> return ([maybePlace (Not (Unplaced $ And stmts)) pos], tmp')
transformStmt _ tmp Nop pos =
    return ([], tmp)
transformStmt resources tmp (Cond test thn els) pos = do
    (test',tmp1) <- placedApplyM (transformStmt resources tmp) test
    (thn',tmp2) <- transformBody resources tmp1 thn
    (els',tmp3) <- transformBody resources tmp2 els
    return ([maybePlace (Cond (Unplaced $ And test') thn' els') pos], tmp3)
transformStmt resources tmp (Loop body) pos = do
    (body',tmp') <- transformBody resources tmp body
    return ([maybePlace (Loop body') pos], tmp')
transformStmt resources tmp (UseResources res body) pos = do
    let resFlows = flip ResourceFlowSpec ParamInOut <$> res
    scoped <- Set.fromList <$> mapM (canonicaliseResourceFlow pos) resFlows
    let resources' = Set.union resources scoped
    -- XXX what about resources with same name and different modules?
    let toSave = resourceName . resourceFlowRes
                 <$> Set.elems (Set.intersection resources scoped)
    let resCount = length toSave
    let var n f = Unplaced $ Var n f Ordinary
    let tmp' = tmp + resCount
    let pairs = zip toSave (mkTempName <$> [tmp..])
    let saves = (\(r,t) -> Unplaced $ ForeignCall "llvm" "move" []
                  [var r ParamIn,var t ParamOut]) <$> pairs
    let restores = (\(r,t) -> Unplaced $ ForeignCall "llvm" "move" []
                     [var t ParamIn,var r ParamOut]) <$> pairs
    (body',tmp'') <- transformBody resources' tmp' body
    return (saves ++ body' ++ restores, tmp'')
transformStmt _ tmp (For itr gen) pos =
    return ([maybePlace (For itr gen) pos], tmp)
transformStmt _ tmp Break pos =
    return ([maybePlace Break pos], tmp)
transformStmt _ tmp Next pos =
    return ([maybePlace Next pos], tmp)


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
