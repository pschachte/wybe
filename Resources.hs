--  File     : Resources.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Resource checker for Wybe
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

module Resources (resourceCheckMod, resourceCheckProc, resourceVar,
                  resourceArg, resourceParam) where

import AST
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
    -- XXX Must check validity of declared types and initial values
    -- for resources, and declared resources for procs.
    return (False,[])



-- |Check use of resources in a single procedure definition, updating
-- parameters and body to thread extra arguments as needed.
resourceCheckProc :: ProcDef -> Compiler ProcDef
resourceCheckProc pd =
    evalStateT 
    (do
       let resources = procResources pd
       let proto = procProto pd
       let params = primProtoParams proto
       let body = procBody pd
       let pos = procPos pd
       resFlows <- fmap concat $ lift $ mapM (simpleResourceFlows pos) resources
       mapM_ initResource resFlows
       body' <- transformBody body
       let params' = List.filter (not . resourceParam)
                     params
       resParams <- fmap concat $ mapM (resourceParams pos) resFlows
       let proto' = proto { primProtoParams = params' ++ resParams }
       let pd' = pd { procProto = proto', procBody = body' }
       -- liftIO $ putStrLn $ "--------------------------------------\n"
       -- liftIO $ putStrLn $ "Adding resources to:" ++ showProcDef 4 pd
       -- liftIO $ putStrLn $ "Adding resources results in:" ++ showProcDef 4 pd'
       return pd')
    Map.empty


resourceFlowType :: ArgFlowType -> Bool
resourceFlowType (Resource _) = True
resourceFlowType _ = False


resourceArg :: PrimArg -> Bool
resourceArg (ArgVar _ _ _ flowtype _) = resourceFlowType flowtype
resourceArg _ = False


resourceParam :: PrimParam -> Bool
resourceParam = resourceFlowType . primParamFlowType



type ResourceDict = Map ResourceSpec (Int,TypeSpec)

type Resourcer = StateT ResourceDict Compiler


-- |Get a list of all the SimpleResources, and their types, referred 
-- to by a ResourceFlowSpec.  This is necessary because a resource spec
-- may refer to a compound resource.
simpleResourceFlows :: OptPos -> ResourceFlowSpec ->
                       Compiler [(ResourceFlowSpec,TypeSpec)]
simpleResourceFlows pos (ResourceFlowSpec spec flow) = do
    maybeIFace <- lookupResource spec pos
    case maybeIFace of
        Nothing -> return []
        Just iface ->
            return $
            [(ResourceFlowSpec sp flow,ty) |
             (sp,ty) <- Map.toList iface]

            


initResource :: (ResourceFlowSpec,TypeSpec) -> Resourcer ()
initResource (res,ty) = do
    when (flowsIn $ resourceFlowFlow res) $
      modify (Map.insert (resourceFlowRes res) (1,ty))


resourceParams :: OptPos -> (ResourceFlowSpec,TypeSpec) -> Resourcer [PrimParam]
resourceParams pos (ResourceFlowSpec res flow, typ) = do
    let varName = resourceVar res
    inParam <- if flowsIn flow
               then return [PrimParam (PrimVarName varName 1) typ FlowIn 
                            (Resource res) True]
               else return []
    outParam <- if flowsOut flow
                then do
                    maybeNum <- gets $ Map.lookup res
                    case maybeNum of
                        Nothing -> do
                            lift $ message Error
                              ("Resource " ++ show res ++
                               " might not be assigned") pos
                            return []
                        Just (n,_) -> 
                            return [PrimParam (PrimVarName varName n) typ 
                                    FlowOut (Resource res) True]
                else return []
    return $ inParam ++ outParam


resourceVar :: ResourceSpec -> String
resourceVar (ResourceSpec mod name) = intercalate "." mod ++ "$" ++ name


transformBody :: ProcBody -> Resourcer ProcBody
transformBody body = do
    prims <- mapM (placedApply transformPrim) $ bodyPrims body
    fork <- transformFork $ bodyFork body
    return $ body { bodyPrims = prims, bodyFork = fork }
    

transformFork :: PrimFork -> Resourcer PrimFork
transformFork NoFork = return NoFork
transformFork fork = do
    dict <- get
    pairs <- mapM (\b -> lift $ runStateT (transformBody b) dict) $ 
             forkBodies fork
    put $ foldr1 (Map.intersectionWith max) $ List.map snd pairs
    bodies' <- mapM (uncurry addReconciliation) pairs
    return $ fork { forkBodies = bodies' }


transformPrim :: Prim -> OptPos -> Resourcer (Placed Prim)
transformPrim (PrimCall m n (Just pspec) args) pos = do
    resources <- fmap procResources $ lift $ getProcDef pspec
    let args' = List.filter (not . resourceArg) args
    args'' <- fmap concat $ mapM (resourceArgs pos) resources
    return $ maybePlace (PrimCall m n (Just pspec) (args'++args'')) pos
transformPrim prim pos = return $ maybePlace prim pos


resourceArgs ::  OptPos -> ResourceFlowSpec -> Resourcer [PrimArg]
resourceArgs pos rflow = do
    simpleSpecs <- lift $ simpleResourceFlows pos rflow
    fmap concat $ mapM (simpleResourceArgs pos) simpleSpecs


simpleResourceArgs :: OptPos -> (ResourceFlowSpec,TypeSpec) -> Resourcer [PrimArg]
simpleResourceArgs pos ((ResourceFlowSpec res flow),typ) = do
    maybePair <- gets (Map.lookup res)
    let varName = resourceVar res
    case maybePair of
        Nothing -> do
                   lift $ message Error
                     ("Proc needs unavailable resource " ++ show res) pos
                   return []
        Just (num,typ) -> do
            inArg <- if flowsIn flow
                     then return [ArgVar (PrimVarName varName num) typ FlowIn 
                                  (Resource res) False]
                     else return []
            outArg <- if flowsOut flow
                      then do
                          let newNum = num+1
                          modify $ Map.insert res (newNum,typ)
                          return [ArgVar (PrimVarName varName (num+1)) typ 
                                  FlowOut (Resource res) False]
                      else return []
            return $ inArg ++ outArg


addReconciliation :: ProcBody -> ResourceDict -> Resourcer ProcBody
addReconciliation body dict = do
    return body
