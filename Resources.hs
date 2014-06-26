--  File     : Resources.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Resource checker for Wybe
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

module Resources (resourceCheckMod, resourceCheckProc, resourceVar) where

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
    reenterModule thisMod
    resources <- getModuleImplementationField (Map.toAscList . modResources)
    (chg,errs,resources') <-
        fmap unzip3 $ mapM (uncurry checkResourceDef) resources
    updateModImplementation (\imp -> imp { modResources = 
                                              Map.fromAscList resources'})
    finishModule
    -- liftIO $ putStrLn $ "**** Exiting module " ++ showModSpec thisMod
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
    ty' <- lookupType ty pos
    case ty' of
        -- lookupType reports any undefined types
        Nothing -> return (False,[],(rspec,impln))
        Just ty'' ->
          return (ty'' /= ty,[],(rspec,Just (SimpleResource ty'' init pos)))
checkOneResource rspec Nothing = do
    -- XXX don't currently handle compound resources
    nyi "compound resources"


-- |Check use of resources in a single procedure definition, updating
-- parameters and body to thread extra arguments as needed.
resourceCheckProc :: ProcDef -> Compiler ProcDef
resourceCheckProc pd =
    return pd
--     evalStateT 
--     (do
--        -- liftIO $ putStrLn $ "--------------------------------------\n"
--        -- liftIO $ putStrLn $ "Adding resources to:" ++ showProcDef 4 pd
--        let resources = procProtoResources $ procProto pd
--        let proto = procProto pd
--        let params = procProtoParams proto
--        let (ProcDefSrc body) = procImpln pd
--        let pos = procPos pd
--        resFlows <- fmap concat $ lift $ mapM (simpleResourceFlows pos) resources
--        mapM_ initResource resFlows
--        body' <- transformBody body
--        -- let params' = List.filter (not . resourceParam)
--        --               params
--        -- resParams <- fmap concat $ mapM (resourceParams pos) resFlows
--        -- let proto' = proto { primProtoParams = params' ++ resParams }
--        let pd' = pd { procImpln = ProcDefSrc body' }
--        -- liftIO $ putStrLn $ "Adding resources results in:" ++ showProcDef 4 pd'
--        return pd')
--     Map.empty


-- resourceFlowType :: ArgFlowType -> Bool
-- resourceFlowType (Resource _) = True
-- resourceFlowType _ = False


-- resourceArg :: PrimArg -> Bool
-- resourceArg (ArgVar _ _ _ flowtype _) = resourceFlowType flowtype
-- resourceArg _ = False


-- resourceParam :: PrimParam -> Bool
-- resourceParam = resourceFlowType . primParamFlowType



-- ----------------------------------------------------------------
-- --                         The Resourcer monad
-- ----------------------------------------------------------------

-- -- |For each resource, we remember the current variable number, the
-- -- offset to add to the variable number of any explicit references,
-- -- and its type.  Existing explicit references are treated as ordinary
-- -- variables before we know which procs we call use which resources,
-- -- so they need to be renumbered.
-- data ResourceInfo 
--      = ResourceInfo {
--          resourceInfoNumber :: Int,
--          resourceInfoOffset :: Int,
--          resourceInfoResource :: ResourceSpec,
--          resourceInfoType :: TypeSpec }
--      | ResourceRef VarName
--      deriving Show

-- -- |Maps variable names to resource info.  Invariant: if there is a 
-- -- ResourceRef mapping that specifies a variable, the mapping for 
-- -- that variable will be a ResourceInfo.
-- type ResourceDict = Map VarName ResourceInfo

-- type Resourcer = StateT ResourceDict Compiler


-- resourceInfo :: VarName -> 
--                 Resourcer (Maybe (VarName,Int,Int,ResourceSpec,TypeSpec))
-- resourceInfo var = do
--     maybeInfo <- gets (Map.lookup var)
--     case maybeInfo of
--         Nothing -> return Nothing
--         Just (ResourceRef var') -> resourceInfo var'
--         Just (ResourceInfo num offset resource typ) ->
--             return $ Just (var, num, offset, resource, typ)


-- -- |Get a list of all the SimpleResources, and their types, referred 
-- -- to by a ResourceFlowSpec.  This is necessary because a resource spec
-- -- may refer to a compound resource.
-- simpleResourceFlows :: OptPos -> ResourceFlowSpec ->
--                        Compiler [(ResourceFlowSpec,TypeSpec)]
-- simpleResourceFlows pos (ResourceFlowSpec spec flow) = do
--     maybeIFace <- lookupResource spec pos
--     case maybeIFace of
--         Nothing -> return []
--         Just iface ->
--             return $
--             [(ResourceFlowSpec sp flow,ty) |
--              (sp,ty) <- Map.toList iface]


-- -- |Update the Resourcer state to reflect the fact that the resource 
-- --  with the specified flow spec and type is available.  To allow the 
-- --  resource to be specified by any tail of the module hierarchy down 
-- --  to the resource name alone, we add indirection records for them.
-- initResource :: (ResourceFlowSpec,TypeSpec) -> Resourcer ()
-- initResource (resFlow,ty) = do
--     when (flowsIn $ resourceFlowFlow resFlow) $ do
--         let res@(ResourceSpec mod name) = resourceFlowRes resFlow
--         let (var:aliases) = [resourceVar (ResourceSpec m name) 
--                             | m <- List.tails mod]
--         modify (Map.insert var (ResourceInfo 0 0 res ty))
--         mapM_ (\nm -> modify (\s -> Map.insert nm (ResourceRef var) s)) aliases


-- resourceParams :: OptPos -> (ResourceFlowSpec,TypeSpec) -> Resourcer [PrimParam]
-- resourceParams pos (ResourceFlowSpec res flow, _) = do
--     maybeInfo <- resourceInfo $ resourceVar res
--     case maybeInfo of
--         Nothing -> do
--             lift $ message Error
--               ("Resource " ++ show res ++ " might not be assigned") pos
--             return []
--         Just (varName, num, _, res, typ) -> do
--             inParam <- do
--                 if flowsIn flow
--                   then return [PrimParam (PrimVarName varName 0) typ FlowIn 
--                                (Resource res) True]
--                   else return []
--             outParam <- do
--                 if flowsOut flow
--                   then return [PrimParam (PrimVarName varName num) typ 
--                                FlowOut (Resource res) True]
--                   else return []
--             return $ inParam ++ outParam


resourceVar :: ResourceSpec -> String
resourceVar (ResourceSpec [] name) = name
resourceVar (ResourceSpec mod name) = intercalate "." mod ++ "$" ++ name


-- transformBody :: [Placed Stmt] -> Resourcer [Placed Stmt]
-- transformBody body = mapM (placedApply transformStmt) body
    

-- -- |Combine the ResourceInfos from two arms of a fork into one for 
-- --  the fork as a whole.
-- joinInfo (ResourceRef name1) (ResourceRef name2)
--   | name1 == name2  = ResourceRef name2
-- joinInfo (ResourceInfo num1 off1 res1 ty1) (ResourceInfo num2 off2 res2 ty2)
--   | res1 == res2 && ty1 == ty2 =
--       ResourceInfo (max num1 num2) (max off1 off2) res2 ty2
-- joinInfo inf1 inf2 =
--     shouldnt $ "inconsistent resource info in condition arms: " ++ 
--     show inf1 ++ " vs. " ++ show inf2
    

-- transformStmt :: Stmt -> OptPos -> Resourcer (Placed Stmt)
-- transformStmt (ProcCall m n (Just procID) args) pos = do
--     resources <- fmap (procProtoResources . procProto) $
--                  lift $ getProcDef (ProcSpec m n procID)
--     args' <- mapM transformArg args
--     resArgs <- fmap concat $ mapM (resourceArgs pos) resources
--     mapM_ (accountResourceArgs resources . content) args'
--     return $ maybePlace (ProcCall m n (Just procID) (args'++resArgs)) pos
-- transformStmt (ForeignCall lang name flags args) pos = do
--     args' <- mapM transformArg args
--     mapM_ (accountResourceArgs [] . content) args
--     return $ maybePlace (ForeignCall lang name flags args') pos
-- transformStmt (Nop) pos = return $ maybePlace Nop pos
-- transformStmt (Cond test exp thn els) pos = do
--     test' <- transformBody test
--     thn' <- transformBody thn
--     els' <- transformBody els
--     return $ maybePlace (Cond test' exp thn' els') pos
-- transformStmt (Loop body) pos = do
--     body' <- transformBody body
--     return $ maybePlace (Loop body') pos
-- transformStmt (For itr gen) pos = return $ maybePlace (For itr gen) pos
-- transformStmt (Break) pos = return $ maybePlace Break pos
-- transformStmt (Next) pos = return $ maybePlace Next pos


-- -- |Transform any explicit arguments that are actually references to 
-- --  resources.  First, we update the variable numbers to account for 
-- --  the implicit resource usage, and second, we update the variable 
-- --  names to reflect the module qualified resource name.  
-- transformArg :: Exp -> Resourcer Exp
-- transformArg arg@(Var name flow ftype final) = do
--     dict <- get
--     -- liftIO $ putStrLn $ "Translating arg:" ++ show arg ++ " with dict " ++ show dict
--     maybeTuple <- resourceInfo name
--     case maybeTuple of
--         Nothing -> do
--             -- liftIO $ putStrLn $ "not a resource"
--             return arg
--         Just (name', currNum, offset, res, typ) -> do
--             let newVarName = PrimVarName name' (num+offset)
--             let arg' = ArgVar newVarName typ flow (Resource res) final
--             -- liftIO $ putStrLn $ "Translated to: " ++ show arg'
--             return arg'
-- transformArg arg = return arg
    

-- -- |Update resource mapping for any out resource args to reflect 
-- -- changed numbering.
-- accountResourceArgs :: [ResourceFlowSpec] -> Exp -> Resourcer ()
-- accountResourceArgs specs 
--   arg@(ArgVar (PrimVarName name _) _ FlowOut _ _) = do
--       maybeInfo <- resourceInfo name
--       case maybeInfo of
--           Nothing -> return ()
--           Just (name',currNum,offset,res,typ) -> do
--               modify $ 
--                 Map.insert name' (ResourceInfo (currNum+1) (offset+1) res typ)
--               return ()
-- -- XXX also need to report error if the resource is on the list 
-- -- of specs with an out or in-out flow, and this flow is out
-- accountResourceArgs _ arg = return ()
    

-- -- |Returns the list of args corresponding to the specified resource
-- -- flow spec.  This produces up to two arguments for each simple
-- -- resource, multiplied by all the simple resources a single resource
-- -- flow spec might refer to.
-- resourceArgs ::  OptPos -> ResourceFlowSpec -> Resourcer [PrimArg]
-- resourceArgs pos rflow = do
--     simpleSpecs <- lift $ simpleResourceFlows pos rflow
--     fmap concat $ 
--       mapM (\((ResourceFlowSpec res flow),_) ->
--              resourceVarArgs pos (resourceVar res) flow)
--       simpleSpecs



-- resourceVarArgs :: OptPos -> VarName -> FlowDirection -> Resourcer [PrimArg]
-- resourceVarArgs pos varName flow = do
--     maybeTuple <- gets (Map.lookup varName)
--     case maybeTuple of
--         Nothing -> do
--                    lift $ message Error
--                      ("Proc needs unavailable resource " ++ varName) pos
--                    return []
--         Just (ResourceInfo num offset res typ) -> do
--             inArg <- if flowsIn flow
--                      then return [ArgVar (PrimVarName varName num) typ FlowIn 
--                                   (Resource res) False]
--                      else return []
--             outArg <- if flowsOut flow
--                       then do
--                           let newNum = num+1
--                           modify $ Map.insert varName 
--                             (ResourceInfo newNum offset res typ)
--                           return [ArgVar (PrimVarName varName (num+1)) typ 
--                                   FlowOut (Resource res) False]
--                       else return []
--             return $ inArg ++ outArg
--         Just (ResourceRef varName') -> do
--             resourceVarArgs pos varName' flow


-- addReconciliation :: ProcBody -> ResourceDict -> Resourcer ProcBody
-- addReconciliation body dict = do
--     -- XXX must implement this!
--     return body
