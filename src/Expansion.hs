--  File     : Expansion.hs
--  Author   : Peter Schachte
--  Purpose  : Replace certain procedure calls with others
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
--  This code is used for inlining procedures and other similar
--  transformations.  As part of this, variables are also renamed.
--  This code operates on LPVM (Prim) form.
--
--  This code is used bottom-up, ie, callees are expanded before
--  their callers, so it does not need to recursively expand calls.

module Expansion (procExpansion) where

import           AST
import           Util
import           BodyBuilder
import           Control.Monad
import           Control.Monad.Extra       (ifM)
import           Control.Monad.Trans       (lift)
import           Control.Monad.Trans.State
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Set                  as Set
import           Data.Maybe                as Maybe
import           Options                   (LogSelection (Expansion))


-- | Expand the supplied ProcDef, inlining as desired.
procExpansion :: ProcSpec -> ProcDef -> Compiler ProcDef
procExpansion pspec def = do
    logMsg Expansion $ replicate 50 '='
    logMsg Expansion $ "*** Try to expand proc " ++ show pspec
    let impln = procImpln def
    let proto = procImplnProto impln
    let body = procImplnBody impln
    logMsg Expansion $ "    initial body: " ++ show (procImpln def)
    let tmp = procTmpCount def
    let (ins,outs) = inputOutputParams proto
    isClosure <- isClosureProc pspec
    let params = primProtoParams proto
    let st = initExpanderState (procCallSiteCount def)
    (st', tmp', used, body') <- buildBody tmp (Map.fromSet id outs)
                                $ execStateT (expandBody body) st
    let params' = markParamNeededness isClosure used ins <$> params
    let proto' = proto {primProtoParams = params'}
    let impln' = impln{ procImplnProto = proto',
                        procImplnBody = body' }
    let def' = def { procImpln = impln',
                     procTmpCount = tmp',
                     procCallSiteCount = nextCallSiteID st' }
    if def /= def'
        then
        logMsg Expansion
        $ "*** Expanded:" ++ showProcDef 4 def
          ++ "\n*** To:" ++ showProcDef 4 def'
          ++ "\nTemp counter = " ++ show (procTmpCount def')
        else
        logMsg Expansion
        $ "*** Expansion did not change proc " ++ show (procName def)
    return def'


-- |Update the param to indicate whether the param is actually needed based
-- on the set of variables used in the prod body and the set of input var
-- names.  We consider outputs to be unneeded if they're identical to inputs.
markParamNeededness :: Bool -> Set PrimVarName -> Set PrimVarName
                    -> PrimParam -> PrimParam
markParamNeededness isClosure used _ param@PrimParam{primParamName=nm,
                                                     primParamFlow=FlowIn,
                                                     primParamFlowType=ft,
                                                     primParamInfo=info} =
    param {primParamInfo=info{paramInfoUnneeded=Set.notMember nm used
                                                && (not isClosure
                                                    || ft /= Ordinary)}}
markParamNeededness isClosure _ ins param@PrimParam{primParamName=nm,
                                                    primParamFlow=FlowOut,
                                                    primParamFlowType=ft,
                                                    primParamInfo=info} =
    param {primParamInfo=info{paramInfoUnneeded=Set.member nm ins
                                                && (not isClosure
                                                    || ft /= Ordinary)}}
markParamNeededness _ _ _ PrimParam{ primParamFlow=FlowOutByReference } =
    shouldnt "unexpected FlowOutByReference at this stage of compilation"
markParamNeededness _ _ _ PrimParam{ primParamFlow=FlowTakeReference } =
    shouldnt "unexpected FlowTakeReference at this stage of compilation"


-- |Type to remember the variable renamings.
type Renaming = Map PrimVarName PrimArg


-- |A Renaming that doesn't substitute anything
identityRenaming :: Renaming
identityRenaming = Map.empty


----------------------------------------------------------------
--                       The Expander Monad
--
-- This monad keeps track of variable renaming needed to keep inlining
-- hygenic.  To do this, we rename all the input parameters of the proc to
-- be inlined, and when expanding the body, we rename any variables when
-- first assigned.  The exception to this is the proc's output parameters.
-- These are kept as a set.  We also maintain a counter for temporary
-- variable names.
----------------------------------------------------------------

data ExpanderState = Expander {
    inlining       :: Bool,      -- ^Whether we are currently inlining (and
                                 --  therefore should not inline calls)
    renaming       :: Renaming,  -- ^The current variable renaming
    writeNaming    :: Renaming,  -- ^Renaming for new assignments
    noFork         :: Bool,      -- ^There's no fork at the end of this body
    nextCallSiteID :: CallSiteID -- ^The next callSiteID to use
    }


type Expander = StateT ExpanderState BodyBuilder

-- |Substitute a fresh temp variable for the specified variable, unless
-- we've already recorded the mapping for that name in writeNaming
freshVar :: PrimVarName -> TypeSpec -> ArgFlowType  -> Expander PrimArg
freshVar oldVar typ ft = do
    logExpansion $ "Making fresh name for variable " ++ show oldVar
    maybeName <- gets (Map.lookup oldVar . writeNaming)
    case maybeName of
        Nothing -> do
            newVar <- lift freshVarName
            logExpansion $ "    Generated fresh name " ++ show newVar
            addRenaming oldVar $ ArgVar newVar typ FlowIn ft False
            return $ ArgVar newVar typ FlowOut ft False
        Just newArg -> do
            logExpansion $ "    Already named it " ++ show newArg
            return newArg


-- |Add a binding for a variable. If that variable is an output for the
-- proc being defined, also add an explicit assignment to that variable.
addRenaming :: PrimVarName -> PrimArg -> Expander ()
addRenaming var val = do
    logExpansion $ "      adding renaming " ++ show var ++ " -> " ++ show val
    modify (\s -> s { renaming = Map.insert var val $ renaming s })
-- Need to add renaming even if it's an identity, because renamings
-- are used to tell which variables shoudn't be renamed.


addInstr :: Prim -> OptPos -> Expander ()
addInstr prim pos = do
    -- reassign "CallSiteID" if the given prim is inlined from other proc
    prim' <- case prim of
        PrimCall _ pspec args gFlows -> do
            inliningNow <- gets inlining
            if inliningNow
            then do
                callSiteID <- gets nextCallSiteID
                modify (\st -> st {nextCallSiteID = callSiteID + 1})
                return $ PrimCall callSiteID pspec args gFlows
            else
                return prim
        _ -> return prim
    lift $ instr prim' pos


-- init a expander state based on the given call site count
initExpanderState :: CallSiteID -> ExpanderState
initExpanderState = Expander False identityRenaming identityRenaming True


----------------------------------------------------------------
--                        Expanding Proc Bodies
----------------------------------------------------------------

expandBody :: ProcBody -> Expander ()
expandBody (ProcBody prims fork) = do
    logExpansion $ "Expanding unforked part of body:" ++ showPlacedPrims 4 prims
    modify (\s -> s { noFork = fork == NoFork })
    mapM_ (placedApply expandPrim) prims
    logExpansion $ "Finished expanding unforked part of body"
    case fork of
      NoFork -> do
        logExpansion "No fork for this body"
        return ()
      PrimFork var ty final bodies -> do
        st <- get
        logExpansion $ "Now expanding fork (" ++
          (if inlining st then "without" else "WITH") ++ " inlining)"
        logExpansion $ "  with renaming = " ++ show (renaming st)
        let var' = case Map.lookup var $ renaming st of
              Nothing -> var
              Just ArgVar{argVarName=v} -> v
              Just _ -> shouldnt "expansion led to non-var conditional"
        logExpansion $ "  fork on " ++ show var' ++ ":" ++ show ty
                       ++ " with " ++ show (length bodies) ++ " branches"
        expandFork var' ty bodies
        logExpansion $ "Finished expanding fork on " ++ show var'


expandFork :: PrimVarName -> TypeSpec -> [ProcBody] -> Expander ()
expandFork var ty bodies = do
    maybeVal <- lift $ definiteVariableValue var
    case maybeVal of
      Just (ArgInt n _) | n < fromIntegral (length bodies) -> do
        logExpansion $ "Value of " ++ show var ++ " known to be " ++ show n
                       ++ ": expanding only that branch"
        expandBody $ bodies !! fromIntegral n
      _ -> do
        lift $ buildFork var ty
        zipWithM_ (\b n -> do
                  logExpansion $ "Beginning expansion of branch " ++ show n
                                 ++ " on " ++ show var
                  lift beginBranch
                  expandBody b
                  lift endBranch
                  logExpansion $ "Finished expansion of branch " ++ show n
                                 ++ " on " ++ show var)
               bodies [0..]
        lift completeFork



-- XXX allow this to handle primitives that can fail with all inputs known,
-- like less than, removing ops that succeed and killing branches that
-- fail.
-- XXX allow this to handle non-primitives with all inputs known by inlining.
expandPrim :: Prim -> OptPos -> Expander ()
expandPrim (PrimCall id pspec args gFlows) pos = do
    args' <- mapM expandArg args
    let call' = PrimCall id pspec args' gFlows
    logExpansion $ "  Expand call " ++ show call'
    inliningNow <- gets inlining
    if inliningNow
    then do
        logExpansion "  Cannot inline:  already inlining"
        addInstr call' pos
    else do
        def <- lift2 $ getProcDef pspec
        case procImpln def of
            ProcDefSrc _ -> shouldnt $ "uncompiled proc: " ++ show pspec
            ProcDefPrim{procImplnProto = proto, procImplnBody = body} ->
                if procInline def
                then inlineCall proto args' body pos
                else do
                    -- inlinableLast <- gets (((final && singleCaller def
                    --                          && procVis def == Private) &&)
                    --                        . noFork)
                    let inlinableLast = False
                    if inlinableLast
                    then do
                        logExpansion "  Inlining tail call to branching proc"
                        inlineCall proto args' body pos
                    else do
                        logExpansion "  Not inlinable"
                        addInstr call' pos
expandPrim call@(PrimHigher id fn args) pos = do
    logExpansion $ "  Expand higher call " ++ show call
    fn' <- expandArg fn
    case fn' of
        ArgClosure pspec closed _ -> do
            pspec' <- fromMaybe pspec <$> lift (lift $ maybeGetClosureOf pspec)
            logExpansion $ "  As first order call to " ++ show pspec'
            gFlows <- lift2 $ getProcGlobalFlows pspec
            expandPrim (PrimCall id pspec' (closed ++ args) gFlows) pos
        _ -> do
            args' <- mapM expandArg args
            logExpansion $ "  As higher call to " ++ show fn'
            addInstr (PrimHigher id fn' args') pos
expandPrim (PrimForeign lang nm flags args) pos = do
    st <- get
    logExpansion $ "  Expanding " ++ show (PrimForeign lang nm flags args)
    logExpansion $ "    with renaming = " ++ show (renaming st)
    args' <- mapM expandArg args
    logExpansion $ "  --> " ++ show (PrimForeign lang nm flags args')
    addInstr (PrimForeign lang nm flags args')  pos
    st' <- get
    logExpansion $ "    renaming = " ++ show (renaming st')



inlineCall :: PrimProto -> [PrimArg] -> ProcBody -> OptPos -> Expander ()
inlineCall proto args body pos = do
    saved <- get
    logExpansion $ "  Before inlining:"
    logExpansion $ "    renaming = " ++ show (renaming saved)
    modify (\s -> s { renaming = identityRenaming,
                      inlining = True })
    mapM_ (addOutputNaming pos) $ zip (primProtoParams proto) args
    mapM_ (addInputAssign pos) $ zip (primProtoParams proto) args
    logExpansion $ "  Inlining defn: " ++ showBlock 4 body
    expandBody body
    -- restore the saved state except the "nextCallSiteID"
    callSiteID <- gets nextCallSiteID
    put $ saved {nextCallSiteID = callSiteID}
    st <- get
    logExpansion $ "  After inlining:"
    logExpansion $ "    renaming = " ++ show (renaming st)


expandArg :: PrimArg -> Expander PrimArg
expandArg arg@(ArgVar var ty flow ft _) = do
    renameAll <- gets inlining
    if renameAll
    then case flow of
        FlowOut -> freshVar var ty ft
        FlowIn ->
            setArgType ty . setArgFlowType ft
            <$> gets (Map.findWithDefault arg var . renaming)
        FlowOutByReference  -> shouldnt "FlowOutByReference not available at this stage of compilation"
        FlowTakeReference -> shouldnt "FlowTakeReference not available at this stage of compilation"
    else return arg
expandArg arg@(ArgClosure ps as ty) = do
    as' <- mapM expandArg as
    return $ ArgClosure ps as' ty
expandArg arg = return arg


inputOutputParams :: PrimProto -> (Set PrimVarName,Set PrimVarName)
inputOutputParams proto =
  let setFromParamList = (Set.fromList . List.map primParamName)
      (ins,outs) = List.partition ((==FlowIn) . primParamFlow)
                   $ primProtoParams proto
  in  (setFromParamList ins, setFromParamList outs)


-- |Add a writeNaming assignment of output parameter to output argument
--  for a call.  Any subsequent assignment of the parameter variable should
--  be replaced with an assignment of the argument variable, rather than
--  generating a temp variable name.
addOutputNaming :: OptPos -> (PrimParam,PrimArg) -> Expander ()
addOutputNaming _ (param@(PrimParam pname ty FlowOut _ _),
                     v@ArgVar{argVarName=vname}) = do
    when (AnyType == ty) $
      shouldnt $ "Danger: untyped param: " ++ show param
    when (AnyType == argType v) $
      shouldnt $ "Danger: untyped argument: " ++ show v
    logExpansion $ "  recording output naming for " ++ show pname
      ++ " -> " ++ show vname
    modify (\s -> s { writeNaming = Map.insert pname v (writeNaming s)})
addOutputNaming _ _ = return ()


-- |Add an assignment of input argument to parameter in preparation for
-- inlining a call. The parameter name must be substituted with a new name;
-- the argument has already been renamed as appropriate for the calling
-- context.
addInputAssign :: OptPos -> (PrimParam,PrimArg) -> Expander ()
addInputAssign pos (param@(PrimParam name ty FlowIn ft _),v) = do
    newVar <- freshVar name ty ft
    addInstr (PrimForeign "llvm" "move" [] [v,newVar]) pos
addInputAssign _ _ = return ()



-- renameParam :: Renaming -> PrimParam -> PrimParam
-- renameParam renaming param@(PrimParam name typ FlowOut ftype inf ) =
--     maybe param
--     (\arg -> case arg of
--           ArgVar name' _ _ _ _ -> PrimParam name' typ FlowOut ftype inf
--           _ -> param) $
--     Map.lookup name renaming
-- renameParam _ param = param


-- singleCaller :: ProcDef -> Bool
-- singleCaller def =
--     let m = procCallers def
--     in  Map.size m == 1 && (snd . Map.findMin) m == 1


-- |Log a message, if we are logging inlining and code expansion activity.
logExpansion :: String -> Expander ()
logExpansion s = lift2 $ logMsg Expansion s
