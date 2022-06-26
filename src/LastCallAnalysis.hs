--  File     : LastCallAnalysis.hs
--  Author   : Chris Chamberlain
--  Purpose  : Transform proc bodies and their output arguments so that
--             more recursive algorithms can be tail-call optimised.
--  Copyright: (c) 2015-2022 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module LastCallAnalysis (lastCallAnalyseMod, lastCallAnalyseProc, inseparablePrims) where
import AST
import qualified Data.List as List
import qualified UnivSet
import Options (LogSelection(LastCallAnalysis),
                optimisationEnabled, OptFlag(TailCallModCons))
import Util (sccElts, lift2)
import Data.Foldable (foldrM, foldlM)
import Data.List.Predicate (allUnique)
import Callers (getSccProcs)
import Data.Graph (SCC (AcyclicSCC, CyclicSCC))
import Control.Monad.State (StateT (runStateT), MonadTrans (lift), execStateT, execState, runState, MonadState (get, put), gets, modify, unless, MonadPlus (mzero), MonadIO (liftIO))
import Control.Monad ( liftM, (>=>), when )
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (listToMaybe, fromJust)
import Data.List (intercalate)
import System.IO (hPutStrLn, stderr)
import qualified Data.Text as T
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)

-- | Perform last call analysis on a single module.
-- Internally, we perform analysis bottom-up on proc SCCs.
lastCallAnalyseMod :: ModSpec -> Compiler ()
lastCallAnalyseMod thisMod = do
    reenterModule thisMod
    orderedProcs <- getSccProcs thisMod
    logLastCallAnalysis $ ">>> Analyse Mod:" ++ show thisMod
    logLastCallAnalysis $ ">>> Ordered Procs:" ++ show orderedProcs
    logLastCallAnalysis $ ">>> Analyse SCCs: \n" ++
        unlines (List.map ((++) "    " . show . sccElts) orderedProcs)
    tcmcOpt <- gets (optimisationEnabled TailCallModCons . options)
    when tcmcOpt $ mapM_ (updateEachProcM lastCallAnalyseProc) orderedProcs
    -- We need to fixup calls regardless whether tcmc is enabled or not,
    -- as there could be modified calls to e.g.: standard library functions
    -- Also, we try where possible to write outByReference outputs from other
    -- calls directly into a destination structure, rather than first `load`
    -- then `mutate`.
    mapM_ (updateEachProcM fixupProc) orderedProcs
    reexitModule

-- | Apply a mapping function to each proc in an SCC
updateEachProcM :: (ProcDef -> Compiler ProcDef) -> SCC ProcSpec -> Compiler ()
updateEachProcM f (AcyclicSCC pspec) = updateProcDefM f pspec
updateEachProcM f (CyclicSCC pspecs) = mapM_ (updateProcDefM f) pspecs

-- | Analyse whether a proc is suitable for last-call -> tail-call transformation.
-- If so, we:
--   (1) modify the function's signature, switching some outputs to FlowOutByReference
--   (2) mark the last call with the LPVM `tail` attribute
--   (3) mark the mutate() instructions after the last call with `takeReference` flows
lastCallAnalyseProc :: ProcDef -> Compiler ProcDef
lastCallAnalyseProc def = do
    let impln = procImpln def
    let spec = procImplnProcSpec impln
    let proto = procImplnProto impln
    let body = procImplnBody impln
    logLastCallAnalysis $ ">>> Last Call Analysis: " ++ show spec
    case procVariant def of
        ClosureProc {} -> do
            logLastCallAnalysis "skipping closure proc, shouldn't have direct tail-recursion anyway"
            return def
        _ -> do
            (maybeBody', finalState) <- runStateT (runMaybeT (mapProcLeavesM transformLeaf body))
                LeafTransformState { procSpec = spec, originalProto = proto, outByReferenceArguments = Set.empty }
            case maybeBody' of
                Just body' -> do
                    let outByRefArgs = outByReferenceArguments finalState
                    unless (null outByRefArgs) $ logLastCallAnalysis $ "out by reference arguments: " ++ show outByRefArgs
                    proto' <- modifyProto proto (outByReferenceArguments finalState)
                    unless (null outByRefArgs) $ logLastCallAnalysis $ "new proto: " ++ show proto'
                    return def {procImpln = impln{procImplnProto = proto', procImplnBody = body'}}
                _ -> return def

data LeafTransformState = LeafTransformState {
    procSpec :: ProcSpec,
    originalProto :: PrimProto,
    outByReferenceArguments :: Set ParameterID
}

type LeafTransformer = MaybeT (StateT LeafTransformState Compiler)

-- | Run our analysis on a single leaf of the function body,
-- collecting state inside the LeafTransformer monad.
--
-- XXX: we should relax the assumption that last calls must be in the
-- leaves of a proc body, as there are real-world examples which defy this
-- assumption, e.g.: see test-cases/final-dump/tcmc_partition.wybe.
transformLeaf :: [Placed Prim] -> LeafTransformer [Placed Prim]
transformLeaf lastBlock = do
    spec <- gets procSpec
    case partitionLastCall lastBlock of
        -- XXX: we currently only consider directly-recursive calls,
        --      it would be nice to handle mutual recursion too.
        (Just (beforeCall, lastCall), afterLastCall@(_:_)) | primIsCallToProcSpec lastCall spec -> do
            logLeaf $ "identified a directly-recursive last-call: " ++ show lastCall
            logLeaf $ "before: " ++ showPrims beforeCall ++ "\nafter: " ++ showPrims afterLastCall
            -- First we identify whether we can move this last call below some of the prims
            -- i.e.: the prims don't depend on any values produced by the last call
            (lastCall', movedAboveCall, remainingBelowCall) <- lift2 $ tryMovePrimBelowPrims lastCall afterLastCall
            -- Next, we look at the remaining prims which couldn't be simply moved before the last call,
            -- to see if they are just "filling in the fields" of struct(s) with
            -- outputs from the last call.
            (movedAboveCall2, mutateGraph, remainingBelowCall') <- lift2 $ buildMutateGraph lastCall' isOutputFlow remainingBelowCall
            case remainingBelowCall' of
                [] -> do
                    let outByRefArgs = [name | (name, node) <- Map.assocs mutateGraph, callOutputIsOutByRef node]
                    let outByRefIndices = Set.fromList [fromJust $ List.findIndex (\case
                            ArgVar {argVarName=name'} -> name == name'
                            _ -> False) (fst . primArgs $ content lastCall) | name <- outByRefArgs]

                    -- The output parameters which we want to convert to be
                    -- `FlowOutByReference` are the union of parameters we want to
                    -- convert for each leaf in the proc body.
                    modify (\state@LeafTransformState{outByReferenceArguments=params} ->
                        state { outByReferenceArguments = Set.union params outByRefIndices }
                        )

                    -- We annotate the final call + remaining mutates with appropriate
                    -- `FlowOutByReference` and `FlowTakeReference` flows.
                    let body' = beforeCall ++ movedAboveCall ++ movedAboveCall2 ++
                            [contentApply (transformCall outByRefArgs) lastCall] ++ mutateGraphPrims mutateGraph

                    logLeaf $ "modified body: " ++ showPrims body'
                    return body'
                _ -> do
                    logLeaf $ "error: there were leftover prims which didn't fit into a mutate chain:\n" ++ showPrims remainingBelowCall'
                    return lastBlock
        (Just (_, call), []) | primIsCallToProcSpec call spec -> do
            logLeaf "directly-recursive last call is already in tail position"
            return lastBlock
        (Just (_, call), _) -> do
            logLeaf $ "leaf didn't qualify for last-call transformation\n    last call: " ++ show call ++ "\n    pspec: " ++ show spec
            return lastBlock
        _ -> do
            logLeaf "leaf didn't qualify for last-call transformation - didn't find a tail call"
            return lastBlock

-- Returns true if this prim is calling proc spec
primIsCallToProcSpec :: Placed Prim -> ProcSpec -> Bool
primIsCallToProcSpec p spec = case content p of
    (PrimCall _ spec' _ _) | procSpecMod spec == procSpecMod spec' &&
                             procSpecName spec == procSpecName spec' &&
                             procSpecID spec == procSpecID spec' -> True
    _ -> False

-- | Returns true if `prim` uses any of the outputs generated by `otherPrims`
-- If this is the case, then it is not possible to move `prim` before the last call.
primsUseOutputsOfPrims :: [Prim] -> [Prim] -> Bool
primsUseOutputsOfPrims prims otherPrims =
    let
        primInputs = varsInPrims isInputFlow prims
        anyGlobals = all (\prim -> let globals = snd $ primArgs prim
            in not (UnivSet.isEmpty (globalFlowsIn globals)) || not (UnivSet.isEmpty (globalFlowsOut globals))
            ) prims
        otherPrimOutputs = varsInPrims isOutputFlow otherPrims
    in
    -- if the prim refers to any global variables, then skip reordering (conservative approximation for now)
    -- otherwise, check it doesn't refer to any outputs from `otherPrims`
    anyGlobals || Set.size (Set.intersection primInputs otherPrimOutputs) > 0

-- | Converts a subset of proc outputs to be
--   `FlowOutByReference` instead of `FlowOut`
modifyProto :: PrimProto -> Set ParameterID -> Compiler PrimProto
modifyProto proto outByRefOutputs = do
    let params = primProtoParams proto
    let makeParamsOutByReference = (\i param@PrimParam{primParamFlow=flow } ->
            if i `notElem` outByRefOutputs then
                param
            else case flow of
                FlowOut -> param { primParamFlow = FlowOutByReference }
                _ -> shouldnt "can only convert FlowOut -> FlowOutByReference"
            )
    return proto { primProtoParams = zipWith makeParamsOutByReference [0..] params }

-- | Turn the specified set of arguments into FlowOutByReference arguments.
transformCall :: [PrimVarName] -> Prim -> Prim
transformCall outByRefArgs call@(PrimCall siteId spec args globalFlows) =
    PrimCall siteId spec (map (\arg ->
        case arg of
            var@ArgVar { argVarName = name } | name `elem` outByRefArgs
                -> var { argVarFlow = FlowOutByReference }
            _ -> arg
        ) args) globalFlows
transformCall _ _ = shouldnt "not a call"

newtype MutateInstr a = MutateInstr a

instance HasPrim a => Show (MutateInstr a) where
    show (MutateInstr p) = show (getPrim p)

data Source a =
    -- a mutate() call
    ResultFromMutate (MutateInstr a)
    -- a value which was available *before* the last call (e.g.: the head of the
    -- list in append)
    | ResultFromBeforeCall
    -- a value which is one of the outputs of the last call.
    | ResultFromCall { callResultFlow :: PrimFlow }
    deriving (Show)

type MutateGraph a = Map PrimVarName (Source a)

data MutateGraphArc = Member | Input deriving (Show, Eq, Ord)

class (Show a, Eq a) => HasPrim a where
    getPrim :: a -> Prim
    setPrim :: Prim -> a -> a

instance HasPrim (Placed Prim) where
    getPrim = content
    setPrim p' = contentApply (const p')

instance HasPrim Prim where
    getPrim = id
    setPrim p _ = p

instance HasPrim (Bool, Placed Prim) where
    getPrim (_, p) = content p
    setPrim p' (x, p) = (x, contentApply (const p') p)

sourceIsBeforeCall :: Source a -> Bool
sourceIsBeforeCall ResultFromBeforeCall = True
sourceIsBeforeCall _ = False

showPrims :: HasPrim a => [a] -> String
showPrims ps = show (getPrim <$> ps)

tryMovePrimBelowPrims :: HasPrim a => a -> [a] -> Compiler (a, [a], [a])
tryMovePrimBelowPrims prim otherPrims = do
    (prim, above, below) <- tryMovePrimBelowPrims' otherPrims (prim, [], [])
    logLastCallAnalysis $ "moved below: " ++ showPrims above
    logLastCallAnalysis $ "remaining below: " ++ showPrims below
    return (prim, above, below)

-- when optimizing writes directly into structures,
-- we need to treat "a call plus subseqent takeReference mutate()s" as an atomic
-- statement that is not allowed to be split up.
tryMovePrimBelowPrims' :: HasPrim a => [a] -> (a, [a], [a]) -> Compiler (a, [a], [a])
tryMovePrimBelowPrims' [] state = return state
tryMovePrimBelowPrims' (nextPrim:remainingPrims) (prim, above, below) =
    let (takeReferences, remainingPrims') = inseparablePrims nextPrim remainingPrims
        nextPrims = nextPrim:takeReferences
    in
    if primsUseOutputsOfPrims (getPrim <$> nextPrims) (getPrim <$> (prim:below))
    then do
        logLastCallAnalysis $ "cannot move " ++ showPrims (prim:below) ++ " below " ++ showPrims nextPrims
        tryMovePrimBelowPrims' remainingPrims' (prim, above, below ++ nextPrims)
    else do
        logLastCallAnalysis $ "can move " ++ showPrims (prim:below) ++ " below " ++ showPrims nextPrims
        let lastUseVarsToSwap = varsInPrims' (\flow isFinalUse -> isFinalUse) (getPrim <$> nextPrims)
        unless (null lastUseVarsToSwap) $ logLastCallAnalysis $ "potentially swapping last use annotations `~` on " ++ show lastUseVarsToSwap
        let (nextPrims', prim':below') = swapLastUsed lastUseVarsToSwap (nextPrims, prim:below)
        unless (null lastUseVarsToSwap) $ logLastCallAnalysis $ "above=" ++ show nextPrims' ++ " below=" ++ show (prim':below')
        tryMovePrimBelowPrims' remainingPrims' (prim', above ++ nextPrims', below')

-- `var` is last used in list of prims `from`, we want to swap the last used
-- flag to the last prim arg in `to`, which references `var`.
swapLastUsed :: HasPrim a => Set PrimVarName -> ([a], [a]) -> ([a], [a])
swapLastUsed vars (from, to) =
        -- foldr works through `to` in reverse-order, so we mark the *final*
        -- occurence of each var as "final".
        let (to', varsNotFound) = List.foldr (setLastUse True) ([], vars) to
            (from', varsNotFound1) = List.foldr (setLastUse False) ([], Set.difference vars varsNotFound) from
        in
        if null varsNotFound1
            then (from', to')
            else shouldnt "expected to swap last use flag for all vars"

setLastUse :: HasPrim a => Bool -> a -> ([a], Set PrimVarName) -> ([a], Set PrimVarName)
setLastUse newFinalValue p (prims, vars) =
        let prim = getPrim p
            (args, gFlows) = primArgs prim
            (args', vars') = foldr (\arg (args, vars) -> case arg of
                        arg@ArgVar {argVarName = var, argVarFinal=_ } | var `elem` vars -> (arg { argVarFinal = newFinalValue }:args, Set.delete var vars)
                        _ -> (arg:args, vars)
                        ) ([], vars) args
            in
        (setPrim (replacePrimArgs prim args' gFlows) p : prims, vars')

-- | Given a prim and some subsequent prims, collects any prims that should
-- never be separated from the first prim.
--
-- For example, it's very important that we treat the following prims as an inseparable unit.
--
--     call_foo(..., outByReference x, outByReference)
--     mutate(..., takeReference x)
--     mutate(..., takeReference y)
--
-- Since codegen requires the mutate()'s to appear immediately after the call.
inseparablePrims :: HasPrim a => a -> [a] -> ([a], [a])
inseparablePrims prim prims = case getPrim prim of
    PrimCall callSiteId pSpec args gFlows ->
        let (takeReferenceMutates, rest) = span (\p ->
                case getPrim p of
                    PrimForeign "lpvm" "mutate" _ [_, _, _, ArgInt 1 _, _, _, ArgVar { argVarFlow = FlowTakeReference }]
                        -> True
                    _ -> False
                ) prims
        in
            (takeReferenceMutates, rest)
    _ -> ([], prims)

-- | The only prims allowed after a "would-be tail call" are `foreign lpvm mutate`
-- instructions, with specific conditions (e.g.: all the mutates have the
-- "destructive" flag set, and the fields they are writing
-- into don't alias)
buildMutateGraph :: HasPrim a => a -> (PrimFlow -> Bool) -> [a] -> Compiler ([a], MutateGraph a, [a])
buildMutateGraph call allowedOutputFlows prims = do
    (graph, remainingBelowCall) <- buildMutateGraph' call allowedOutputFlows prims Map.empty
    logLastCallAnalysis $ "built mutate graph: " ++ show graph
    logLastCallAnalysis $ graphvizOutput graph
    -- There may be some mutates in a chain which could be swapped such that
    -- some of them can be done before the last call.
    -- This allows us to handle the case of e.g.: snoc(tail: list(T), head: T)
    -- where the the `head` is written to after the tail.
    (pushedAboveCall, graph') <- slideMutatesOffGraph graph
    graph'' <- tcmcOptimizeGraph graph'
    logLastCallAnalysis $ "mutate graph v2: " ++ show graph''
    logLastCallAnalysis $ graphvizOutput graph''

    let validGraph = all (\(var, node) ->
            -- any variable in the graph may be used at most once
            List.length (varReferences graph var) <= 1 &&
            case node of
                -- last argument to mutate() must be marked as `final`
                (ResultFromMutate instr) -> let (_, _, final) = mutateInstrMember' instr in final
                _ -> True) (Map.assocs graph'')

    if validGraph then
        return (pushedAboveCall, graph'', remainingBelowCall)
    else
        return ([], Map.empty, prims)

buildMutateGraph' :: HasPrim a => a -> (PrimFlow -> Bool) -> [a] -> MutateGraph a -> Compiler (MutateGraph a, [a])
buildMutateGraph' lastCall allowedOutputFlows (prim:prims) graph = do
    result <- runExceptT (addMutateGraphVertex lastCall allowedOutputFlows prim graph)
    case result of
        Left msg -> do
            logLastCallAnalysis $ "failed to add " ++ show prim ++ " to mutate graph: " ++ msg
            return (graph, prim:prims)
        Right graph' -> do
            logLastCallAnalysis $ "added " ++ show prim ++ " to graph.\ngraph' = " ++ show graph'
            buildMutateGraph' lastCall allowedOutputFlows prims graph'
buildMutateGraph' _ _ [] graph = return (graph, [])

argVarHasName :: PrimArg -> PrimVarName -> Bool
argVarHasName ArgVar {argVarName=name} name' | name == name' = True
argVarHasName _ _ = False

callOutputIsOutByRef :: Source a -> Bool
callOutputIsOutByRef ResultFromCall { callResultFlow = FlowOutByReference } = True
callOutputIsOutByRef _ = False

addVarToMutateGraph :: HasPrim a => PrimVarName -> Prim -> (PrimFlow -> Bool) -> Bool -> MutateGraph a -> ExceptT String Compiler (Source a, MutateGraph a)
addVarToMutateGraph var lastCall allowedOutputFlows fromCallAllowed graph = do
    case Map.lookup var graph of
        (Just node) -> return (node, graph)
        Nothing -> do
            let callOutputs = varsInPrim isOutputFlow lastCall
            let (args, _) = primArgs lastCall
            let argFlow = [argFlowDirection arg | arg <- args, argVarHasName arg var]
            case listToMaybe argFlow of
                Nothing -> do
                    -- this var was created *before* the call
                    let node = ResultFromBeforeCall
                    let graph' = Map.insert var node graph
                    return (node, graph')
                (Just _) | not fromCallAllowed -> throwError "can't use an output from the last call in this context"
                (Just flow) | allowedOutputFlows flow -> do
                    let node = ResultFromCall { callResultFlow = flow }
                    let graph' = Map.insert var node graph
                    return (node, graph')
                -- Corner-case:
                -- When we are analyzing prims for the purposes of *deciding*
                -- whether or not we can make this call a tail call,
                -- we allow any FlowOut or FlowOutByReference output, since
                -- we will transform those outputs to be FlowOutByReference later on.
                -- However when we are analyzing prims for the purposes of writing
                -- directly into structures from an existing tail call,
                -- then we consider only outputs which are already
                -- FlowOutByReference, since we won't change the call signature
                -- anymore.
                (Just flow) -> throwError $ show var ++ " was created in last call with disallowed flow. Cannot add to mutate graph"

addMutateGraphVertex :: HasPrim a => a -> (PrimFlow -> Bool) -> a -> MutateGraph a -> ExceptT String Compiler (MutateGraph a)
addMutateGraphVertex lastCall allowedOutputFlows prim graph = do
    case getPrim prim of
        PrimForeign "lpvm" "mutate" _ [
            ArgVar { argVarName = input, argVarFlow = FlowIn },
            ArgVar { argVarName = output, argVarFlow = FlowOut },
            -- mutate() must be destructive
            ArgInt offsetArg _, ArgInt 1 _, _, _,
            ArgVar { argVarName = member, argVarFlow = FlowIn, argVarFinal = final }] -> do
                -- make sure `input` exists in the graph
                (inputNode, graph') <- addVarToMutateGraph input (getPrim lastCall) allowedOutputFlows False graph
                -- make sure `member` exists in the graph
                (memberNode, graph'') <- addVarToMutateGraph member (getPrim lastCall) allowedOutputFlows True graph'
                let mutateInstr = ResultFromMutate $ MutateInstr prim
                -- Check some conditions before adding this "mutate()" to the graph
                when (offsetArg `elem` getOffsetList graph'' inputNode) $
                    throwError "mutate()s in a single chain write to overlapping fields"
                let graph''' = Map.insert output mutateInstr graph''
                return graph'''
        _ ->
            throwError "not a mutate instr satisfying constraints"

-- Returns a list of offsets written to in a single mutate chain.
--
-- XXX: Consider both offset and size to determine if writes alias.
getOffsetList :: HasPrim a => MutateGraph a -> Source a -> [Integer]
getOffsetList graph ResultFromBeforeCall = []
getOffsetList graph ResultFromCall { } = shouldnt "mutate() shouldn't use result from call as it's input"
getOffsetList graph (ResultFromMutate instr) = let input = mutateInstrInput instr in
    case Map.lookup input graph of
        (Just inputNode) -> mutateInstrOffset instr : getOffsetList graph inputNode
        Nothing -> shouldnt $ show input ++ " not found in mutate graph"

-- Returns `True` if the given variable is currently
-- referred to in the mutate graph. We only allow each value to be
-- referenced *once* in the graph.
varReferences :: HasPrim a => MutateGraph a -> PrimVarName -> [MutateGraphArc]
varReferences graph var = foldr (\(name, node) arcs ->
        case node of
            ResultFromMutate instr | mutateInstrMember instr == var -> Input:arcs
            ResultFromMutate instr | mutateInstrMember instr == var -> Member:arcs
            _ -> arcs)
        [] (Map.assocs graph)

slideMutatesOffGraph :: HasPrim a => MutateGraph a -> Compiler ([a], MutateGraph a)
slideMutatesOffGraph graph = foldrM slideMutatesOffGraph' ([], graph) (Map.keys graph)

slideMutatesOffGraph' :: HasPrim a => PrimVarName -> ([a], MutateGraph a) -> Compiler ([a], MutateGraph a)
slideMutatesOffGraph' name state@(pushedOut, graph)
    = case Map.lookup name graph of
        Just (ResultFromMutate mutateInstr@(MutateInstr prim)) ->
            let member = mutateInstrMember mutateInstr
                input = mutateInstrInput mutateInstr in
            case (Map.lookup member graph, Map.lookup input graph) of
                -- The two inputs to this mutate are available before this call.
                -- Therefore we can move the mutate above the call.
                (Just ResultFromBeforeCall, Just ResultFromBeforeCall) -> do
                    logLastCallAnalysis $ "popping " ++ show mutateInstr ++ " out of graph."
                    let deleteMemberIfUnused = if List.length (varReferences graph member) > 1 then id else Map.delete member
                    let graph' = deleteMemberIfUnused . Map.delete input . Map.insert name ResultFromBeforeCall $ graph
                    logLastCallAnalysis $ "new graph: " ++ show graph'
                    return (pushedOut ++ [prim], graph')
                -- we can swap the two mutate()'s in the chain, in order to push the
                -- first mutate closer to a "sink" vertex (at which point we can then
                -- "pop" it out of the graph)
                (Just ResultFromBeforeCall, Just (ResultFromMutate mutateInstr0)) -> do
                    logLastCallAnalysis $ "swapping " ++ show mutateInstr
                    let (mutateInstr', mutateInstr0') = mutateInstrSwap mutateInstr mutateInstr0
                    let graph' = Map.insert name (ResultFromMutate mutateInstr0') . Map.insert input (ResultFromMutate mutateInstr') $ graph
                    logLastCallAnalysis $ "mutate graph after swap: " ++ show graph'
                    -- make sure we continue doing swaps
                    slideMutatesOffGraph' input (pushedOut, graph')
                (Nothing, _) -> shouldnt $ show member ++ " not found in graph"
                (_, Nothing) -> shouldnt $ show input ++ " not found in graph"
                _ -> return state
        Nothing -> do
            logLastCallAnalysis $ show name ++ " not found in graph - must have been removed already. Skipping..."
            return state
        _ -> return state

-- Annotate the graph with `outByReference` and `takeReference` as required
tcmcOptimizeGraph :: HasPrim a => MutateGraph a -> Compiler (MutateGraph a)
tcmcOptimizeGraph graph = foldrM tcmcOptimizeGraph' graph (Map.assocs graph)

tcmcOptimizeGraph' :: HasPrim a => (PrimVarName, Source a) -> MutateGraph a -> Compiler (MutateGraph a)
tcmcOptimizeGraph' (name, ResultFromMutate mutateInstr@(MutateInstr prim)) graph =
    let member = mutateInstrMember mutateInstr in
    case Map.lookup member graph of
        -- Turns the FlowOut argument of the call into FlowOutByReference,
        -- and also switches mutate(..., member) to mutate(..., takeReference member)
        (Just ResultFromCall { }) -> do
            let graph' = Map.insert name (ResultFromMutate $ mutateInstrTakeReference mutateInstr) . Map.insert member ResultFromCall { callResultFlow = FlowOutByReference } $ graph
            return graph'
        -- Turns mutate(x, ?y, ...) into mutate(x, outByReference y , ...)
        -- and mutate(..., y) to mutate(..., takeReference y)
        (Just (ResultFromMutate memberMutate)) -> do
            let graph' = Map.insert name (ResultFromMutate $ mutateInstrTakeReference mutateInstr) . Map.insert member (ResultFromMutate $ mutateInstrOutputByReference memberMutate) $ graph
            return graph'
        (Just ResultFromBeforeCall) -> shouldnt $ show member ++ " ResultFromBeforeCall should have already been removed"
        Nothing -> shouldnt $ show member ++ " not found in graph"
tcmcOptimizeGraph' (name, _) graph = return graph

-- | Returns the mutate() prims in a mutate graph, in order of appearance in the
-- LPVM IR.
-- Our mutate graph is essentially a directed-rooted-forest. So for each root
-- (proc output) there is exactly one path to each vertex.
mutateGraphPrims :: HasPrim a => MutateGraph a -> [a]
mutateGraphPrims graph = let sources = List.filter (null . varReferences graph) (Map.keys graph) in
    concatMap (mutateGraphPrims' graph) sources

-- | Returns the mutate() prims for a given node and it's descendents.
mutateGraphPrims' :: HasPrim a => MutateGraph a -> PrimVarName -> [a]
mutateGraphPrims' graph name = case Map.lookup name graph of
    (Just ResultFromCall {}) -> []
    (Just ResultFromBeforeCall) -> []
    (Just (ResultFromMutate mutateInstr@(MutateInstr prim))) ->
        mutateGraphPrims' graph (mutateInstrInput mutateInstr) ++
        mutateGraphPrims' graph (mutateInstrMember mutateInstr) ++
        [prim]
    Nothing -> shouldnt "source not found in graph"

mutateInstrMember :: HasPrim a => MutateInstr a -> PrimVarName
mutateInstrMember m =  let (name, _, _) = mutateInstrMember' m in name

mutateInstrMember' :: HasPrim a => MutateInstr a -> (PrimVarName, PrimFlow, Bool)
mutateInstrMember' (MutateInstr p) = case getPrim p of
    PrimForeign _ _ _ [_, _, _, _, _, _, ArgVar { argVarName = member, argVarFlow = flow, argVarFinal = final }] -> (member, flow, final)
    _ -> shouldnt "not a mutate instr"

mutateInstrInput :: HasPrim a => MutateInstr a -> PrimVarName
mutateInstrInput (MutateInstr p) = case getPrim p of
    PrimForeign _ _ _ (ArgVar { argVarName = input }:_) -> input
    _ -> shouldnt "not a mutate instr"

mutateInstrOutput' :: HasPrim a => MutateInstr a -> (PrimVarName, PrimFlow)
mutateInstrOutput' (MutateInstr p) = case getPrim p of
    PrimForeign _ _ _ (_:ArgVar { argVarName = name, argVarFlow = flow }:_) -> (name, flow)
    _ -> shouldnt "not a mutate instr"

mutateInstrOutput :: HasPrim a => MutateInstr a -> PrimVarName
mutateInstrOutput = fst . mutateInstrOutput'

mutateInstrOffset :: HasPrim a => MutateInstr a -> Integer
mutateInstrOffset (MutateInstr p) = case getPrim p of
    PrimForeign _ _ _ (_:_:(ArgInt offset _):_) -> offset
    _ -> shouldnt "not a mutate instr"

mutateInstrTakeReference :: HasPrim a => MutateInstr a -> MutateInstr a
mutateInstrTakeReference (MutateInstr p) = case getPrim p of
    PrimForeign mode name flags [input, output, offset, destructive, size, startOffset, member] ->
        MutateInstr $ setPrim (PrimForeign mode name flags [input, output, offset, destructive, size, startOffset, setArgFlow FlowTakeReference member]) p
    _ -> shouldnt "not a mutate instr"

mutateInstrOutputByReference :: HasPrim a => MutateInstr a -> MutateInstr a
mutateInstrOutputByReference (MutateInstr p) = case getPrim p of
    PrimForeign mode name flags (input:output:rest) ->
        MutateInstr $ setPrim (PrimForeign mode name flags (input:setArgFlow FlowOutByReference output:rest)) p
    _ -> shouldnt "not a mutate instr"

-- XXX: may need to update last use flags here?
mutateInstrSwap :: HasPrim a => MutateInstr a -> MutateInstr a -> (MutateInstr a, MutateInstr a)
mutateInstrSwap (MutateInstr p1) (MutateInstr p2) = case (getPrim p1, getPrim p2) of
    (PrimForeign "lpvm" "mutate" flags1 (input1:output1:rest1),
     PrimForeign "lpvm" "mutate" flags2 (input2:output2:rest2))
        -> let p1' = PrimForeign "lpvm" "mutate" flags1 (input2:output2:rest1)
               p2' = PrimForeign "lpvm" "mutate" flags2 (input1:output1:rest2)
               in
                (MutateInstr $ setPrim p1' p1, MutateInstr $ setPrim p2' p2)
    _ -> shouldnt "tried to swap two prims which aren't mutate() instrs"

----------------------------------------------------------------------------
-- Visualize mutate graphs                                                --
----------------------------------------------------------------------------

graphvizOutput :: HasPrim a => MutateGraph a -> String
graphvizOutput graph = "digraph D {\n" ++
    "    rankdir=\"BT\"\n" ++
    "    node [ordering=out]\n" ++
    intercalate "\n"["    " ++ varLabel name ++ " [style=\"filled\",fillcolor=\"" ++ graphvizVertexColor node ++ "\", label=\"" ++ varLabel name ++ "\\n" ++ graphvizVertexLabel name node ++ " \"]" | (name, node) <- Map.assocs graph] ++
    "\n" ++ intercalate "" [graphvizArcs name node | (name, node) <- Map.assocs graph] ++
    "\n}\n"

varLabel :: PrimVarName -> String
varLabel var = filter (/= '#') $ T.unpack $ T.replace (T.pack "##0") (T.pack "") (T.pack $ show var)

graphvizVertexColor :: HasPrim a => Source a -> String
graphvizVertexColor ResultFromMutate {} = "lightblue"
graphvizVertexColor ResultFromBeforeCall {} = "gray"
graphvizVertexColor ResultFromCall { callResultFlow = FlowOutByReference } = "lightgreen"
graphvizVertexColor ResultFromCall { callResultFlow = _ } = "salmon"

graphvizVertexLabel :: HasPrim a => PrimVarName -> Source a -> String
graphvizVertexLabel name (ResultFromMutate instr) = "mutate(_, " ++ outByRef ++ ", offset=" ++ show (mutateInstrOffset instr) ++ ", ...," ++ takeReference ++ ")"
    where takeReference = case mutateInstrMember' instr of
                        (name, FlowTakeReference, _) -> "takeReference " ++ varLabel name
                        _ -> "_"
          outByRef = case mutateInstrOutput' instr of
                        (name, FlowOutByReference) -> "outByReference " ++ varLabel name
                        _ -> "_"
graphvizVertexLabel name ResultFromBeforeCall = "(before call)"
graphvizVertexLabel name ResultFromCall {callResultFlow=flow}  = "(" ++ show flow ++ " from call)"

graphvizArcs :: HasPrim a => PrimVarName -> Source a -> String
graphvizArcs name (ResultFromMutate instr) =
    "    " ++ varLabel name ++ " -> " ++ varLabel (mutateInstrMember instr) ++ " [label=\"member\"]\n" ++
    "    " ++ varLabel name ++ " -> " ++ varLabel (mutateInstrInput instr) ++ " [label=\"input\"]\n"
graphvizArcs _ _ = ""

----------------------------------------------------------------------------
-- Write outByReference outputs directly into structures                  --
----------------------------------------------------------------------------

data ProcBodyAnnot = ProcBodyAnnot {
      bodyPrims' ::[(Bool, Placed Prim)],
      bodyFork' ::PrimForkAnnot}
              deriving (Eq, Show)

data PrimForkAnnot =
    NoForkAnnot |
    PrimForkAnnot {
      forkVar' :: PrimVarName,       -- ^The variable that selects branch to take
      forkVarType' :: TypeSpec,      -- ^The Wybe type of the forkVar
      forkVarLast' :: Bool,          -- ^Is this the last occurrence of forkVar
      forkBodies' :: [ProcBodyAnnot] -- ^one branch for each value of forkVar
    }
    deriving (Eq, Show)

allUnvisited :: ProcBody -> ProcBodyAnnot
allUnvisited body@ProcBody { bodyPrims=prims, bodyFork=fork} = ProcBodyAnnot { bodyPrims' = map (\p -> (False, p)) prims, bodyFork' =allUnvisitedFork fork}
allUnvisitedFork :: PrimFork -> PrimForkAnnot
allUnvisitedFork NoFork = NoForkAnnot
allUnvisitedFork PrimFork{forkVar=var, forkVarType=varTy, forkVarLast=varLast, forkBodies=bodies} = PrimForkAnnot{forkVar'=var, forkVarType'=varTy, forkVarLast'=varLast, forkBodies'=allUnvisited <$> bodies}

stripVisited :: ProcBodyAnnot -> ProcBody
stripVisited body@ProcBodyAnnot { bodyPrims'=prims, bodyFork'=fork} = ProcBody { bodyPrims = List.map snd prims, bodyFork = stripVisitedFork fork}
stripVisitedFork :: PrimForkAnnot -> PrimFork
stripVisitedFork NoForkAnnot = NoFork
stripVisitedFork PrimForkAnnot{forkVar'=var, forkVarType'=varTy, forkVarLast'=varLast, forkBodies'=bodies} = PrimFork {forkVar=var, forkVarType=varTy, forkVarLast=varLast, forkBodies=stripVisited <$> bodies}

markVisited :: (Bool, Placed Prim) -> (Bool, Placed Prim)
markVisited (_, p) = (True, p)

writeOutputsDirectlyIntoStructures :: ProcBodyAnnot -> Compiler ProcBodyAnnot
writeOutputsDirectlyIntoStructures procBody@ProcBodyAnnot{bodyPrims'=[], bodyFork'=NoForkAnnot} = return procBody
writeOutputsDirectlyIntoStructures procBody@ProcBodyAnnot{bodyPrims'=[], bodyFork'=fork@PrimForkAnnot{forkBodies'=bodies}} = do
    bodies' <- mapM writeOutputsDirectlyIntoStructures bodies
    return procBody{bodyFork'=fork{forkBodies'=bodies'}}
writeOutputsDirectlyIntoStructures procBody@ProcBodyAnnot{bodyPrims'=call@(False, _):prims} = do
    let argFlows = argFlowDirection <$> (fst . primArgs . getPrim $ call)
    newBody <- if FlowOutByReference `elem` argFlows then do
            logLastCallAnalysis $ "call " ++ show call ++ " has outByReference outputs"
            logLastCallAnalysis $ "trying to move call " ++ show call ++ " down right before outputs are needed"
            (call', above, below) <- tryMovePrimBelowPrims call prims
            -- For each FlowOutByReference output, we want to know if it
            -- appears as the last argument to exactly 1 mutate().
            -- In this case, we believe it is safe to turn that mutate into a
            -- `FlowTakeReference`-style mutate.
            (above2, mutateGraph, below') <- buildMutateGraph call' (==FlowOutByReference) below

            if null mutateGraph
                then do
                    logLastCallAnalysis "keeping existing body"
                    return procBody{bodyPrims'=markVisited call : prims}
                else do
                    let body' = procBody{bodyPrims'=above ++ above2 ++ [markVisited call'] ++ mutateGraphPrims mutateGraph ++ below'}
                    logLastCallAnalysis $ "new body: " ++ show (stripVisited body')
                    return body'
        else return procBody{bodyPrims'=markVisited call:prims}
    writeOutputsDirectlyIntoStructures newBody
writeOutputsDirectlyIntoStructures procBody@ProcBodyAnnot{bodyPrims'=(_, prim):prims} = do
    body' <- writeOutputsDirectlyIntoStructures procBody{bodyPrims'=prims}
    return $ body'{bodyPrims'=(True, prim):bodyPrims' body'}

----------------------------------------------------------------------------
-- Coerce FlowOut into FlowOutByReference                                 --
----------------------------------------------------------------------------

-- | Check the proc protos of all callees, and coerce FlowOut into
-- FlowOutByReference where needed.
fixupProc :: ProcDef -> Compiler ProcDef
fixupProc def@ProcDef { procImpln = impln@ProcDefPrim { procImplnBody = body}} = do
    logLastCallAnalysis $ ">>> Fix up calls in proc: " ++ show (procName def)
    body' <- mapProcPrimsM (updatePlacedM fixupPrim) body
    logLastCallAnalysis $ ">>> Write outputs directly into structures: " ++ show (procName def)
    body'' <- writeOutputsDirectlyIntoStructures (allUnvisited body')
    let body''' = stripVisited body''
    return $ def { procImpln = impln { procImplnBody = body''' } }
fixupProc _ = shouldnt "uncompiled"

fixupPrim :: Prim -> Compiler Prim
fixupPrim p@(PrimCall siteId pspec args gFlows) = do
    proto <- getProcPrimProto pspec
    let args' = coerceArgs args (primProtoParams proto)
    let call' = PrimCall siteId pspec args' gFlows
    when (args /= args') $ logLastCallAnalysis $ "coerced call: " ++ show p ++ "\n          to: " ++ show call'
    return call'
fixupPrim p = return p

-- | Coerce FlowOut arguments into FlowOutByReference where needed
coerceArgs :: [PrimArg] -> [PrimParam] -> [PrimArg]
coerceArgs [] []    = []
coerceArgs [] (_:_) = shouldnt "more parameters than arguments"
coerceArgs (_:_) [] = shouldnt "more arguments than parameters"
coerceArgs (a@ArgVar{argVarFlow = FlowOut}:as) (p@PrimParam{primParamFlow=FlowOutByReference }:ps) =
    let rest = coerceArgs as ps in
    a { argVarFlow = FlowOutByReference }:rest
coerceArgs (a:as) (p:ps) = a:coerceArgs as ps

----------------------------------------------------------------------------
-- Helpers                                                                --
----------------------------------------------------------------------------

partitionLastCall :: [Placed Prim] -> (Maybe ([Placed Prim], Placed Prim), [Placed Prim])
partitionLastCall prims = let (lastCall, after) = _partitionLastCall $ reverse prims
    in (lastCall, reverse after)

-- XXX: rewrite to use `List.span`
_partitionLastCall :: [Placed Prim] -> (Maybe ([Placed Prim], Placed Prim), [Placed Prim])
_partitionLastCall [] = (Nothing, [])
_partitionLastCall (x:xs) =
    case content x of
        PrimCall {} -> (Just (reverse xs, x), [])
        _ -> let (lastCall, afterLastCall) = _partitionLastCall xs
            in (lastCall, x:afterLastCall)

-- | Applies a transformation to the leaves of a proc body
mapProcLeavesM :: (Monad t) => ([Placed Prim] -> t [Placed Prim]) -> ProcBody -> t ProcBody
mapProcLeavesM f leafBlock@ProcBody { bodyPrims = prims, bodyFork = NoFork } = do
        prims <- f prims
        return leafBlock { bodyPrims = prims }
mapProcLeavesM f current@ProcBody { bodyFork = fork@PrimFork{forkBodies = bodies} } = do
        bodies' <- mapM (mapProcLeavesM f) bodies
        return current { bodyFork = fork { forkBodies = bodies' } }

-- | Applies a transformation to each prim in a proc
mapProcPrimsM :: (Monad t) => (Placed Prim -> t (Placed Prim)) -> ProcBody -> t ProcBody
mapProcPrimsM fn body@ProcBody { bodyPrims = prims, bodyFork = NoFork } = do
        prims' <- mapM fn prims
        return body { bodyPrims = prims' }
mapProcPrimsM fn body@ProcBody { bodyPrims = prims, bodyFork = fork@PrimFork{forkBodies = bodies } } = do
        prims' <- mapM fn prims
        bodies <- mapM (mapProcPrimsM fn) bodies
        return body { bodyPrims = prims', bodyFork = fork { forkBodies = bodies } }

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

-- | Logging from the Compiler monad to LastCallAnalysis.
logLastCallAnalysis :: String -> Compiler ()
logLastCallAnalysis = logMsg LastCallAnalysis

-- | Logging from the Compiler monad to LastCallAnalysis.
logLeaf :: String -> LeafTransformer ()
logLeaf s = lift2 $ logMsg LastCallAnalysis s
