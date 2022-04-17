--  File     : LastCallAnalysis.hs
--  Author   : Chris Chamberlain
--  Purpose  : Transform proc bodies and their output arguments so that
--             more recursive algorithms can be tail-call optimised.
--  Copyright: (c) 2015-2022 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE LambdaCase #-}

module LastCallAnalysis (lastCallAnalyseMod, lastCallAnalyseProc) where
import AST
import qualified Data.List as List
import qualified UnivSet
import Options (LogSelection(LastCallAnalysis))
import Util (sccElts, lift2)
import Data.Foldable (foldrM)
import Data.List.Predicate (allUnique)
import Callers (getSccProcs)
import Data.Graph (SCC (AcyclicSCC, CyclicSCC))
import Control.Monad.State (StateT (runStateT), MonadTrans (lift), execStateT, execState, runState, MonadState (get, put), gets, modify, unless, MonadPlus (mzero))
import Control.Monad (liftM, (>=>))
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))
import Control.Monad (when)

lastCallAnalyseMod :: ModSpec -> Compiler ()
lastCallAnalyseMod thisMod = do
    reenterModule thisMod
    orderedProcs <- getSccProcs thisMod
    logLastCallAnalysis $ ">>> Analyse Mod:" ++ show thisMod
    logLastCallAnalysis $ ">>> Ordered Procs:" ++ show orderedProcs
    logLastCallAnalysis $ ">>> Analyse SCCs: \n" ++
        unlines (List.map ((++) "    " . show . sccElts) orderedProcs)
    mapM_ (forEachProc lastCallAnalyseProc) orderedProcs
    mapM_ (forEachProc fixupCallsInProc) orderedProcs
    reexitModule

forEachProc :: (ProcDef -> Compiler ProcDef) -> SCC ProcSpec -> Compiler ()
forEachProc f (AcyclicSCC pspec) = updateProcDefM f pspec
forEachProc f (CyclicSCC pspecs) = mapM_ (updateProcDefM f) pspecs

lastCallAnalyseProc :: ProcDef -> Compiler ProcDef
lastCallAnalyseProc def = do
    let impln = procImpln def
    let spec = procImplnProcSpec impln
    let proto = procImplnProto impln
    let body = procImplnBody impln
    logLastCallAnalysis $ ">>> Last Call Analysis: " ++ show spec
    (maybeBody', finalState) <- runStateT (runMaybeT (mapProcLeavesM transformLeaf body))
        LeafTransformState { procSpec = spec, originalProto = proto, transformedProto = Nothing }
    case (maybeBody', transformedProto finalState) of
        (Just body', Just proto') -> do
            logLastCallAnalysis $ "new proto: " ++ show proto'
            return def {procImpln = impln{procImplnProto = proto', procImplnBody = body'}}
        _ -> return def

fixupCallsInProc :: ProcDef -> Compiler ProcDef
fixupCallsInProc def@ProcDef { procImpln = impln@ProcDefPrim { procImplnBody = body}} = do
    logLastCallAnalysis $ ">>> Fix up calls in proc: " ++ show (procName def)
    body' <- mapProcPrimsM (updatePlacedM fixupCallsInPrim) body
    return $ def { procImpln = impln { procImplnBody = body' } }
fixupCallsInProc _ = shouldnt "uncompiled"

fixupCallsInPrim :: Prim -> Compiler Prim
fixupCallsInPrim p@(PrimCall siteId pspec args gFlows attrs) = do
    logLastCallAnalysis $ "checking call " ++ show p
    proto <- getProcPrimProto pspec
    let args' = coerceArgs args (primProtoParams proto)
    when (args /= args') $ logLastCallAnalysis $ "coerced args: " ++ show args ++ " " ++ show args'
    return $ PrimCall siteId pspec args' gFlows attrs
fixupCallsInPrim p = return p

-- coerce FlowOut arguments into FlowOutByReference where needed
coerceArgs :: [PrimArg] -> [PrimParam] -> [PrimArg]
coerceArgs [] []    = []
coerceArgs [] (_:_) = shouldnt "more parameters than arguments"
coerceArgs (_:_) [] = shouldnt "more arguments than parameters"
coerceArgs (a@ArgVar{argVarFlow = FlowOut}:as) (p@PrimParam{primParamFlow=FlowOutByReference }:ps) =
    let rest = coerceArgs as ps in
    a { argVarFlow = FlowOutByReference }:rest
coerceArgs (a:as) (p:ps) = a:coerceArgs as ps

data LeafTransformState = LeafTransformState {
    procSpec :: ProcSpec,
    originalProto :: PrimProto,
    transformedProto :: Maybe PrimProto
}

type LeafTransformer = MaybeT (StateT LeafTransformState Compiler)

transformLeaf :: [Placed Prim] -> LeafTransformer [Placed Prim]
transformLeaf lastBlock = do
    spec <- gets procSpec
    case partitionLastCall lastBlock of
        -- TODO: use multiple specialization to relax the restriction that
        --       the last call is a directly-recursive call...
        (Just (beforeCall, call), afterLastCall) | isDirectRecursiveCall (content call) spec -> do
            let lastCall = content call
            logLeaf $ "identified a directly-recursive last-call: " ++ show call
            logLeaf $ "before: " ++ show beforeCall ++ "\nafter: " ++ show afterLastCall
            -- First we identify all the prims which can be trivially moved before the last call
            -- i.e.: the prim doesn't depend on any values produced by the last call (or subsequent prims)
            logLeaf "moving prims before last call where possible"
            let MovePrimsResult { remaining = remainingAfterLastCall, succeeded = movedBeforeLastCall } = tryMovePrimsBeforeLastCall lastCall afterLastCall MovePrimsResult { remaining = [], succeeded = [] }
            logLeaf $ "still remaining after last call: " ++ show (reverse remainingAfterLastCall)
            -- Next, we look at the remaining prims which couldn't be simply moved before the last call,
            -- to see if they are just "filling in the fields" of struct(s) with outputs from the last call.
            case foldrM (analyzePrimAfterLastCall (content call)) [] (reverse remainingAfterLastCall) of
                Right mutateChains -> do
                    -- Finally, we check that writes in a single "mutate-chain" don't alias fields.
                    -- This could be bad, since we cannot guarantee that the called proc will write to fields in any particular order.
                    -- In this case, we apply a transformation to make the call the final prim in the proc.
                    --
                    -- XXX: take into account size as well as offset when determining aliasing?
                    if all (allUnique . List.map (trustArgInt . offsetArg)) mutateChains
                    then do
                        proto <- gets originalProto
                        proto'' <- lift2 $ modifyProto proto mutateChains
                        -- attempts to modify this proc's proto.
                        -- will abort if we already tried to modify it
                        -- incompatibly in a different leaf.
                        trySetProto proto''

                        logLeaf $ "remaining prims meet requirements for last call -> tail call transform\nmutate chains: " ++ show mutateChains
                        logLeaf $ "modified proto: " ++ show proto''

                        body' <- lift2 $ buildTailCallLeaf (beforeCall ++ reverse movedBeforeLastCall) call mutateChains

                        logLeaf $ "modified leaf: " ++ show body'
                        return body'
                    else do
                        logLeaf "mutate instructions alias! aborting"
                        return lastBlock
                Left error -> do
                    logLeaf $ "remaining prims didn't satisfy constraints: " ++ error
                    return lastBlock
        -- (Just (beforeCall, call), afterLastCall@[]) | isDirectRecursiveCall (content call) spec -> do
        --     logLeaf "last call is already in tail position, adding `musttail` LPVM call attr"
        --     proto <- gets originalProto
        --     trySetProto proto
        --     return $ beforeCall ++ [contentApply (addAttributeToCall Tail) call]
        _ -> do
            logLeaf "leaf didn't qualify for last-call transformation"
            return lastBlock

isDirectRecursiveCall :: Prim -> ProcSpec -> Bool
isDirectRecursiveCall (PrimCall _ spec' _ _ _) spec | spec == spec' = True
isDirectRecursiveCall _ _ = False

trySetProto :: PrimProto -> LeafTransformer ()
trySetProto proto'' = do
                        proto <- gets originalProto
                        proto' <- gets transformedProto
                        case proto' of
                            Just proto' | proto' /= proto'' -> do
                                logLeaf $ "conflicting protos" ++ show proto' ++ "\n" ++ show proto''
                                mzero
                            _ -> do
                                logLeaf $ "setting transformed proto: " ++ show proto''
                                modify $ \s -> s { transformedProto = Just proto'' }

addAttributeToCall :: PrimCallAttribute  -> Prim -> Prim
addAttributeToCall attr (PrimCall id spec args gFlows attrs) = PrimCall id spec args gFlows (Set.insert attr attrs)
addAttributeToCall attr _ = shouldnt "not a call"

-- Returns true if `prim` uses any of the outputs generated by `otherPrims`
-- If this is the case, then it is not possible to move `prim` before the last call.
primUsesOutputsOfOtherPrims :: Prim -> [Prim] -> Bool
primUsesOutputsOfOtherPrims prim otherPrims =
    let (args, globals) = primArgs prim
        vars = varsInPrimArgs FlowIn args
        otherPrimOutputs = varsInPrims FlowOut otherPrims
    in
    -- if the prim refers to any global variables, then skip reordering (conservative approximation for now)
    -- otherwise, check it doesn't refer to any outputs from `otherPrims`
    not (UnivSet.isEmpty (globalFlowsIn globals) && UnivSet.isEmpty (globalFlowsOut globals)) || any (`elem` otherPrimOutputs) vars

-- Finds outputs which are the final result of a mutate chain
-- and modifies them to be `FlowOutByReference` instead of `FlowOut`
modifyProto :: PrimProto -> [MutateChain] -> Compiler PrimProto
modifyProto proto [] = return proto
modifyProto proto (mutateChain:xs) = do
    proto' <- modifyProto proto xs
    let output = outputName (last mutateChain)
    let params = primProtoParams proto'
    let params' = map (\param@PrimParam{primParamName = name, primParamFlow=flow } ->
            if name /= output then
                param
            else case flow of
                FlowOutByReference -> shouldnt "multiple mutate chains writing to same output"
                FlowTakeReference -> shouldnt "takeReference arg should only appear as the last argument to a mutate() instruction"
                FlowIn -> shouldnt $ "attempting to convert FlowIn -> FlowOutByReference.\nproto: " ++ show proto ++ "\nmutate chain: " ++ show mutateChain
                -- XXX: change name of param too?
                FlowOut -> param { primParamFlow = FlowOutByReference }
            ) params
    return proto' { primProtoParams = params' }

-- Instead of a series of mutates *after* the last call, we instead
-- perform some extra setup *before* the last call, allowing the last call
-- of this block to be in tail-position.
buildTailCallLeaf :: [Placed Prim] -> Placed Prim -> [MutateChain] -> Compiler [Placed Prim]
buildTailCallLeaf beforeCall call mutateChains = do
    let modifiedMutates = concatMap annotateFinalMutates mutateChains
    let call' = contentApply (transformIntoTailCall mutateChains) call
    return $ beforeCall ++ [call'] ++ modifiedMutates


annotateFinalMutates :: MutateChain -> [Placed Prim]
annotateFinalMutates = map $
    contentApply (\case {
            PrimForeign "lpvm" "mutate" [] [input, output, offset, destructive, size, startOffset, val] -> PrimForeign "lpvm" "mutate" [] [input, output, offset, destructive, size, startOffset, setArgFlow FlowTakeReference val ];
            _ -> shouldnt "must be mutate instr"
    }) . prim

transformIntoTailCall :: [MutateChain] -> Prim -> Prim
transformIntoTailCall mutateChains (PrimCall siteId spec args globalFlows attrs) =
    let mutates = concat mutateChains in
    PrimCall siteId spec (map (\arg ->
        case arg of
            var@ArgVar { argVarName = name } | name `elem` List.map valueName mutates
                -> var { argVarFlow = FlowOutByReference }
            _ -> arg
        ) args) globalFlows (Set.insert Tail attrs)
transformIntoTailCall mutateChains _ = shouldnt "not a call"

data MovePrimsResult = MovePrimsResult {
    succeeded :: [Placed Prim],
    -- TODO: `remaining` should just be [Prim]
    remaining :: [Placed Prim]
}

data MutateInstr = MutateInstr {
    prim      :: Placed Prim,
    inputName :: PrimVarName,
    inputType :: TypeSpec,
    outputName :: PrimVarName,
    outputType :: TypeSpec,
    valueName :: PrimVarName,
    valueType :: TypeSpec,
    offsetArg :: PrimArg
} deriving(Show)

type MutateChain = [MutateInstr]
type LastCall = Prim

tryMovePrimsBeforeLastCall :: LastCall -> [Placed Prim] -> MovePrimsResult -> MovePrimsResult
tryMovePrimsBeforeLastCall lastCall [] state = state
tryMovePrimsBeforeLastCall lastCall (prim:nextPrims) state = if primUsesOutputsOfOtherPrims (content prim) (lastCall : List.map content (remaining state) ++ List.map content nextPrims)
    then tryMovePrimsBeforeLastCall lastCall nextPrims state { remaining = prim : remaining state }
    else tryMovePrimsBeforeLastCall lastCall nextPrims state { succeeded = prim : succeeded state }

analyzePrimAfterLastCall :: LastCall -> Placed Prim -> [MutateChain] -> Either String [MutateChain]
analyzePrimAfterLastCall lastCall prim state = case content prim of
    PrimForeign "lpvm" "mutate" _ mutateInstr@[
        ArgVar { argVarName = inputName, argVarType = inputType, argVarFlow = FlowIn },
        ArgVar { argVarName = outputName, argVarType = outputType, argVarFlow = FlowOut },
        offsetArg,
        ArgInt 1 _,
        _,
        _,
        ArgVar { argVarName = valueName, argVarFlow = FlowIn, argVarType = valueType, argVarFinal = final }]
      | valueName `elem` varsInPrim FlowOut lastCall -> if not final
          then Left $ show valueName ++ " is used in more than one place"
          else tryAddToMutateChain lastCall state MutateInstr { prim = prim, inputName = inputName, inputType = inputType, outputName = outputName, outputType = outputType, offsetArg = offsetArg, valueName = valueName, valueType = valueType } state
    prim -> Left $ "not a mutate instr which uses a value from lastCall where destructive=1 and start_offset=0, offset, size const int:\n" ++ show prim

-- Alternative plan?:
-- run down rest of the list, sequentially grabbing any mutate of the output produced by first mutate?
-- skip over: collect in "residue"
-- when you're done, take the residue, and do the same thing

-- If there's any residue then abort.

tryAddToMutateChain :: LastCall -> [MutateChain] -> MutateInstr -> [MutateChain] -> Either String [MutateChain]
tryAddToMutateChain lastCall chains0 mut1 (chain@(mut:muts):chains) =
    if outputName mut == inputName mut1
        then return $ (mut1:chain):chains
        else do
            chains' <- tryAddToMutateChain lastCall chains0 mut1 chains
            return $ chain:chains'
tryAddToMutateChain lastCall chains0 mut' [] = let inputArg = inputName mut' in
    if inputArg `elem` varsInPrim FlowOut lastCall || any ((==inputArg) . outputName) (concat chains0)
    then
        Left "Input arg is either generated by the last call, or by reusing an intermediate output from an existing mutate-chain."
    else
        Right [[mut']]
tryAddToMutateChain _ _ _ ([]:_) = Left "a mutate chain shouldnt be empty"

partitionLastCall :: [Placed Prim] -> (Maybe ([Placed Prim], Placed Prim), [Placed Prim])
partitionLastCall prims = let (lastCall, after) = _partitionLastCall $ reverse prims
    in (lastCall, reverse after)

_partitionLastCall :: [Placed Prim] -> (Maybe ([Placed Prim], Placed Prim), [Placed Prim])
_partitionLastCall [] = (Nothing, [])
_partitionLastCall (x:xs) =
    case content x of
        PrimCall {} -> (Just (reverse xs, x), [])
        _ -> let (lastCall, afterLastCall) = _partitionLastCall xs
            in (lastCall, x:afterLastCall)

-- Applies a transformation to the leaves of a proc body
-- TODO: this is almost like a functor fmap?
mapProcLeavesM :: (Monad t) => ([Placed Prim] -> t [Placed Prim]) -> ProcBody -> t ProcBody
mapProcLeavesM f leafBlock@ProcBody { bodyPrims = prims, bodyFork = NoFork } =
    do
        prims <- f prims
        return leafBlock { bodyPrims = prims }
mapProcLeavesM f current@ProcBody { bodyFork = fork@PrimFork{forkBodies = bodies} } =
    do
        bodies' <- mapM (mapProcLeavesM f) bodies
        return current { bodyFork = fork { forkBodies = bodies' } }

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
