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
import Options (LogSelection(LastCallAnalysis),
                optimisationEnabled, OptFlag(TailCallModCons))
import Util (sccElts, lift2)
import Data.Foldable (foldrM)
import Data.List.Predicate (allUnique)
import Callers (getSccProcs)
import Data.Graph (SCC (AcyclicSCC, CyclicSCC))
import Control.Monad.State (StateT (runStateT), MonadTrans (lift), execStateT, execState, runState, MonadState (get, put), gets, modify)
import Control.Monad ( liftM, (>=>), when, unless, MonadPlus (mzero) )
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))


-- BEGIN MAJOR DOC
-- 
-- # Last Call Optimisation
-- 
-- The compiler relies on the LLVM compiler to perform last call optimisation,
-- turning the last call in a procedure body into a jump, if no other
-- instructions follow the last call.  This module tries to increase the number
-- of procedures where this optimisation applies by moving code that follows the
-- last call before it, whenever all the inputs to those instructions are
-- available before the last call.
-- 
-- One particular trick employed to make this possible is
-- last-call-module-construction optimisation.  The idea here is to invert the
-- direction of data flow, turing an output into an input, by passing in the
-- address to which to write the output.  When the instruction following the
-- last call in a body simply writes an output of that call into one memory
-- location, without using it in any other way, and when the called procedure is
-- defined in the module currently being compiled (so we can transform it), we
-- can change that output argument into a pointer input, and modify the
-- procedure definition to write the output value to memory through that
-- pointer.  This is done by changing that parameter from FlowOut to
-- FlowOutByReference, and similarly changing the corresponding argument in all
-- calls to that procedure.  Likewise, we change the instruction intended to
-- write the procedure output to memory from FlowIn to FlowTakeReference.
-- 
-- Note that this transformation leaves the call that notionally produces the
-- output before the instruction that notionally writes the value to memory,
-- despite the fact that now the latter actually takes the address to be written
-- to, and the former actually passes that address into a procedure call.
-- Therefore, when the LLVM code is actually generated, the procedure call must
-- be deferred until after the address is taken.  This is performed by the LLVM
-- module.
--
-- END MAJOR DOC




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
    -- we need to fixup calls regardless whether tcmc is enabled or not,
    -- as there could be modified calls to e.g.: standard library functions
    mapM_ (updateEachProcM fixupCallsInProc) orderedProcs
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
                LeafTransformState { procSpec = spec, originalProto = proto, transformedProto = Nothing }
            case (maybeBody', transformedProto finalState) of
                (Just body', Just proto') -> do
                    logLastCallAnalysis $ "new proto: " ++ show proto'
                    return def {procImpln = impln{procImplnProto = proto', procImplnBody = body'}}
                _ -> return def

data LeafTransformState = LeafTransformState {
    procSpec :: ProcSpec,
    originalProto :: PrimProto,
    transformedProto :: Maybe PrimProto
}

type LeafTransformer = MaybeT (StateT LeafTransformState Compiler)

-- | Run our analysis on a single leaf of the function body,
-- collecting state inside the LeafTransformer monad.
transformLeaf :: [Placed Prim] -> LeafTransformer [Placed Prim]
transformLeaf lastBlock = do
    spec <- gets procSpec
    case partitionLastCall lastBlock of
        -- TODO: use multiple specialization to relax the restriction that
        --       the last call is a directly-recursive call...
        (Just (beforeCall, lastCall), afterLastCall@(_:_)) | primIsCallToProcSpec lastCall spec -> do
            logLeaf $ "identified a directly-recursive last-call: " ++ show lastCall
            logLeaf $ "before: " ++ show beforeCall ++ "\nafter: " ++ show afterLastCall
            -- First we identify all the prims which can be trivially moved before the last call
            -- i.e.: the prim doesn't depend on any values produced by the last call (or subsequent prims)
            let moveResult = tryMovePrimsBeforeLastCall lastCall afterLastCall MovePrimsResult { remaining = [], succeeded = [] }
            let remainingAfterLastCall = reverse $ remaining moveResult
            let movedBeforeLastCall = reverse $ succeeded moveResult
            logLeaf $ "prims still remaining after last call: " ++ show remainingAfterLastCall
            -- Next, we look at the remaining prims which couldn't be simply moved before the last call,
            -- to see if they are just "filling in the fields" of struct(s) with outputs from the last call.
            case foldrM (analyzePrimAfterLastCall lastCall) [] remainingAfterLastCall of
                Right mutateChains -> do
                    proto <- gets originalProto
                    proto'' <- lift2 $ modifyProto proto mutateChains
                    -- attempts to modify this proc's proto.
                    -- will abort if we already tried to modify it
                    -- incompatibly in a different leaf.
                    trySetProto proto''

                    -- We apply the transformation to mark the final call as
                    -- a `tail` call
                    body' <- lift2 $ buildTailCallLeaf (beforeCall ++ movedBeforeLastCall) lastCall mutateChains

                    logLeaf "remaining prims meet requirements tail call transformation"
                    logLeaf $ "identified mutate chains: " ++ show mutateChains
                    logLeaf $ "modified proto: " ++ show proto''
                    logLeaf $ "modified body: " ++ show body'
                    return body'
                Left error -> do
                    logLeaf $ "remaining prims didn't satisfy constraints: " ++ error
                    return lastBlock
        (Just (_, call), []) | primIsCallToProcSpec call spec -> do
            logLeaf "directly-recursive last call is already in tail position"
            logLeaf "in the future, we will mark this call with the LPVM `tail` attribute"
            logLeaf "to ensure it gets tail-call-optimised by LLVM"
            return lastBlock
        _ -> do
            logLeaf "leaf didn't qualify for last-call transformation"
            return lastBlock

-- Returns true if this prim is calling proc spec
primIsCallToProcSpec :: Placed Prim -> ProcSpec -> Bool
primIsCallToProcSpec p spec = case content p of
    (PrimCall _ spec' _ _ _) | spec == spec' -> True
    _ -> False

-- | We don't want two different leaves to each try to update the proc's
-- proto to something incompatible. Afterall, there is only a single proto for
-- the proc, so all leaves must agree on a compatible definition.
--
-- XXX: could probably take the union of all `outByReference` parameters,
--      in the case of multiple branches wanting to modify the proc.
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

-- | Returns true if `prim` uses any of the outputs generated by `otherPrims`
-- If this is the case, then it is not possible to move `prim` before the last call.
primUsesOutputsOfOtherPrims :: Placed Prim -> [Placed Prim] -> Bool
primUsesOutputsOfOtherPrims p ps =
    let prim = content p
        otherPrims = List.map content ps
        (args, gFlows) = primArgs prim
        vars = varsInPrimArgs FlowIn args
        otherPrimOutputs = varsInPrims FlowOut otherPrims
    in
    -- if the prim refers to any global variables, then skip reordering (conservative approximation for now)
    -- otherwise, check it doesn't refer to any outputs from `otherPrims`
    (gFlows /= emptyGlobalFlows) || any (`elem` otherPrimOutputs) vars

-- | Finds outputs which are the final result of a mutate chain
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

-- | Instead of a series of mutates *after* the last call, we instead
-- perform some extra setup *before* the last call, allowing the last call
-- of this block to be in tail-position.
buildTailCallLeaf :: [Placed Prim] -> Placed Prim -> [MutateChain] -> Compiler [Placed Prim]
buildTailCallLeaf beforeCall call mutateChains = do
    let modifiedMutates = concatMap annotateFinalMutates mutateChains
    let call' = contentApply (transformIntoTailCall mutateChains) call
    return $ beforeCall ++ [call'] ++ modifiedMutates

-- | Annotates mutates which remain after the tail call with FlowTakeReference
-- This indicates that the mutation will not actually occur after the call,
-- instead, we take a reference to the memory location the mutate would have
-- written to, and pass that reference into the tail call as an `outByReference`
-- parameter.
annotateFinalMutates :: MutateChain -> [Placed Prim]
annotateFinalMutates = map $
    contentApply (\case {
            PrimForeign "lpvm" "mutate" [] [input, output, offset, destructive, size, startOffset, val] ->
                PrimForeign "lpvm" "mutate" [] [input, output, offset, destructive, size, startOffset, setArgFlow FlowTakeReference val ];
            _ -> shouldnt "must be mutate instr"
    }) . prim

-- | Given a set of mutate chains (which are linear sequences of mutations
-- occuring after the call), decorate this call with appropriate
-- `outByReference` args.
transformIntoTailCall :: [MutateChain] -> Prim -> Prim
transformIntoTailCall mutateChains
                      (PrimCall siteId spec impurity args globalFlows) =
    let mutates = concat mutateChains in
    PrimCall siteId spec impurity (map (\arg ->
        case arg of
            var@ArgVar { argVarName = name } | name `elem` List.map valueName mutates
                -> var { argVarFlow = FlowOutByReference }
            _ -> arg
        ) args) globalFlows
transformIntoTailCall mutateChains _ = shouldnt "not a call"

data MovePrimsResult = MovePrimsResult {
    succeeded :: [Placed Prim],
    remaining :: [Placed Prim]
}

data MutateInstr = MutateInstr {
    prim      :: Placed Prim,
    inputName :: PrimVarName,
    outputName :: PrimVarName,
    valueName :: PrimVarName,
    offset :: Integer
} deriving(Show)

type MutateChain = [MutateInstr]
type LastCall = Placed Prim

tryMovePrimsBeforeLastCall :: LastCall -> [Placed Prim] -> MovePrimsResult -> MovePrimsResult
tryMovePrimsBeforeLastCall lastCall [] state = state
tryMovePrimsBeforeLastCall lastCall (prim:nextPrims) state = if primUsesOutputsOfOtherPrims prim (lastCall : remaining state ++ nextPrims)
    then tryMovePrimsBeforeLastCall lastCall nextPrims state { remaining = prim : remaining state }
    else tryMovePrimsBeforeLastCall lastCall nextPrims state { succeeded = prim : succeeded state }

-- | The only prims allowed after a "would-be tail call" are `foreign lpvm mutate`
-- instructions, which specific conditions (i.e.: the fields they are writing
-- into don't alias)
analyzePrimAfterLastCall :: LastCall -> Placed Prim -> [MutateChain] -> Either String [MutateChain]
analyzePrimAfterLastCall lastCall prim state = case content prim of
    PrimForeign "lpvm" "mutate" _ mutateInstr@[
        ArgVar { argVarName = inputName, argVarFlow = FlowIn },
        ArgVar { argVarName = outputName, argVarFlow = FlowOut },
        offsetArg,
        ArgInt 1 _,
        _,
        _,
        ArgVar { argVarName = valueName, argVarFlow = FlowIn, argVarFinal = final }]
      | valueName `elem` varsInPrim FlowOut (content lastCall) -> if not final
          then Left $ show valueName ++ " is used in more than one place"
          else tryAddToMutateChain lastCall state MutateInstr { prim = prim, inputName = inputName, outputName = outputName, offset = trustArgInt offsetArg, valueName = valueName } state
    prim -> Left "not a mutate instr or doesn't satisfy constraints"

-- | We build up these "mutate-chains" incrementally, aborting early if
-- the conditions aren't satisfied.
-- This analysis makes sure that mutations for (zero or more) linear sequences
-- where each mutate in a sequence writes to a non-overlapping field.
tryAddToMutateChain :: LastCall -> [MutateChain] -> MutateInstr -> [MutateChain] -> Either String [MutateChain]
tryAddToMutateChain lastCall chains0 mut1 (chain@(mut:muts):chains) =
    if outputName mut == inputName mut1
        -- We check that writes in a single mutate-chain don't alias fields.
        -- Aliasing could be bad, since we cannot guarantee that the
        -- callee will write it's outByReference arguments in any particular order.
        --
        -- XXX: take into account size as well as offset when determining aliasing?
        then if offset mut `notElem` List.map offset chain then
                Right $ (mut1:chain):chains
            else Left "offsets alias"
        else do
            chains' <- tryAddToMutateChain lastCall chains0 mut1 chains
            return $ chain:chains'
tryAddToMutateChain lastCall chains0 mut' [] = let inputArg = inputName mut' in
    if inputArg `elem` varsInPrim FlowOut (content lastCall)
            || any (any ((==inputArg) . outputName)) chains0
    then
        Left "Input arg is either generated by the last call, or by reusing an intermediate output from an existing mutate-chain."
    else
        Right [[mut']]
tryAddToMutateChain _ _ _ ([]:_) = Left "a mutate chain shouldnt be empty"

----------------------------------------------------------------------------
-- Coerce FlowOut into FlowOutByReference                                 --
----------------------------------------------------------------------------

-- | Check the proc protos of all callees, and coerce FlowOut into
-- FlowOutByReference where needed.
fixupCallsInProc :: ProcDef -> Compiler ProcDef
fixupCallsInProc def@ProcDef { procImpln = impln@ProcDefPrim { procImplnBody = body}} = do
    logLastCallAnalysis $ ">>> Fix up calls in proc: " ++ show (procName def)
    body' <- mapProcPrimsM (updatePlacedM fixupCallsInPrim) body
    return $ def { procImpln = impln { procImplnBody = body' } }
fixupCallsInProc _ = shouldnt "uncompiled"

fixupCallsInPrim :: Prim -> Compiler Prim
fixupCallsInPrim p@(PrimCall siteId pspec impurity args gFlows) = do
    logLastCallAnalysis $ "checking call " ++ show p
    proto <- getProcPrimProto pspec
    let args' = coerceArgs args (primProtoParams proto)
    when (args /= args') $ logLastCallAnalysis $ "coerced args: " ++ show args ++ " " ++ show args'
    return $ PrimCall siteId pspec impurity args' gFlows
fixupCallsInPrim p = return p

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
        -- XXX must map over default, too
        bodies' <- mapM (mapProcLeavesM f) bodies
        return current { bodyFork = fork { forkBodies = bodies' } }

-- | Applies a transformation to each prim in a proc
mapProcPrimsM :: (Monad t) => (Placed Prim -> t (Placed Prim)) -> ProcBody -> t ProcBody
mapProcPrimsM fn body@ProcBody { bodyPrims = prims, bodyFork = NoFork } = do
        prims' <- mapM fn prims
        return body { bodyPrims = prims' }
mapProcPrimsM fn body@ProcBody { bodyPrims = prims, bodyFork = fork@PrimFork{forkBodies = bodies } } = do
        -- XXX must map over default, too
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
