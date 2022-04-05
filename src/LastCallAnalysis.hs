--  File     : LastCallAnalysis.hs
--  Author   : Chris Chamberlain
--  Purpose  : Transform proc bodies and their output arguments so that
--             more recursive algorithms can be tail-call optimised.
--  Copyright: (c) 2015-2022 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module LastCallAnalysis (lastCallAnalyseMod, lastCallAnalyseProc) where
import AST
import qualified Data.List as List
import qualified UnivSet
import Options (LogSelection(LastCallAnalysis))
import Util (sccElts)
import Data.Foldable (foldrM)
import Data.List.Predicate (allUnique)
import Callers (getSccProcs)
import Data.Graph (SCC (AcyclicSCC, CyclicSCC))
import Control.Monad.State (StateT (runStateT), MonadTrans (lift), execStateT, execState, runState, MonadState (get, put), gets, modify, unless)
import Control.Monad (liftM)
import Data.Set (Set)

lastCallAnalyseMod :: ModSpec -> Compiler ()
lastCallAnalyseMod thisMod = do
    reenterModule thisMod

    -- TODO: run this on specialized versions as well:
    orderedProcs <- getSccProcs thisMod

    -- Some logging
    logLastCallAnalysis $ replicate 60 '='
    logLastCallAnalysis $ "analyseMod:" ++ show thisMod
    logLastCallAnalysis $ ">>> orderedProcs:" ++ show orderedProcs
    logLastCallAnalysis $ ">>> Analyse SCCs: \n" ++
        unlines (List.map ((++) "    " . show . sccElts) orderedProcs)
    logLastCallAnalysis $ replicate 60 '='

    mapM_ lastCallAnalyseSCC orderedProcs

    reexitModule

lastCallAnalyseSCC :: SCC ProcSpec -> Compiler ()
lastCallAnalyseSCC (AcyclicSCC proc) = lastCallAnalyseProcSpec proc
lastCallAnalyseSCC (CyclicSCC procs) = mapM_ lastCallAnalyseProcSpec procs

lastCallAnalyseProcSpec :: ProcSpec -> Compiler ()
lastCallAnalyseProcSpec pspec = do
    updateProcDefM (lastCallAnalyseProc pspec) pspec
    return ()

lastCallAnalyseProc :: ProcSpec -> ProcDef -> Compiler ProcDef
lastCallAnalyseProc spec def = do
    logLastCallAnalysis $ "\n>>> Last Call Analysis: " ++ show spec
    let impln = procImpln def
    res <- tryMakeTailCall spec (procImplnProto impln) (procImplnBody impln)
    case res of
        Just (proto', body') -> return def {procImpln = impln{procImplnProto = proto', procImplnBody = body'}}
        Nothing -> return def

isDirectRecursiveCall :: Prim -> ProcSpec -> Bool
isDirectRecursiveCall (PrimCall _ spec' _ _) spec = True
isDirectRecursiveCall _ _ = False

data LeafTransformState = LeafTransformState {
    procSpec :: ProcSpec,
    originalProto :: PrimProto,
    transformedProto :: Maybe PrimProto,
    protoConflict :: Bool
}

type LeafTransformer = StateT LeafTransformState Compiler

tryMakeTailCall :: ProcSpec -> PrimProto -> ProcBody -> Compiler (Maybe (PrimProto, ProcBody))
tryMakeTailCall spec proto body = do
    -- We map over the leaves the proc twice. First we identify the leaves
    -- where can move the last call -> tail call.

    (body', finalState) <- runStateT
            (mapProcLeaves transformLeaf body)
            LeafTransformState { procSpec = spec, originalProto = proto, transformedProto = Nothing, protoConflict = False }

    case (protoConflict finalState, transformedProto finalState) of
        (False, Just proto') -> do
            -- Then we map over leaves a second time, inserting
            -- `foreign lpvm store()` calls for all FlowOutByReference args
            logLastCallAnalysis "inserting missing store() calls for out-by-reference args"
            body'' <- mapProcLeaves (assignReferenceOutputs proto proto') body'

            -- Return modified result
            return $ Just (proto', body'')
        _ -> return Nothing

transformLeaf :: [Placed Prim] -> LeafTransformer [Placed Prim]
transformLeaf lastBlock = do
    spec <- gets procSpec
    case partitionLastCall lastBlock of
        -- TODO: use multiple specialization to relax the restriction that
        -- the last call is a directly-recursive call...
        (Just (beforeCall, call), afterLastCall@(_:_)) | isDirectRecursiveCall (content call) spec -> do
            let lastCall = content call
            logLeaf $ "identified a directly-recursive last-call: " ++ show call
            logLeaf $ "before: " ++ show beforeCall ++ "\nafter: " ++ show afterLastCall
            -- First we identify all the prims which can be trivially moved before the last call
            -- i.e.: the prim doesn't depend on any values produced by the last call (or subsequent prims)
            logLeaf $ "moving prims before last call where possible"
            let MovePrimsResult { remaining = remainingAfterLastCall, succeeded = movedBeforeLastCall } = tryMovePrimsBeforeLastCall lastCall afterLastCall MovePrimsResult { remaining = [], succeeded = [] }
            logLeaf $ "still remaining after last call: " ++ show (reverse remainingAfterLastCall)
            -- Next, we look at the remaining prims which couldn't be simply moved before the last call,
            -- to see if they are just "filling in the fields" of struct(s) with outputs from the last call.
            case foldrM (analyzePrimAfterLastCall (content call)) [] (reverse (List.map content remainingAfterLastCall)) of
                Right mutateChains -> do
                    -- Finally, we check that writes in a single "mutate-chain" don't alias fields.
                    -- This could be bad, since we cannot guarantee that the called proc will write to fields in any particular order.
                    -- In this case, we apply a transformation to make the call the final prim in the proc.
                    --
                    -- XXX: take into account size as well as offset when determining aliasing?
                    if all (allUnique . List.map (trustArgInt . offsetArg)) mutateChains
                    then do
                        proto <- gets originalProto
                        proto' <- gets transformedProto
                        proto'' <- lift $ modifyProto proto mutateChains
                        case proto' of
                            Just proto' | proto' /= proto'' -> do
                                logLeaf $ "conflicting protos" ++ show proto' ++ "\n" ++ show proto''
                                modify (\state -> state { protoConflict = True })
                                return lastBlock
                            _ -> do
                                modify (\state -> state { transformedProto = Just proto'' })
                                logLeaf $ "remaining prims meet requirements for last call -> tail call transform\nmutate chains: " ++ show mutateChains
                                logLeaf $ "modified proto: " ++ show proto''
                                body' <- lift $ buildTailCallLeaf (beforeCall ++ reverse movedBeforeLastCall) call mutateChains
                                logLeaf $ "modified leaf: " ++ show body'
                                return body'
                    else do
                        logLeaf "mutate instructions alias! aborting"
                        return lastBlock
                Left error -> do
                    logLeaf $ "remaining prims didn't satisfy constraints: " ++ error
                    return lastBlock
        _ -> do
            logLeaf "leaf didn't qualify for last-call transformation"
            return lastBlock

paramUnassigned :: Set PrimVarName -> PrimParam -> Bool
paramUnassigned outputs param =
    primParamName param `notElem` outputs


assignReferenceOutputs :: PrimProto -> PrimProto -> [Placed Prim] -> Compiler [Placed Prim]
assignReferenceOutputs proto proto' leaf = do
    let leafPrims = map content leaf
    let potentialArgs = varsInPrims FlowIn leafPrims
    let outByRefParams = filter (paramUnassigned potentialArgs) $ filter ((==FlowOutByReference ) . primParamFlow) $ primProtoParams proto'
    -- find the original param names / types before the transformation
    let outByRefParams' = map (\param -> (primProtoParams proto !! parameterVarNameToID proto' (primParamName param), param)) outByRefParams
    logLastCallAnalysis $ "leaf: " ++ show leaf ++ "\nassigning by reference outputs: " ++ show outByRefParams'
    let inits = map (\(PrimParam name ty _ _ _, _) -> initializeOutput name name ty) outByRefParams'
    return $ leaf ++ inits

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
    let params' = map (\param@PrimParam{primParamName = name, primParamFlow=flow, primParamType=ty} ->
            if name /= output then
                param
            else case flow of
                FlowOutByReference -> shouldnt "multiple mutate chains writing to same output"
                FlowIn -> shouldnt $ "attempting to convert FlowIn -> FlowOutByReference.\nproto: " ++ show proto ++ "\nmutate chain: " ++ show mutateChain
                -- XXX: change name of param too?
                FlowOut -> param { primParamName = addSuffix name outByRefSuffix, primParamFlow = FlowOutByReference, primParamType = Pointer ty }
            ) params
    return proto' { primProtoParams = params' }

-- Instead of a series of mutates *after* the last call, we instead
-- perform some extra setup *before* the last call, allowing the last call
-- of this block to be in tail-position.
buildTailCallLeaf :: [Placed Prim] -> Placed Prim -> [MutateChain] -> Compiler [Placed Prim]
buildTailCallLeaf beforeCall call mutateChains = do
    inits <- mapM initializeOutputFromChain mutateChains
    let addresses = computeArgumentAddresses mutateChains
    let call' = modifyCall mutateChains call
    return $ beforeCall ++ inits ++ addresses ++ [call']

initializeOutputFromChain :: MutateChain -> Compiler (Placed Prim)
initializeOutputFromChain mutateChain = do
    let outputTy = outputType $ last mutateChain
    let inputTy = inputType $ head mutateChain
    unless (outputTy == inputTy) (logLastCallAnalysis $ "WARNING: types of head and tail of mutate chain differ: " ++ show inputTy ++ " vs. " ++ show outputTy)
    return $ initializeOutput (inputName $ head mutateChain) (outputName $ last mutateChain) outputTy

initializeOutput :: PrimVarName -> PrimVarName -> TypeSpec -> Placed Prim
initializeOutput input output ty =
    Unplaced $ PrimForeign "lpvm" "store" [] [
        ArgVar input ty FlowIn Ordinary False,
        ArgVar (addSuffix output outByRefSuffix) (Pointer ty) FlowIn Ordinary True
    ]

addressSuffix :: [Char]
addressSuffix = "address"


outByRefSuffix :: [Char]
outByRefSuffix = "outByRef"


addSuffix :: PrimVarName -> String -> PrimVarName
addSuffix varName suffix = varName { primVarName = primVarName varName ++ [specialChar] ++ suffix }


computeArgumentAddresses :: [MutateChain] -> [Placed Prim]
computeArgumentAddresses = concatMap (\mutateChain ->
    map (\mutate ->
            let valueVar = valueName mutate in
            Unplaced $ PrimForeign "lpvm" "address" [] [
                ArgVar {
                    argVarName = inputName $ head mutateChain,
                    argVarType = inputType $ head mutateChain,
                    argVarFlow = FlowIn,
                    argVarFlowType = Ordinary,
                    argVarFinal = False
                },
                offsetArg mutate,
                sizeArg mutate,
                startOffsetArg mutate,
                ArgVar {
                    argVarName = addSuffix valueVar addressSuffix,
                    argVarType = Pointer $ valueType mutate,
                    argVarFlow = FlowOut,
                    argVarFlowType = Ordinary,
                    argVarFinal = False
                }
            ]
        ) mutateChain
    )

modifyCall :: [MutateChain] -> Placed Prim -> Placed Prim
modifyCall mutateChains = contentApply (\call -> case call of
        PrimCall siteId spec args globalFlows ->
            let mutates = concat mutateChains in
            PrimCall siteId spec (map (\arg ->
                case arg of
                    var@ArgVar { argVarName = name, argVarType = ty } | name `elem` List.map valueName mutates
                        -> var { argVarName = addSuffix name addressSuffix, argVarType = Pointer ty, argVarFlow = FlowOutByReference }
                    _ -> arg
                ) args) globalFlows
        _ -> call
    )

data MovePrimsResult = MovePrimsResult {
    succeeded :: [Placed Prim],
    -- TODO: `remaining` should just be [Prim]
    remaining :: [Placed Prim]
}

data MutateInstr = MutateInstr {
    inputName :: PrimVarName,
    inputType :: TypeSpec,
    outputName :: PrimVarName,
    outputType :: TypeSpec,
    valueName :: PrimVarName,
    valueType :: TypeSpec,
    offsetArg :: PrimArg,
    sizeArg :: PrimArg,
    startOffsetArg :: PrimArg
} deriving(Show)

type MutateChain = [MutateInstr]
type LastCall = Prim

tryMovePrimsBeforeLastCall :: LastCall -> [Placed Prim] -> MovePrimsResult -> MovePrimsResult
tryMovePrimsBeforeLastCall lastCall [] state = state
tryMovePrimsBeforeLastCall lastCall (prim:nextPrims) state = if primUsesOutputsOfOtherPrims (content prim) (lastCall : List.map content (remaining state) ++ List.map content nextPrims)
    then tryMovePrimsBeforeLastCall lastCall nextPrims state { remaining = prim : remaining state }
    else tryMovePrimsBeforeLastCall lastCall nextPrims state { succeeded = prim : succeeded state }

analyzePrimAfterLastCall :: LastCall -> Prim -> [MutateChain] -> Either String [MutateChain]
analyzePrimAfterLastCall lastCall prim state = case prim of
    PrimForeign "lpvm" "mutate" _ mutateInstr@[
        ArgVar { argVarName = inputName, argVarType = inputType, argVarFlow = FlowIn },
        ArgVar { argVarName = outputName, argVarType = outputType, argVarFlow = FlowOut },
        offsetArg,
        ArgInt 1 _,
        sizeArg,
        startOffsetArg,
        ArgVar { argVarName = valueName, argVarFlow = FlowIn, argVarType = valueType, argVarFinal = final }]
      | valueName `elem` varsInPrim FlowOut lastCall -> if not final
          then Left $ show valueName ++ " is used in more than one place"
          else tryAddToMutateChain lastCall state MutateInstr { inputName = inputName, inputType = inputType, outputName = outputName, outputType = outputType, offsetArg = offsetArg, sizeArg = sizeArg, startOffsetArg = startOffsetArg, valueName = valueName, valueType = valueType } state
    prim -> Left $ "not a mutate instr which uses a value from lastCall where destructive=0 and start_offset=0, offset, size const int:\n" ++ show prim

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
mapProcLeaves :: (Monad t) => ([Placed Prim] -> t [Placed Prim]) -> ProcBody -> t ProcBody
mapProcLeaves f leafBlock@ProcBody { bodyPrims = prims, bodyFork = NoFork } =
    do
        prims <- f prims
        return leafBlock { bodyPrims = prims }
mapProcLeaves f current@ProcBody { bodyFork = fork@PrimFork{forkBodies = bodies} } =
    do
        bodies' <- mapM (mapProcLeaves f) bodies
        return current { bodyFork = fork { forkBodies = bodies' } }

----------------------------------------------------------------------------
-- Logging                                                                --
----------------------------------------------------------------------------

-- | Logging from the Compiler monad to LastCallAnalysis.
logLastCallAnalysis :: String -> Compiler ()
logLastCallAnalysis = logMsg LastCallAnalysis

-- | Logging from the Compiler monad to LastCallAnalysis.
logLeaf :: String -> LeafTransformer ()
logLeaf s = lift $ logMsg LastCallAnalysis s