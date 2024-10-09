--  File     : AliasAnalysis.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE LambdaCase #-}

module AliasAnalysis (
    AliasMapLocal, AliasMapLocalItem(..), aliasSccBottomUp, currentAliasInfo,
    isAliasInfoChanged, updateAliasedByPrim, isArgUnaliased,
    isArgVarUsedOnceInArgs, DeadCells, updateDeadCellsByAccessArgs,
    assignDeadCellsByAllocArgs
    ) where

import           AST
import           Control.Monad
import           Data.Graph
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Data.Maybe    as Maybe
import           Data.Tuple.Extra
import           Flow          ((|>))
import           Options       (LogSelection (Analysis))
import           Util
import           Config        (specialName2)


-- This "AliasMapLocal" is used during analysis and it will be converted to
-- "AliasMap" (defined in "AST.hs") and stored in LPVM module.
-- The "AliasMap" records the relation between parameters of each procedure.
-- The "AliasMapLocal" records all variables during the analysis. "LiveVar" is
-- for variables, it can be added to and removed from the map during analysis.
-- For parameters, we consider it's a normal variable ("LiveVar") aliased with
-- something outside the procedure scope ("AliasByParam" / "MaybeAliasByParam").
-- "AliasByParam" and "MaybeAliasByParam" won't be removed during the analysis,
-- but if the existence of a "MaybeAliasByParam" can change the outcome then we
-- consider the corresponding parameter as interesting.
data AliasMapLocalItem
    = LiveVar           PrimVarName
    | AliasByGlobal     GlobalInfo
    | AliasByParam      PrimVarName
    | MaybeAliasByParam PrimVarName
    deriving (Eq, Ord, Show)

type AliasMapLocal = DisjointSet AliasMapLocalItem


-- For each size, record all reusable cells, more on this can be found under
-- the "Dead Memory Cell Analysis" section below.
-- Each reusable cell is recorded as "((var, startOffset), requiredParams)".
-- "var" is the variable (copy from it's last access) that can be reused
-- and requiredParams is a list of parameters that need to be non-aliased
-- before reusing that cell (caused by "MaybeAliasByParam").
type DeadCells = Map Int [((PrimArg, PrimArg), [PrimVarName])]


-- Intermediate data structure used during the analysis
type AnalysisInfo =
    (AliasMapLocal, Set InterestingCallProperty, MultiSpeczDepInfo, DeadCells)


aliasSccBottomUp :: SCC ProcSpec -> Compiler ()
aliasSccBottomUp (AcyclicSCC single) = do
    _ <- aliasProcBottomUp single -- immediate fixpoint if no mutual dependency
    return ()
-- | Gather all flags (indicating if any proc alias information changed or not)
--     by comparing transitive closure of the (key, value) pairs of the map;
--     Only cyclic procs need to reach a fixed point; False means alias info not
--     changed, so that a fixed point is reached.
aliasSccBottomUp procs@(CyclicSCC multi) = do
    changed <- mapM aliasProcBottomUp multi

    logAlias $ replicate 50 '>'
    logAlias $ "Check aliasing for CyclicSCC procs: " ++ show procs
    logAlias $ "Changes: " ++ show changed
    logAlias $ "Proc level alias changed? " ++ show (or changed)
    logAlias $ replicate 50 '>'

    -- Aliasing is always changed after the first run, so cyclic procs are
    -- analysed at least twice.
    when (or changed) $ aliasSccBottomUp procs


currentAliasInfo :: SCC ProcSpec
        -> Compiler [(AliasMap, Set InterestingCallProperty)]
currentAliasInfo (AcyclicSCC single) = do
    def <- getProcDef single
    let ProcDefPrim{procImplnAnalysis = analysis} = procImpln def
    return [extractAliasInfoFromAnalysis analysis]
currentAliasInfo procs@(CyclicSCC multi) =
    foldM (\info pspec -> do
        def <- getProcDef pspec
        let ProcDefPrim{procImplnAnalysis = analysis} = procImpln def
        return $ info ++ [extractAliasInfoFromAnalysis analysis]
        ) [] multi


-- extract "AliasMap" and "Set InterestingCallProperty" from
-- the given "ProcAnalysis"
extractAliasInfoFromAnalysis :: ProcAnalysis
        -> (AliasMap, Set InterestingCallProperty)
extractAliasInfoFromAnalysis analysis =
    (procArgAliasMap analysis, procInterestingCallProperties analysis)

-- This comparison is CRUCIAL. The underlying data struct should
-- handle equal CORRECTLY.
isAliasInfoChanged :: (AliasMap, Set InterestingCallProperty)
                    -> (AliasMap, Set InterestingCallProperty) -> Bool
isAliasInfoChanged = (/=)

aliasProcBottomUp :: ProcSpec -> Compiler Bool
aliasProcBottomUp pspec = do
    logAlias $ replicate 50 '-'
    logAlias $ "Alias analysis proc (Bottom-up): " ++ show pspec
    logAlias $ replicate 50 '-'

    oldDef <- getProcDef pspec
    let ProcDefPrim{procImplnAnalysis = oldAnalysis} = procImpln oldDef
    -- Update alias analysis info to this proc
    updateProcDefM aliasProcDef pspec
    -- Get the new analysis info from the updated proc
    newDef <- getProcDef pspec
    let ProcDefPrim{procImplnAnalysis = newAnalysis} = procImpln newDef
    -- And compare if the [AliasInfo] changed.
    let oldAliasInfo = extractAliasInfoFromAnalysis oldAnalysis
    let newAliasInfo = extractAliasInfoFromAnalysis newAnalysis
    logAlias "================================================="
    logAlias $ "old: " ++ show oldAliasInfo
    logAlias $ "new: " ++ show newAliasInfo
    return $ isAliasInfoChanged oldAliasInfo newAliasInfo
    -- XXX wrong way to do this. Need to change type signatures of a bunch of
    -- functions start from aliasProcDef which is called by updateProcDefM


-- Check if any argument become stale in this (not inlined) proc call
-- Return updated ProcDef and a flag (indicating if proc analysis info changed)
aliasProcDef :: ProcDef -> Compiler ProcDef
aliasProcDef def
    | not (procInline def) = do
        let oldImpln@(ProcDefPrim _ caller body oldAnalysis speczBodies) =
             procImpln def
        logAlias $ show caller

        realParams <- (primParamName <$>) <$> protoRealParams caller
        let initAliasMap = List.foldl (\am param -> unionTwoInDS (LiveVar param)
                                (MaybeAliasByParam param) am) emptyDS realParams

        -- Actual analysis
        (aliasMap, interestingCallProperties, multiSpeczDepInfo, _) <-
                aliasedByBody caller body
                    (initAliasMap, Set.empty, Map.empty, Map.empty)

        aliasMap' <- completeAliasMap caller aliasMap
        -- Update proc analysis with new aliasPairs
        let newAnalysis =
                oldAnalysis {
                    procArgAliasMap = aliasMap',
                    procInterestingCallProperties = interestingCallProperties,
                    procMultiSpeczDepInfo = multiSpeczDepInfo}
        return $
            def { procImpln = oldImpln { procImplnAnalysis = newAnalysis } }
aliasProcDef def = return def


-- Analysis a "ProcBody".
aliasedByBody :: PrimProto -> ProcBody -> AnalysisInfo -> Compiler AnalysisInfo
aliasedByBody caller body analysisInfo =
    aliasedByPrims caller body analysisInfo >>=
    aliasedByFork caller body


-- Check alias created by prims of caller proc
aliasedByPrims :: PrimProto -> ProcBody -> AnalysisInfo -> Compiler AnalysisInfo
aliasedByPrims caller body analysisInfo = do
    let prims = bodyPrims body
    -- Analyse simple prims:
    -- (only process alias pairs incurred by move, access, cast)
    logAlias "\nAnalyse prims (aliasedByPrims):    "
    foldM (aliasedByPrim caller) analysisInfo prims


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
aliasedByFork :: PrimProto -> ProcBody -> AnalysisInfo -> Compiler AnalysisInfo
aliasedByFork caller body analysisInfo = do
    logAlias "\nAnalyse forks (aliasedByFork):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies deflt -> do
            logAlias ">>> Forking:"
            analysisInfos <-
                mapM (\body' -> aliasedByBody caller body' analysisInfo)
                    $ fBodies ++ maybeToList deflt
            return $ mergeAnalysisInfo analysisInfos
        NoFork -> do
            logAlias ">>> No fork."
            -- drop "deadCells", we don't need it after fork
            return analysisInfo


aliasedByPrim :: PrimProto -> AnalysisInfo -> Placed Prim
        -> Compiler AnalysisInfo
aliasedByPrim proto info prim = do
    let (aliasMap, interestingCallProperties, multiSpeczDepInfo, deadCells) =
            info
    aliasMap' <- updateAliasedByPrim aliasMap prim
    (interestingCallProperties', multiSpeczDepInfo')
        <- updateMultiSpeczInfoByPrim
            proto (aliasMap, interestingCallProperties, multiSpeczDepInfo) prim
    (interestingCallProperties'', deadCells')
        <- updateDeadCellsByPrim
            proto (aliasMap, interestingCallProperties', deadCells) prim
    return
        (aliasMap', interestingCallProperties'', multiSpeczDepInfo', deadCells')


-- merge a list of "AnalysisInfo" after fork.
mergeAnalysisInfo :: [AnalysisInfo] -> AnalysisInfo
mergeAnalysisInfo infos =
    let (aliasMapList, interestingCallPropertiesList,
            multiSpeczDepInfoList, deadCellsList) = List.unzip4 infos
        aliasMap = List.foldl combineTwoDS emptyDS aliasMapList
        interestingCallProperties =
            List.foldl Set.union Set.empty interestingCallPropertiesList
        -- XXX there could be something better than "Map.unions"
        multiSpeczDepInfo = Map.unions multiSpeczDepInfoList
        -- We don't need "deadCells" after fork for now.
        deadCells = Map.empty
    in (aliasMap, interestingCallProperties, multiSpeczDepInfo, deadCells)


-- |Log a message, if we are logging optimisation activity.
logAlias :: String -> Compiler ()
logAlias = logMsg Analysis

----------------------------------------------------------------
--                 Proc Level Aliasing Analysis
----------------------------------------------------------------
-- Compute aliasMap on parameters for each procedure


completeAliasMap :: PrimProto -> AliasMapLocal -> Compiler AliasMap
completeAliasMap caller aliasMap = do
    -- Clean up summary of aliases by removing phantom params
    -- and singletons
    realParams <- Set.fromList . (primParamName <$>)
                    <$> protoRealParams caller
    -- realParams is a list of formal params of this caller
    let aliasMap' = filterDS (\x -> case x of
                            MaybeAliasByParam _ -> True
                            _ -> False) aliasMap
                        |> removeSingletonFromDS
                        |> mapDS (\x -> case x of
                            MaybeAliasByParam arg -> arg
                            _ -> shouldnt "aliasMap is invalid")
    -- Some logging
    logAlias $ "^^^  after analyse:    " ++ show aliasMap
    logAlias $ "^^^  remove phantom params: " ++ show realParams
    logAlias $ "^^^  alias of formal params: " ++ show aliasMap'
    return aliasMap'


-- Build up alias pairs triggerred by proc calls
updateAliasedByPrim :: AliasMapLocal -> Placed Prim -> Compiler AliasMapLocal
updateAliasedByPrim aliasMap prim =
    case content prim of
        PrimCall _ spec _ args _ -> do
            -- Analyse proc calls
            calleeDef <- getProcDef spec
            let ProcDefPrim _ calleeProto _ analysis _ = procImpln calleeDef
            let calleeParamAliases = procArgAliasMap analysis
            logAlias $ "--- call          " ++ show spec ++" (callee): "
            logAlias $ "" ++ show calleeProto
            logAlias $ "PrimCall args:    " ++ show args
            let paramArgMap = mapParamToArgVar calleeProto args
            -- calleeArgsAliasMap is the alias map of actual arguments passed
            -- into callee
            logAlias $ "args: " ++ show args
            logAlias $ "paramArgMap: " ++ show paramArgMap
            let calleeArgsAliases =
                    mapDS (\x -> Map.lookup x paramArgMap) calleeParamAliases
                    -- filter out aliases of constant args
                    -- (caused by constant constructor)
                    |> filterDS isJust
                    |> mapDS (\x -> LiveVar (fromJust x))
            combined <- aliasedArgsInPrimCall calleeArgsAliases aliasMap args
            logAlias $ "calleeParamAliases: " ++ show calleeParamAliases
            logAlias $ "calleeArgsAliases:  " ++ show calleeArgsAliases
            logAlias $ "current aliasMap:   " ++ show aliasMap
            logAlias $ "combined:           " ++ show combined
            return combined
        _ -> do
            -- Analyse simple prims
            logAlias $ "--- simple prim:  " ++ show prim
            let prim' = content prim
            maybeAliasedPrimArgs <- maybeAliasPrimArgs prim'
            aliasedArgsInSimplePrim aliasMap maybeAliasedPrimArgs
                                        (fst $ primArgs prim')


-- Build up maybe aliased inputs and outputs triggered by move, access, cast,
-- load and store instructions.
-- Not to compute aliasing from mutate instructions with the assumption that we
-- always try to do nondestructive update.
-- Retruns maybeAliasedVariables
maybeAliasPrimArgs :: Prim -> Compiler [AliasMapLocalItem]
maybeAliasPrimArgs (PrimForeign "lpvm" "access" _ args) =
    _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign "lpvm" "cast" _ args) =
    _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign "llvm" "move" _ args) =
    _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign "lpvm" "load" _ args) =
    _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign "lpvm" "store" _ args) =
    _maybeAliasPrimArgs args
maybeAliasPrimArgs prim@(PrimForeign "lpvm" "mutate" flags args) = do
    let [fIn, fOut, _, _, _, _, mem] = args
    -- "fIn" is not alised to "fOut" when "noalias" flag is set
    -- Primitive types will be removed in "_maybeAliasPrimArgs"
    let args' =if "noalias" `elem` flags
        then [fOut, mem]
        else [fIn, fOut, mem]
    _maybeAliasPrimArgs args'
maybeAliasPrimArgs prim = return []


-- Helper function for the above maybeAliasPrimArgs function
-- It filters the args and keeps those may aliased with others
-- We don't care about the Flow of args
-- since the aliasMap is undirectional
_maybeAliasPrimArgs :: [PrimArg] -> Compiler [AliasMapLocalItem]
_maybeAliasPrimArgs args = do
    args' <- mapM filterArg args
    let escapedVars = catMaybes args'
    return escapedVars
  where
    filterArg arg =
        case arg of
        ArgVar{argVarName=var, argVarType=ty} -> maybeAddressAlias arg ty $ LiveVar var
        ArgGlobal global ty -> maybeAddressAlias arg ty $ AliasByGlobal global
        _ -> return Nothing
    maybeAddressAlias arg ty item = do
        rep <- lookupTypeRepresentation ty
        -- Only Pointer types will create alias
        if rep == Just Pointer
        then return $ Just item
        else return Nothing


-- Check Arg aliases in one of proc calls inside a ProcBody
-- primArgs: argument in current prim that being analysed
aliasedArgsInPrimCall :: AliasMapLocal -> AliasMapLocal
        -> [PrimArg] -> Compiler AliasMapLocal
aliasedArgsInPrimCall calleeArgsAliases currentAlias primArgs = do
    let combinedAliases1 = combineTwoDS calleeArgsAliases currentAlias
    return $ removeDeadVar combinedAliases1 primArgs


-- Check Arg aliases in one of the prims of a ProcBody.
-- (maybeAliasedInput, maybeAliasedOutput, primArgs): argument in current prim
-- that being analysed
aliasedArgsInSimplePrim :: AliasMapLocal -> [AliasMapLocalItem] -> [PrimArg]
        -> Compiler AliasMapLocal
aliasedArgsInSimplePrim aliasMap [] primArgs =
        -- No new aliasing incurred but still need to cleanup final args
        return $ removeDeadVar aliasMap primArgs
aliasedArgsInSimplePrim aliasMap maybeAliasedPrimArgs primArgs = do
        logAlias $ "      primArgs:             " ++ show primArgs
        logAlias $ "      maybeAliasedPrimArgs: " ++ show maybeAliasedPrimArgs
        let aliasMap' = addConnectedGroupToDS maybeAliasedPrimArgs aliasMap
        return $ removeDeadVar aliasMap' primArgs


-- Helper: map arguments in callee proc to its formal parameters so we can get
-- alias info of the arguments
mapParamToArgVar :: PrimProto -> [PrimArg] -> Map PrimVarName PrimVarName
mapParamToArgVar proto args =
    let formalParamNames = primProtoParamNames proto
        paramArgPairs = _zipParamToArgVar formalParamNames args
    in Map.fromList paramArgPairs


-- Helper: zip formal param to PrimArg with ArgVar data constructor
_zipParamToArgVar :: [PrimVarName] -> [PrimArg] -> [(PrimVarName, PrimVarName)]
_zipParamToArgVar (p:params) (ArgVar{argVarName=nm}:args) =
    (p, nm):_zipParamToArgVar params args
_zipParamToArgVar (_:params) (_:args) = _zipParamToArgVar params args
_zipParamToArgVar [] _ = []
_zipParamToArgVar _ [] = []


removeDeadVar :: AliasMapLocal -> [PrimArg] -> AliasMapLocal
removeDeadVar aliasMap args =
    let finalArg arg =
            case arg of
                ArgVar{argVarName=varName, argVarFinal=final} ->
                    if final then Just varName else Nothing
                _ ->
                    Nothing
    in
    Maybe.mapMaybe finalArg args
    |> List.map LiveVar
    |> Set.fromList
    |> (`removeFromDS` aliasMap)


----------------------------------------------------------------
--                 Global Level Aliasing Analysis
----------------------------------------------------------------
-- The local one above considers all parameters as aliased, and this global
-- one is to extend that by generating specialized procedures where
-- some parameters aren't aliased.
-- The code here is to analysis each procedure and list parameters
-- that are interesting for further use (in "Transform.hs").
-- We consider a parameter is interesting when the alias
-- information of that parameter can help us generate a
-- better version of that procedure.
-- More detail about Multiple Specialization can be found in "Transform.hs"


-- we say a real param is interesting if it can be updated
-- destructively when it doesn't alias to anything from outside
updateMultiSpeczInfoByPrim :: PrimProto
        -> (AliasMapLocal, Set InterestingCallProperty, MultiSpeczDepInfo)
        -> Placed Prim
        -> Compiler (Set InterestingCallProperty, MultiSpeczDepInfo)
updateMultiSpeczInfoByPrim proto
        (aliasMap, interestingCallProperties, multiSpeczDepInfo) prim =
    case content prim of
        PrimCall callSiteID spec _ args  _ -> do
            calleeDef <- getProcDef spec
            let ProcDefPrim _ calleeProto _ analysis _ = procImpln calleeDef
            let interestingPrimCallInfo = List.zip args [0..]
                    |> List.filter (\(arg, paramID) ->
                        -- we only care parameters that are interesting,
                        -- args that aren't struct(address) are removed.
                        Set.member (InterestingUnaliased paramID)
                                (procInterestingCallProperties analysis)
                        -- if a argument is used more than once,
                        -- then it should be aliased
                        && isArgVarUsedOnceInArgs arg args calleeProto)
                    |> Maybe.mapMaybe (\(arg, paramID) ->
                        fmap (\requiredParams -> (arg, paramID, requiredParams))
                            (isArgUnaliased aliasMap arg))
            logAlias $ "interestingPrimCallInfo: "
                    ++ show interestingPrimCallInfo
            -- update interesting params
            let newInterestingParams =
                    List.concatMap (\(_, _, x) -> x) interestingPrimCallInfo
            unless (List.null newInterestingParams)
                        $ logAlias $ "Found interesting params: "
                        ++ show newInterestingParams
            let interestingCallProperties' =
                    addInterestingUnaliasedParams proto
                        interestingCallProperties newInterestingParams
            -- update dependencies
            let infoItems = List.map (\(_, calleeParamID, requiredParams) ->
                    let requiredParamIDs =
                            List.map (parameterVarNameToID proto) requiredParams
                    in
                    NonAliasedParamCond calleeParamID requiredParamIDs
                    ) interestingPrimCallInfo
            multiSpeczDepInfo' <- updateMultiSpeczDepInfo multiSpeczDepInfo
                    callSiteID spec infoItems
            return (interestingCallProperties', multiSpeczDepInfo')
        PrimForeign "lpvm" "mutate" flags args ->
            case args of
                [fIn, _, _, ArgInt des _, _, _, _] ->
                    -- Skip "mutate" that is set to be destructive by
                    -- previous optimizer
                    if des /= 1
                    then
                        -- mutate only happens on struct(address)
                        case isArgUnaliased aliasMap fIn of
                        Just requiredParams -> do
                            logAlias $ "Found interesting params: "
                                    ++ show requiredParams
                            let interestingCallProperties' =
                                    addInterestingUnaliasedParams proto
                                        interestingCallProperties requiredParams
                            return
                                (interestingCallProperties', multiSpeczDepInfo)
                        Nothing ->
                            return
                                (interestingCallProperties, multiSpeczDepInfo)
                    else return (interestingCallProperties, multiSpeczDepInfo)
                _ ->
                    shouldnt "unable to match args of lpvm mutate instruction"
        _ -> return (interestingCallProperties, multiSpeczDepInfo)


-- It returns "Just requiredParams" if the given "PrimArg" isn't aliased and
-- isn't used after this point.
-- "requiredParams" is a list of params that needs to be non-aliased to make
-- the given "PrimArg" actually interesting (Caused by "MaybeAliasByParam").
-- A special case is that it returns "Just []" for "ArgInt", because "ArgInt"
-- can be used for struct tags.
-- It returns "Nothing" in other cases.
isArgUnaliased :: AliasMapLocal -> PrimArg -> Maybe [PrimVarName]
isArgUnaliased aliasMap ArgVar{argVarName=varName, argVarFinal=final} =
    let items = connectedItemsInDS (LiveVar varName) aliasMap |> Set.toList in
    let requiredParams =
            Maybe.mapMaybe (\case
                    MaybeAliasByParam param -> Just param
                    _ -> Nothing
                ) items
    in
    -- only "MaybeAliasByParam" is allowed
    if final && sameLength items requiredParams
    then
        Just requiredParams
    else
        Nothing
isArgUnaliased _ (ArgInt _ _) = Just []
isArgUnaliased _ _ = Nothing


-- return True if the given arg is only used once in given list of arg.
-- Unneeded params are ignored.
-- no need to worry about output var since it's in SSA form.
isArgVarUsedOnceInArgs :: PrimArg -> [PrimArg] -> PrimProto -> Bool
isArgVarUsedOnceInArgs ArgVar{argVarName=varName} args calleeProto =
    List.zip args (primProtoParams calleeProto)
    |> List.filter (\case
            (ArgVar{argVarName=varName'}, param)
                -> varName == varName' && paramIsNeeded param
            _
                -> False)
    |> List.length |> (== 1)
isArgVarUsedOnceInArgs _ _ _ = True -- we don't care about constant value


-- adding interesting unaliased params
addInterestingUnaliasedParams :: PrimProto -> Set InterestingCallProperty
        -> [PrimVarName] -> Set InterestingCallProperty
addInterestingUnaliasedParams proto properties params =
    List.map (InterestingUnaliased . (parameterVarNameToID proto)) params
    |> (List.foldr Set.insert) properties


-- adding new specz version dependency
updateMultiSpeczDepInfo :: MultiSpeczDepInfo -> CallSiteID -> ProcSpec
        -> [CallSiteProperty] -> Compiler MultiSpeczDepInfo
updateMultiSpeczDepInfo multiSpeczDepInfo callSiteID pSpec items =
    if List.null items
    then
        return multiSpeczDepInfo
    else do
        logAlias $ "Update MultiSpeczDepInfo, CallSiteID: " ++ show callSiteID
                ++ " ProcSpec: " ++ show pSpec ++ " items:" ++ show items
        return $ Map.alter (\x ->
            fromMaybe (pSpec, Set.empty) x
            |> second (Set.union (Set.fromList items))
            |> Just) callSiteID multiSpeczDepInfo


----------------------------------------------------------------
--                 Dead Memory Cell Analysis
----------------------------------------------------------------
-- This analyser finds dead memory cells so we can reuse them to
-- avoid some alloc instructions.
-- The currently alias map is undirectional, so we have to identify
-- dead cells using access instruction.
-- if there is an access instruction that reads some value from x,
-- then we consider x is dead if x is unaliased and final.
--
-- The transform part can be found in "Transform.hs".

-- XXX currently it relies on the size arg of the access instruction. Another
--       way (much more flexible) to do it is introducing some lpvm instructions
--       that do nothing and only provide information for the compiler.
-- TODO call "GC_free" on large unused dead cells.
--       (according to https://github.com/ivmai/bdwgc, > 8 bytes)
-- TODO we'd like this analysis to detect structures that are dead aside from
--       later access instructions, which could be moved earlier to allow the
--       structure to be reused.
-- TODO consider re-run the optimiser after this or even run this before the
--       optimiser.


-- Update dead cells info based on the given prim. If a dead cell comes from a
-- parameter, then we mark that parameter as interesting.
updateDeadCellsByPrim :: PrimProto
        -> (AliasMapLocal, Set InterestingCallProperty, DeadCells)
        -> Placed Prim -> Compiler (Set InterestingCallProperty, DeadCells)
updateDeadCellsByPrim proto (aliasMap, interestingCallProperties, deadCells)
        prim =
    case content prim of
        PrimForeign "lpvm" "access" _ args -> do
            deadCells'
                <- updateDeadCellsByAccessArgs (aliasMap, deadCells) args
            return (interestingCallProperties, deadCells')
        PrimForeign "lpvm" "alloc" _ args  -> do
            let (result, deadCells') = assignDeadCellsByAllocArgs deadCells args
            interestingCallProperties' <- case result of
                    Nothing -> return interestingCallProperties
                    Just (selectedCell, requiredParams) ->
                        if requiredParams /= []
                        then do
                            logAlias $ "Found interesting parameters in dead "
                                    ++ "cell analysis. " ++ show requiredParams
                            return $ addInterestingUnaliasedParams proto
                                        interestingCallProperties requiredParams
                        else return interestingCallProperties
            return (interestingCallProperties', deadCells')
        _ ->
            return (interestingCallProperties, deadCells)


-- Find new dead cell from the given "primArgs" of "access" instruction.
updateDeadCellsByAccessArgs :: (AliasMapLocal, DeadCells) -> [PrimArg]
        -> Compiler DeadCells
updateDeadCellsByAccessArgs (aliasMap, deadCells) primArgs = do
    case primArgs of
        -- [struct:type, offset:int, size:int, startOffset:int, ?member:type2]
        [struct@ArgVar{argVarName=varName}, _, ArgInt size _, startOffset, _] ->
            let size' = fromInteger size in
            case isArgUnaliased aliasMap struct of
                Just requiredParams -> do
                    logAlias $ "Found new dead cell: " ++ show varName
                            ++ " size:" ++ show size' ++ " requiredParams:"
                            ++ show requiredParams
                    let newCell = ((struct, startOffset), requiredParams)
                    return $ Map.alter (\x ->
                        (case x of
                            Nothing -> [newCell]
                            Just cells -> newCell:cells) |> Just)
                                    size' deadCells
                Nothing ->
                    return deadCells
        _ -> return deadCells


-- Try to assign a dead cell to reuse for the given "alloc" instruction.
-- It returns "(result, deadCells)". "result" is "Nothing" when there isn't a
-- suitable dead cell to reuse. Otherwise, result is
-- "Just ((selectedCell, startOffset), requiredParams)". "requiredParams"
-- contains parameters that need to be non-aliased before reusing the
-- "selectedCell" (Caused by "MaybeAliasByParam"). Note that this always tries
-- to assigned a cell with empty "requiredParams" first.
assignDeadCellsByAllocArgs :: DeadCells -> [PrimArg]
        -> (Maybe ((PrimArg, PrimArg), [PrimVarName]), DeadCells)
assignDeadCellsByAllocArgs deadCells primArgs =
    case primArgs of
        -- [size:int, ?struct:type]
        [ArgInt size _, struct] ->
            let size' = fromInteger size in
            case Map.lookup size' deadCells of
                Just cells ->
                    let assigned =
                            -- try to select one without "requiredParams".
                            case List.find (List.null . snd) cells of
                                Just x  -> Just x
                                Nothing -> case cells of
                                    []    -> Nothing
                                    (x:_) -> Just x
                    in
                    case assigned of
                        Nothing -> (Nothing, deadCells)
                        Just x  ->
                            -- XXX we need something better than this. In order to
                            -- have better optimization, we combine "requiredParams"
                            -- from all possible cells. However, it may create some
                            -- specialized versions that are identical.
                            let requiredParams =
                                    if List.null $ snd x
                                    then []
                                    else
                                        List.concatMap snd cells
                                        |> Set.fromList |> Set.toList
                            in
                            let cells' = List.delete x cells in
                            let deadCells' = Map.insert size' cells' deadCells in
                            (Just (fst x, requiredParams), deadCells')
                Nothing    -> (Nothing, deadCells)
        _ -> (Nothing, deadCells)
