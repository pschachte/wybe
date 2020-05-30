--  File     : AliasAnalysis.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE LambdaCase #-}

module AliasAnalysis (
    AliasMapLocal, AliasMapLocalItem(..), aliasSccBottomUp, currentAliasInfo,
    isAliasInfoChanged, updateAliasedByPrim, isArgVarInteresting,
    pairArgVarWithParam, isArgVarUsedOnceInArgs,
    DeadCells, updateDeadCellsByAccessArgs, assignDeadCellsByAllocArgs
    ) where

import           AST
import           Control.Monad
import           Data.Graph
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Data.Maybe    as Maybe
import           Flow          ((|>))
import           Options       (LogSelection (Analysis))
import           Util


-- This type is for local use only. After the analysis, it will be converted to 
-- "AliasMultiSpeczInfo" and stored in LPVM module. It's almost the same as
-- "AliasMultiSpeczInfo" but it use "Set" so it can be easier to use during
-- analysis. Original definition can be found in "AST.hs".
-- More on this can be found under the 
-- "Global Level Aliasing Analysis" section below.
type AliasMultiSpeczInfoLocal = (Set PrimVarName, AliasMultiSpeczDep)


-- This "AliasMapLocal" is used during analysis and it will be converted to
-- "AliasMap" (defined in "AST.hs") and stored in LPVM module.
-- The "AliasMap" records the relation between parameters of each procedure.
-- The "AliasMapLocal" records all variables during the analysis. "LiveVar" is
-- for variables, it can be added to and removed from the map during analysis.
-- For parameters, we consider it's a nomarl variable ("LiveVar") aliased with 
-- something outside the procedure scope ("AliasByParam" / "MaybeAliasByParam").
-- "AliasByParam" and "MaybeAliasByParam" won't be removed during the analysis,
-- but if the existence of a "MaybeAliasByParam" can change the outcome then we
-- consider the corresponding parameter as interesting.
data AliasMapLocalItem 
    = LiveVar           PrimVarName
    | AliasByParam      PrimVarName
    | MaybeAliasByParam PrimVarName
    deriving (Eq, Ord, Show)

type AliasMapLocal = DisjointSet AliasMapLocalItem


-- For each type, record all reusable cells, more on this can be found under
-- the "Dead Memory Cell Analysis" section below.
-- Each reusable cell is recorded as "(varName, requiredParams)"". "varName" is
-- the name of the variable that can be reused and requiredParams is a list of 
-- parameters that need to be non-aliased before reusing that cell (casused by
-- "MaybeAliasByParam").
type DeadCells = Map TypeSpec [(PrimVarName, [PrimVarName])]

type AnalysisInfo = (AliasMapLocal, AliasMultiSpeczInfoLocal, DeadCells)

-- XXX aliasSccBottomUp :: SCC ProcSpec -> Compiler a
aliasSccBottomUp :: SCC ProcSpec -> Compiler ()
aliasSccBottomUp (AcyclicSCC single) = do
    _ <- aliasProcBottomUp single -- ^immediate fixpoint if no mutual dependency
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


currentAliasInfo :: SCC ProcSpec -> Compiler [(AliasMap, AliasMultiSpeczInfo)]
currentAliasInfo (AcyclicSCC single) = do
    def <- getProcDef single
    let (ProcDefPrim _ _ analysis _) = procImpln def
    return [extractAliasInfoFromAnalysis analysis]
currentAliasInfo procs@(CyclicSCC multi) =
    foldM (\info pspec -> do
        def <- getProcDef pspec
        let (ProcDefPrim _ _ analysis _) = procImpln def
        return $ info ++ [extractAliasInfoFromAnalysis analysis]
        ) [] multi


-- extract "AliasMap" and "AliasMultiSpeczInfo" from the given
-- "ProcAnalysis"
extractAliasInfoFromAnalysis :: ProcAnalysis -> (AliasMap, AliasMultiSpeczInfo) 
extractAliasInfoFromAnalysis analysis = 
    (procArgAliasMap analysis, procArgAliasMultiSpeczInfo analysis)

-- This comparison is CRUCIAL. The underlying data struct should
-- handle equal CORRECTLY.
isAliasInfoChanged :: (AliasMap, AliasMultiSpeczInfo) 
                    -> (AliasMap, AliasMultiSpeczInfo) -> Bool
isAliasInfoChanged = (/=)

-- XXX aliasProcBottomUp :: ProcSpec -> Compiler a
aliasProcBottomUp :: ProcSpec -> Compiler Bool
aliasProcBottomUp pspec = do
    logAlias $ replicate 50 '-'
    logAlias $ "Alias analysis proc (Bottom-up): " ++ show pspec
    logAlias $ replicate 50 '-'

    oldDef <- getProcDef pspec
    let (ProcDefPrim _ _ oldAnalysis _) = procImpln oldDef
    -- Update alias analysis info to this proc
    updateProcDefM aliasProcDef pspec
    -- Get the new analysis info from the updated proc
    newDef <- getProcDef pspec
    let (ProcDefPrim _ _ newAnalysis _) = procImpln newDef
    -- And compare if the [AliasInfo] changed.
    let oldAliasInfo = extractAliasInfoFromAnalysis oldAnalysis
    let newAliasInfo = extractAliasInfoFromAnalysis newAnalysis
    logAlias "================================================="
    logAlias $ "old: " ++ show oldAliasInfo
    logAlias $ "new: " ++ show newAliasInfo
    return $ isAliasInfoChanged oldAliasInfo newAliasInfo
    -- ^XXX wrong way to do this. Need to change type signatures of a bunch of
    -- functions start from aliasProcDef which is called by updateProcDefM


-- Check if any argument become stale in this (not inlined) proc call
-- Return updated ProcDef and a flag (indicating if proc analysis info changed)
-- XXX aliasProcDef :: ProcDef -> Compiler (ProcDef, a)
aliasProcDef :: ProcDef -> Compiler ProcDef
aliasProcDef def
    | not (procInline def) = do
        let (ProcDefPrim caller body oldAnalysis speczBodies) = procImpln def
        logAlias $ show caller

        realParams <- (primParamName <$>) <$> protoRealParams caller
        let initAliasMap = List.foldl (\am param -> unionTwoInDS (LiveVar param) 
                                (MaybeAliasByParam param) am) emptyDS realParams

        -- Actual analysis
        (aliasMap, multiSpeczInfo) <- 
                aliasedByBody caller body
                        (initAliasMap, (Set.empty, Set.empty), Map.empty)
        
        aliasMap' <- completeAliasMap caller aliasMap
        let multiSpeczInfo' =
                    completeMultiSpeczInfo realParams multiSpeczInfo
        -- Update proc analysis with new aliasPairs
        let newAnalysis = oldAnalysis {
                            procArgAliasMap = aliasMap',
                            procArgAliasMultiSpeczInfo = multiSpeczInfo'
                        }
        return $ 
            def { procImpln = ProcDefPrim caller body newAnalysis speczBodies}
aliasProcDef def = return def


-- Analysis a "ProcBody"
-- It returns "AliasMap" and "AliasMultiSpeczInfoLocal" but not "DeadCells"
-- since we don't need to merge it and have the result after the analysis.
aliasedByBody :: PrimProto -> ProcBody -> AnalysisInfo 
        -> Compiler (AliasMapLocal, AliasMultiSpeczInfoLocal)
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
    foldM aliasedByPrim analysisInfo prims


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- It returns "AliasMap" and "AliasMultiSpeczInfoLocal" but not "DeadCells"
-- since we don't need to merge it and have the result after the analysis.
aliasedByFork :: PrimProto -> ProcBody -> AnalysisInfo
        -> Compiler (AliasMapLocal, AliasMultiSpeczInfoLocal)
aliasedByFork caller body analysisInfo = do
    logAlias "\nAnalyse forks (aliasedByFork):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logAlias ">>> Forking:"
            analysisInfos <- 
                mapM (\body' -> aliasedByBody caller body' analysisInfo) fBodies
            let (aliasMaps, multiSpeczInfos) = unzip analysisInfos
            let aliasMap' = List.foldl combineTwoDS emptyDS aliasMaps
            let multiSpeczInfo' = mergeMultiSpeczInfo multiSpeczInfos 
            return (aliasMap', multiSpeczInfo')
        NoFork -> do
            logAlias ">>> No fork."
            -- drop "deadCells", we don't need it after fork
            let (aliasMap, multiSpeczInfo, _) = analysisInfo
            return (aliasMap, multiSpeczInfo)


aliasedByPrim :: AnalysisInfo -> Placed Prim
                                                -> Compiler AnalysisInfo
aliasedByPrim (aliasMap, multiSpeczInfo, deadCells) prim = do
    aliasMap' <- updateAliasedByPrim aliasMap prim
    multiSpeczInfo' 
        <- updateMultiSpeczInfoByPrim (aliasMap, multiSpeczInfo) prim
    (multiSpeczInfo'', deadCells')
        <- updateDeadCellsByPrim (aliasMap, multiSpeczInfo', deadCells) prim
    return (aliasMap', multiSpeczInfo'', deadCells')


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
    -- ^realParams is a list of formal params of this caller
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
        PrimCall spec args -> do
            -- | Analyse proc calls
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto _ analysis _) = procImpln calleeDef
            let calleeParamAliases = procArgAliasMap analysis
            logAlias $ "--- call          " ++ show spec ++" (callee): "
            logAlias $ "" ++ show calleeProto
            logAlias $ "PrimCall args:    " ++ show args
            let paramArgMap = mapParamToArgVar calleeProto args
            -- calleeArgsAliasMap is the alias map of actual arguments passed
            -- into callee
            let calleeArgsAliases = 
                    mapDS (\x -> 
                        case Map.lookup x paramArgMap of 
                            -- TODO: verify this part. Better to use
                            -- "shouldnt" if that is really the case.
                            -- Currently some tests (eg. "alias_fork1")
                            -- reach this path.
                            Nothing -> x -- shouldn't happen
                            Just y -> y
                    ) calleeParamAliases
            let calleeArgsAliases' = mapDS LiveVar calleeArgsAliases
            combined <- aliasedArgsInPrimCall calleeArgsAliases' aliasMap args
            logAlias $ "calleeArgsAliases:" ++ show calleeArgsAliases
            logAlias $ "current aliasMap: " ++ show aliasMap
            logAlias $ "combined:         " ++ show combined
            return combined
        _ -> do
            -- | Analyse simple prims
            logAlias $ "--- simple prim:  " ++ show prim
            let prim' = content prim
            maybeAliasedVariables <- maybeAliasPrimArgs prim'
            aliasedArgsInSimplePrim aliasMap maybeAliasedVariables 
                                        (primArgs prim')


-- Build up maybe aliased inputs and outputs triggered by move, access, cast
-- instructions.
-- Not to compute aliasing from mutate instructions with the assumption that we
-- always try to do nondestructive update.
-- Retruns maybeAliasedVariables
maybeAliasPrimArgs :: Prim -> Compiler [PrimVarName]
maybeAliasPrimArgs (PrimForeign "lpvm" "access" _ args) =
    _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign "lpvm" "cast" _ args) =
    _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign "llvm" "move" _ args) =
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
_maybeAliasPrimArgs :: [PrimArg] -> Compiler [PrimVarName]
_maybeAliasPrimArgs args = do
    args' <- mapM filterArg args
    let escapedVars = catMaybes args'
    return escapedVars
  where
    filterArg arg =
        case arg of 
        ArgVar{argVarName=var, argVarType=ty}
            -> do
                isPhantom <- argIsPhantom arg
                rep <- lookupTypeRepresentation ty 
                -- Only Address type will create alias
                if not isPhantom && rep == Just Address
                    then return $ Just var
                    else return Nothing
        _   -> return Nothing 


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
aliasedArgsInSimplePrim :: AliasMapLocal -> [PrimVarName] -> [PrimArg]
        -> Compiler AliasMapLocal
aliasedArgsInSimplePrim aliasMap [] primArgs =
        -- No new aliasing incurred but still need to cleanup final args
        return $ removeDeadVar aliasMap primArgs
aliasedArgsInSimplePrim aliasMap
                            maybeAliasedVariables primArgs = do
        logAlias $ "      primArgs:           " ++ show primArgs
        logAlias $ "      maybeAliasedVariables:  " 
                                    ++ show maybeAliasedVariables 
        let maybeAliasedVariables' = List.map LiveVar maybeAliasedVariables
        let aliasMap' = addConnectedGroupToDS maybeAliasedVariables' aliasMap
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
-- We consider a parameter is intersting when the alias
-- information of that parameter can help us generate a
-- better version of that procedure. 


mergeMultiSpeczInfo :: [AliasMultiSpeczInfoLocal] -> AliasMultiSpeczInfoLocal
mergeMultiSpeczInfo info =
    let (interestingParamsList, dependenciesList) = List.unzip info in
    let interestingParams = 
            List.foldl Set.union Set.empty interestingParamsList
    in 
    let dependencies = Set.unions dependenciesList in
        (interestingParams, dependencies)


-- we say a real param is interesting if it can be updated
-- destructively when it doesn't alias to anything from outside
updateMultiSpeczInfoByPrim :: (AliasMapLocal, AliasMultiSpeczInfoLocal)
        -> Placed Prim -> Compiler AliasMultiSpeczInfoLocal
updateMultiSpeczInfoByPrim (aliasMap, multiSpeczInfo) prim =
    case content prim of
        PrimCall spec args -> do
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto _ analysis _) = procImpln calleeDef
            let calleeMultiSpeczInfo = procArgAliasMultiSpeczInfo analysis
            let calleeInterestingParams = fst calleeMultiSpeczInfo
            -- [(arg, calleeParam, [requiredCallerParam])]
            let interestingPrimCallInfo = 
                    pairArgVarWithParam args calleeProto
                    |> List.filter (\(arg, param) -> 
                        -- we only care parameters that are interesting,
                        -- args that aren't struct(address) are removed.
                        List.elem param calleeInterestingParams
                        -- if a argument is used more than once,
                        -- then it should be aliased
                        && isArgVarUsedOnceInArgs arg args)
                    |> Maybe.mapMaybe (\(arg, param) ->
                        case isArgVarInteresting aliasMap arg of
                            Right requiredParams -> 
                                Just (arg, param, requiredParams)
                            Left () ->
                                Nothing)
            logAlias $ "interestingPrimCallInfo: " 
                    ++ show interestingPrimCallInfo
            -- update interesting params
            let interestingParams = 
                    List.concatMap (\(_, _, x) -> x) interestingPrimCallInfo
            unless (List.null interestingParams) 
                        $ logAlias $ "Found interesting params: " 
                        ++ show interestingParams
            let multiSpeczInfo' = 
                    addInterestingParams multiSpeczInfo interestingParams
            -- update dependencies
            let speczVersion = List.map (\calleeParam ->
                    let result =
                            List.find (\(_, param, _) -> param == calleeParam)
                                    interestingPrimCallInfo
                    in
                    case result of 
                        Just (_, _, requiredParams) -> BasedOn requiredParams
                        Nothing                     -> Aliased
                    ) calleeInterestingParams
            addSpeczVersion multiSpeczInfo' spec speczVersion
        PrimForeign "lpvm" "mutate" flags args ->
            case args of
                [fIn, _, _, ArgInt des _, _, _, _] ->
                    -- Skip "mutate" that is set to be destructive by 
                    -- previous optimizer
                    if des /= 1
                    then
                        -- mutate only happens on struct(address)
                        case isArgVarInteresting aliasMap fIn of
                        Right requiredParams -> do
                            logAlias $ "Found interesting params: " 
                                    ++ show requiredParams
                            return $ addInterestingParams multiSpeczInfo
                                        requiredParams
                        Left () ->
                            return multiSpeczInfo 
                    else return multiSpeczInfo
                _ ->
                    shouldnt "unable to match args of lpvm mutate instruction"
        _ -> return multiSpeczInfo


-- pair up argument variables of the caller with parameters of the callee
pairArgVarWithParam :: [PrimArg] -> PrimProto -> [(PrimArg, PrimVarName)]
pairArgVarWithParam args proto =
    let formalParamNames = primProtoParamNames proto in
    List.zip args formalParamNames


-- we consider a varibale is interesting when it isn't aliased and not used
-- after this point. Note that it doesn't check whether the given "PrimArg"
-- is a pointer.
-- It returns "Right requiredParams" if it's interesting.
-- "requiredParams" is a list of params that needs to be non-aliased to make
-- the given "PrimArg" actually interesting (Caused by "MaybeAliasByParam").
-- It returns "Left ()" in other cases.
isArgVarInteresting :: AliasMapLocal -> PrimArg -> Either () [PrimVarName]
isArgVarInteresting aliasMap ArgVar{argVarName=varName, argVarFinal=final} =
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
        Right requiredParams
    else
        Left ()
isArgVarInteresting _ _ = Left ()


-- return True if the given arg is only used once in given list of arg.
-- no need to worry about output var since it's in SSA form. 
isArgVarUsedOnceInArgs :: PrimArg -> [PrimArg] -> Bool
isArgVarUsedOnceInArgs ArgVar{argVarName=varName} args =
    List.filter (\case
        ArgVar{argVarName=varName'} -> varName == varName'
        _ -> False) args
    |> List.length |> (== 1)
isArgVarUsedOnceInArgs _ _ = True -- we don't care about constant value


-- update "AliasMultiSpeczInfoLocal" by adding interesting params
addInterestingParams :: AliasMultiSpeczInfoLocal -> [PrimVarName]
        -> AliasMultiSpeczInfoLocal
addInterestingParams info vars = 
    let (params, dependencies) = info in
        (List.foldr Set.insert params vars, dependencies)


-- update "AliasMultiSpeczInfoLocal" by adding new specz version dependency
addSpeczVersion :: AliasMultiSpeczInfoLocal -> ProcSpec
        -> AliasMultiSpeczDepVersion -> Compiler AliasMultiSpeczInfoLocal
addSpeczVersion info proc version = 
    if List.all (== Aliased) version
    then
        return info
    else do
        logAlias $ "Found required specz version: " ++ show proc
                ++ " :" ++ show version
        let (params, dependencies) = info
        let ProcSpec mod procName procID _ = proc
        let dependencies' = Set.insert 
                ((mod, procName, procID), version) dependencies
        return (params, dependencies')


-- Convert the set of interesting params to list
-- The order matters, we keep it the same as the "realParams".
completeMultiSpeczInfo :: [PrimVarName] -> AliasMultiSpeczInfoLocal
        -> AliasMultiSpeczInfo
completeMultiSpeczInfo realParams info = 
    let (params, dependencies) = info in
    (List.filter (`Set.member` params) realParams, dependencies)


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
-- The transform part can be found in "Tranform.hs".

-- TODO: reuse cells that are different types but has the same size.
-- TODO: call "GC_free" on large unused dead cells.
-- TODO: we'd like this analysis to detect structures that are dead aside from
--       later access instructions, which could be moved earlier to allow the
--       structure to be reused.
-- TODO: consider re-run the optimiser after this or even run this before the
--       optimiser.


-- Update dead cells info based on the given prim. If a dead cell comes from a
-- parameter, then we mark that parameter as interesting.
updateDeadCellsByPrim :: AnalysisInfo -> Placed Prim 
        -> Compiler (AliasMultiSpeczInfoLocal, DeadCells)
updateDeadCellsByPrim (aliasMap, multiSpeczInfo, deadCells) prim =
    case content prim of
        PrimForeign "lpvm" "access" _ args -> do
            deadCells' 
                <- updateDeadCellsByAccessArgs (aliasMap, deadCells) args
            return (multiSpeczInfo, deadCells')
        PrimForeign "lpvm" "alloc" _ args  -> do
            let (result, deadCells') = assignDeadCellsByAllocArgs deadCells args
            multiSpeczInfo' <- case result of
                    Nothing -> return multiSpeczInfo
                    Just (selectedCell, requiredParams) -> 
                        if requiredParams /= []
                        then do
                            logAlias $ "Found interesting parameters in dead "
                                    ++ "cell analysis. " ++ show requiredParams
                            return $ addInterestingParams 
                                        multiSpeczInfo requiredParams
                        else return multiSpeczInfo
            return (multiSpeczInfo', deadCells')
        _ ->
            return (multiSpeczInfo, deadCells)


-- Find new dead cell from the given "primArgs" of "access" instruction.
updateDeadCellsByAccessArgs :: (AliasMapLocal, DeadCells) -> [PrimArg]
        -> Compiler DeadCells
updateDeadCellsByAccessArgs (aliasMap, deadCells) primArgs = do
    -- [struct:type, offset:int, ?member:type2]
    let [struct, _, _] = primArgs
    let ArgVar{argVarName=varName, argVarType=ty} = struct
    rep <- lookupTypeRepresentation ty
    if rep == Just Address
    then
        case isArgVarInteresting aliasMap struct of
            Right requiredParams -> do 
                logAlias $ "Found new dead cell: " ++ show varName 
                        ++ " type:" ++ show ty ++ " requiredParams:"
                        ++ show requiredParams
                let newCell = (varName, requiredParams)
                return $ Map.alter (\x ->
                    (case x of 
                        Nothing -> [newCell]
                        Just cells -> newCell:cells) |> Just) ty deadCells
            Left () ->
                return deadCells
    else 
        return deadCells


-- Try to assign a dead cell to reuse for the given "alloc" instruction.
-- It returns "(result, deadCells)". "result" is "Nothing" when there isn't a
-- suitable dead cell to reuse. Otherwise, result is 
-- "Just (selectedCell, requiredParams)". "requiredParams" contains parameters
-- that need to be non-aliased before reusing the "seletedCell" (Caused by
-- "MaybeAliasByParam"). Note that this always trys to assigned a cell with
-- empty "requiredParams" first.
assignDeadCellsByAllocArgs :: DeadCells -> [PrimArg] 
        -> (Maybe (PrimVarName, [PrimVarName]), DeadCells)
assignDeadCellsByAllocArgs deadCells primArgs =
    -- [size:int, ?struct:type]
    let [_, struct] = primArgs in
    let ArgVar{argVarName=varName, argVarType=ty} = struct in
    case Map.lookup ty deadCells of 
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
                    -- TODO: we need something better than this. In order to
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
                    let deadCells' = Map.insert ty cells' deadCells in
                    (Just (fst x, requiredParams), deadCells')
        Nothing    -> (Nothing, deadCells)
