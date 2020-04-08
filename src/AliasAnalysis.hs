--  File     : AliasAnalysis.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module AliasAnalysis (aliasSccBottomUp,
                        currentAliasInfo,
                        isAliasInfoChanged,
                        updateAliasedByPrim,
                        pairArgVarWithParam) where

import           AST
import           Control.Monad
import           Data.Graph
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Data.Maybe    (catMaybes)
import           Flow          ((|>))
import           Options       (LogSelection (Analysis))
import           Util


-- This type is for local use only. It stores interesting
-- parameters during the analysis. After the analysis, it
-- will be converted to [AliasMultiSpeczInfo] and stored
-- in LPVM modure. 
-- More on this can be found under the 
-- "Global Level Aliasing Analysis" section below.
type AliasMultiSpeczInfoLocal = Set PrimVarName

-- For each type, record all reusable cells, more on this can be found under
-- the "Dead Memory Cell Analysis" section below.
type DeadCells = Map TypeSpec [PrimVarName]

type AnalysisInfo = (AliasMap, AliasMultiSpeczInfoLocal, DeadCells)

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


currentAliasInfo :: SCC ProcSpec 
                    -> Compiler [(AliasMap, AliasMultiSpeczInfo)]
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


-- extract [AliasMap] and [AliasMultiSpeczInfo] from the given
-- [ProcAnalysis]
extractAliasInfoFromAnalysis :: ProcAnalysis 
                                -> (AliasMap, AliasMultiSpeczInfo) 
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

        -- Actual analysis
        (aliasMap, multiSpeczInfo) <- 
                aliasedByBody caller body (emptyDS, Set.empty, Map.empty)
        
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


-- Analysis a [ProcBody]
-- It doesn't return [DeadCells].
aliasedByBody :: PrimProto -> ProcBody -> AnalysisInfo 
                                -> Compiler (AliasMap, AliasMultiSpeczInfoLocal)
aliasedByBody caller body analysisInfo =
    aliasedByPrims caller body analysisInfo >>=
    aliasedByFork caller body


-- Check alias created by prims of caller proc
aliasedByPrims :: PrimProto -> ProcBody -> AnalysisInfo -> Compiler AnalysisInfo
aliasedByPrims caller body analysisInfo = do
    realParams <- (primParamName <$>) <$> protoRealParams caller
    let prims = bodyPrims body
    -- Analyse simple prims:
    -- (only process alias pairs incurred by move, access, cast)
    logAlias "\nAnalyse prims (aliasedByPrims):    "
    foldM (aliasedByPrim realParams) analysisInfo prims


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- It doesn't return [DeadCells].
aliasedByFork :: PrimProto -> ProcBody -> AnalysisInfo
                                -> Compiler (AliasMap, AliasMultiSpeczInfoLocal)
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
            -- drop [deadCells], we don't need it after fork
            let (aliasMap, multiSpeczInfo, _) = analysisInfo
            return (aliasMap, multiSpeczInfo)


aliasedByPrim :: [PrimVarName] -> AnalysisInfo -> Placed Prim
                                                -> Compiler AnalysisInfo
aliasedByPrim realParams (aliasMap, multiSpeczInfo, deadCells) prim = do
    aliasMap' <- updateAliasedByPrim realParams aliasMap prim
    multiSpeczInfo' 
        <- updateMultiSpeczInfoByPrim realParams (aliasMap, multiSpeczInfo) prim
    (multiSpeczInfo'', deadCells')
        <- updateDeadCellsByPrim realParams 
                            (aliasMap, multiSpeczInfo', deadCells) prim
    return (aliasMap', multiSpeczInfo'', deadCells')


-- |Log a message, if we are logging optimisation activity.
logAlias :: String -> Compiler ()
logAlias = logMsg Analysis

----------------------------------------------------------------
--                 Proc Level Aliasing Analysis
----------------------------------------------------------------
-- Compute aliasMap on parameters for each procedure


completeAliasMap :: PrimProto -> AliasMap -> Compiler AliasMap
completeAliasMap caller aliasMap = do
    -- Clean up summary of aliases by removing phantom params
    -- and singletons
    realParams <- Set.fromList . (primParamName <$>)
                    <$> protoRealParams caller
    -- ^realParams is a list of formal params of this caller
    let aliasMap' = filterDS (`Set.member` realParams) aliasMap
                        |> removeSingletonFromDS
    -- Some logging
    logAlias $ "^^^  after analyse:    " ++ show aliasMap
    logAlias $ "^^^  remove phantom params: " ++ show realParams
    logAlias $ "^^^  alias of formal params: " ++ show aliasMap'
    return aliasMap'


-- Build up alias pairs triggerred by proc calls
-- realParams: caller's formal params
updateAliasedByPrim :: [PrimVarName] -> AliasMap -> Placed Prim 
                                                -> Compiler AliasMap
updateAliasedByPrim realParams aliasMap prim =
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
                            -- Currently some tests (eg. [alias_fork1])
                            -- reach this path.
                            Nothing -> x -- shouldn't happen
                            Just y -> y
                    ) calleeParamAliases
            combined <- aliasedArgsInPrimCall calleeArgsAliases realParams
                                    aliasMap args
            logAlias $ "calleeArgsAliases:" ++ show calleeArgsAliases
            logAlias $ "current aliasMap: " ++ show aliasMap
            logAlias $ "combined:         " ++ show combined
            return combined
        _ -> do
            -- | Analyse simple prims
            logAlias $ "--- simple prim:  " ++ show prim
            let prim' = content prim
            maybeAliasedVariables <- maybeAliasPrimArgs prim'
            aliasedArgsInSimplePrim realParams aliasMap maybeAliasedVariables
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
    -- [fIn] is not alised to [fOut] when "noalias" flag is set
    -- Primitive types will be removed in [_maybeAliasPrimArgs]
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
-- realParams: caller's formal params
-- primArgs: argument in current prim that being analysed
aliasedArgsInPrimCall :: AliasMap -> [PrimVarName] -> AliasMap -> [PrimArg]
                            -> Compiler AliasMap
aliasedArgsInPrimCall calleeArgsAliases realParams currentAlias primArgs
    = do
        let combinedAliases1 = combineTwoDS calleeArgsAliases currentAlias
        -- Gather variables in final use
        finals <- foldM (finalArgs realParams) Set.empty primArgs
        -- Then remove them from aliasmap
        return $ removeFromDS finals combinedAliases1


-- Check Arg aliases in one of the prims of a ProcBody.
-- realParams: caller's formal params;
-- (maybeAliasedInput, maybeAliasedOutput, primArgs): argument in current prim
-- that being analysed
aliasedArgsInSimplePrim :: [PrimVarName] -> AliasMap -> [PrimVarName] 
                            -> [PrimArg] -> Compiler AliasMap
aliasedArgsInSimplePrim realParams currentAlias [] primArgs = do
        -- No new aliasing incurred but still need to cleanup final args
        -- Gather variables in final use
        finals <- foldM (finalArgs realParams) Set.empty primArgs
        -- Then remove them from aliasmap
        return $ removeFromDS finals currentAlias
aliasedArgsInSimplePrim realParams currentAlias
                            maybeAliasedVariables primArgs = do
        logAlias $ "      primArgs:           " ++ show primArgs
        logAlias $ "      maybeAliasedVariables:  " 
                                    ++ show maybeAliasedVariables 
        let aliasMap1 = addConnectedGroupToDS maybeAliasedVariables currentAlias
        -- Gather variables in final use
        finals <- foldM (finalArgs realParams) Set.empty primArgs
        -- Then remove them from aliasmap
        return $ removeFromDS finals aliasMap1


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


-- Helper: put final arg into the set
-- Don't add to finalset if the var is a formal parameter in caller's proto
-- realParams: caller's formal params
finalArgs :: [PrimVarName] -> Set PrimVarName -> PrimArg
                -> Compiler (Set PrimVarName)
finalArgs realParams finalSet
          fIn@ArgVar{argVarName=inName,argVarFinal=final} =
    if List.notElem inName realParams && final
    then return $ Set.insert inName finalSet
    else return finalSet
finalArgs _ finalSet _ = return finalSet


----------------------------------------------------------------
--                 Global Level Aliasing Analysis
----------------------------------------------------------------
-- The local one above considers all parameters as aliased, and this global
-- one is to extend that by generating specialized procedures where 
-- some parameters aren't aliased.
-- The code here is to analysis each procedure and list parameters
-- that are interesting for further use (in [Transform.hs]).
-- We consider a parameter is intersting when the alias
-- information of that parameter can help us generate a
-- better version of that procedure. 


mergeMultiSpeczInfo :: [AliasMultiSpeczInfoLocal] -> AliasMultiSpeczInfoLocal
mergeMultiSpeczInfo = List.foldl Set.union Set.empty


-- we say a real param is interesting if it can be updated
-- destructively when it doesn't alias to anything from outside
updateMultiSpeczInfoByPrim :: [PrimVarName]
                    -> (AliasMap, AliasMultiSpeczInfoLocal)
                    -> Placed Prim -> Compiler AliasMultiSpeczInfoLocal
updateMultiSpeczInfoByPrim realParams (aliasMap, multiSpeczInfo) prim =
    case content prim of
        PrimCall spec args -> do
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto _ analysis _) = procImpln calleeDef
            let calleeMultiSpeczInfo = procArgAliasMultiSpeczInfo analysis
            let interestingArgWithCalleeParam = 
                    List.filter (\(arg, param) -> 
                        List.elem param calleeMultiSpeczInfo
                        && isArgVarInteresting aliasMap arg
                    ) (pairArgVarWithParam args calleeProto)
            -- If a variable is in this list more than once, then it should
            -- be removed since it's aliased.
            let interestingArgWithCalleeParam' = 
                    List.filter (\(arg, param) ->
                        let count = 
                                interestingArgWithCalleeParam
                                |> List.filter ((arg ==) . fst) 
                                |> List.length
                        in
                            count == 1
                    ) interestingArgWithCalleeParam
            logAlias $ "interestingArgWithCalleeParam: " 
                            ++ show interestingArgWithCalleeParam'
            let interestingParams = 
                    interestingArgWithCalleeParam'
                    |> List.map (argVarName . fst)
                    |> List.filter (flip List.elem realParams)
            unless (List.null interestingParams) 
                        $ logAlias $ "Found interesting params: " 
                        ++ show interestingParams
            let multiSpeczInfo' = 
                    List.foldr Set.insert multiSpeczInfo interestingParams
            return multiSpeczInfo'
        PrimForeign "lpvm" "mutate" flags args -> do
            let [fIn, _, _, _, _, _, _] = args
            let ArgVar{argVarName=inName} = fIn
            if List.elem inName realParams 
                && isArgVarInteresting aliasMap fIn
            then do 
                logAlias $ "Found interesting param: " ++ show inName
                return $ Set.insert inName multiSpeczInfo
            else return multiSpeczInfo
        _ -> return multiSpeczInfo


-- pair up argument variables of the caller with parameters of the callee
pairArgVarWithParam :: [PrimArg] -> PrimProto -> [(PrimArg, PrimVarName)]
pairArgVarWithParam args proto =
    let formalParamNames = primProtoParamNames proto in
    List.zip args formalParamNames


-- we consider a varibale is interesting when it isn't aliased and not used
-- after this
isArgVarInteresting :: AliasMap -> PrimArg -> Bool
isArgVarInteresting aliasMap 
            ArgVar{argVarName=inName, argVarFinal=final} =
    not (connectedToOthersInDS inName aliasMap) && final 
isArgVarInteresting _aliasMap _ = False


-- Convert the set of interesting params to list
-- The order matters, we keep it the same as the [realParams].
completeMultiSpeczInfo :: [PrimVarName] -> AliasMultiSpeczInfoLocal
                                                -> AliasMultiSpeczInfo
completeMultiSpeczInfo realParams info = 
    List.filter (`Set.member` info) realParams


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
-- The transform part can be found in [Tranform.hs]

-- TODO: reuse cells that are different types but has the same size.
-- TODO: call [GC_free] on large unused dead cells.

updateDeadCellsByPrim :: [PrimVarName] -> AnalysisInfo -> Placed Prim 
                            -> Compiler (AliasMultiSpeczInfoLocal, DeadCells)
updateDeadCellsByPrim realParams (aliasMap, multiSpeczInfo, deadCells) prim =
    case content prim of
        PrimForeign "lpvm" "access" _ args -> do
            -- During analysis, we consider all [realParams] are non-aliased
            deadCells' 
                <- updateDeadCellsByAccessArgs [] (aliasMap, deadCells) args
            return (multiSpeczInfo, deadCells')
        PrimForeign "lpvm" "alloc" _ args  -> do
            let (result, deadCells') =
                    assignDeadCellsByAllocArgs realParams deadCells args
            multiSpeczInfo' <- 
                case result of
                    Nothing -> return multiSpeczInfo
                    Just (selectedCell, possibleCells) -> 
                        if List.elem selectedCell realParams
                        then do
                            -- Mark all [possibleCells] as interesting. Since 
                            -- it trys to avoid [realParams] if possible,
                            -- [possibleCells] here are all from [realParams].
                            -- TODO: we need something better than this. this 
                            -- may create some specialized versions that are 
                            -- identical.
                            logAlias $ "Found interesting parameters in dead "
                                    ++ "cell analysis. " ++ show possibleCells
                            return (possibleCells 
                                |> Set.fromList 
                                |> Set.union multiSpeczInfo)
                        else return multiSpeczInfo
            return (multiSpeczInfo', deadCells')
        _ ->
            return (multiSpeczInfo, deadCells)


-- [PrimArg]
updateDeadCellsByAccessArgs aliasedParams (aliasMap, deadCells) primArgs = do
    -- [struct:type, offset:int, ?member:type2]
    let [struct, _, _] = primArgs
    let ArgVar{argVarName=varName, argVarType=ty, argVarFinal=final} = struct
    if not (connectedToOthersInDS varName aliasMap) && final 
        && List.notElem varName aliasedParams
    then do
        logAlias $ "Found new dead cell: " ++ show varName 
                    ++ " type:" ++ show ty
        return $ Map.alter (\x ->
            (case x of 
                Nothing -> [varName]
                Just cells -> varName:cells)
            |> Just
            ) ty deadCells
    else
        return deadCells


assignDeadCellsByAllocArgs realParams deadCells primArgs =
    -- [size:int, ?struct:type]
    let [_, struct] = primArgs in
    let ArgVar{argVarName=varName, argVarType=ty} = struct in
    case Map.lookup ty deadCells of 
        Nothing    -> (Nothing, deadCells)
        Just cells -> 
            let assigned = 
                    -- Always try to avoid realParams if possible
                    case List.find (`List.notElem` realParams) cells of
                        Just x  -> Just x
                        Nothing -> case cells of 
                            []    -> Nothing
                            (x:_) -> Just x
            in
            case assigned of 
                Nothing -> (Nothing, deadCells)
                Just x  -> 
                    let cells' = List.delete x cells in
                    (Just (x, cells), Map.insert ty cells' deadCells)
