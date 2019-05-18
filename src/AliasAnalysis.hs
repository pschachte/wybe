--  File     : AliasAnalysis.hs
--  Author   : Ting Lu
--  Origin   : Sun Sep 16 16:08:00 EST 2018
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.

module AliasAnalysis (aliasSccBottomUp,
                        currentAliasInfo,
                        areDifferentMaps,
                        maybeAliasPrimArgs,
                        aliasedArgsInSimplePrim,
                        aliasedArgsInPrimCall,
                        mapParamToArgVar) where

import           AST
import           Control.Monad
import           Data.Graph
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Options       (LogSelection (Analysis))
import           Util


----------------------------------------------------------------
--                 Proc Level Aliasing Analysis
----------------------------------------------------------------
-- PROC LEVEL ALIAS ANALYSIS
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


-- | Generate aliasMap for procs
currentAliasInfo :: SCC ProcSpec -> Compiler [AliasMap]
currentAliasInfo (AcyclicSCC single) = do
    def <- getProcDef single
    let (ProcDefPrim _ _ analysis) = procImpln def
    return [procArgAliasMap analysis]
currentAliasInfo procs@(CyclicSCC multi) =
    foldM (\info pspec -> do
        def <- getProcDef pspec
        let (ProcDefPrim _ _ analysis) = procImpln def
        return $ info ++ [procArgAliasMap analysis]
        ) [] multi


-- XXX aliasProcBottomUp :: ProcSpec -> Compiler a
aliasProcBottomUp :: ProcSpec -> Compiler Bool
aliasProcBottomUp pspec = do
    logAlias $ replicate 50 '-'
    logAlias $ "Alias analysis proc (Bottom-up): " ++ show pspec
    logAlias $ replicate 50 '-'

    oldDef <- getProcDef pspec
    let (ProcDefPrim _ _ oldAnalysis) = procImpln oldDef
    -- Update alias analysis info to this proc
    updateProcDefM checkEscapeDef pspec
    -- Get the new analysis info from the updated proc
    newDef <- getProcDef pspec
    let (ProcDefPrim _ _ newAnalysis) = procImpln newDef
    -- And compare if the alias map changed.
    return $ areDifferentMaps (procArgAliasMap oldAnalysis) (procArgAliasMap newAnalysis)
    -- ^XXX wrong way to do this. Need to change type signatures of a bunch of
    -- functions start from checkEscapeDef which is called by updateProcDefM


-- Check if any argument become stale in this (not inlined) proc call
-- Return updated ProcDef and a flag (indicating if proc analysis info changed)
-- XXX checkEscapeDef :: ProcDef -> Compiler (ProcDef, a)
checkEscapeDef :: ProcDef -> Compiler ProcDef
checkEscapeDef def
    | not (procInline def) = do
        let (ProcDefPrim caller body oldAnalysis) = procImpln def
        logAlias $ show caller
        -- (1) Analysis of current caller's prims
        alias1 <- checkEscapePrims caller body []
        aliaseMap1 <- aliasedByPrims caller body initUnionFind
        -- (2) Analysis of caller's bodyFork
        alias2 <- checkEscapeFork caller body alias1
        -- Update body while checking alias incurred by bodyfork
        aliaseMap2 <- aliasedByFork caller body aliaseMap1
        -- (3) Clean up summary of aliases by removing phantom params
        let nonePhantomParams = protoNonePhantomParams caller
        -- ^nonePhantomParams is a list of formal params of this caller
        let aliaseMap3 = Map.filterWithKey (\k _ -> List.elem
                                    k nonePhantomParams) aliaseMap2
        -- Some logging
        logAlias $ "\n^^^  aliases (int pair):     " ++ show alias2
        logAlias $ "^^^  after analyse prims:    " ++ show aliaseMap1
        logAlias $ "^^^  after analyse forks:    " ++ show aliaseMap2
        logAlias $ "^^^  alias of formal params: " ++ show aliaseMap3
        -- (4) Update proc analysis with new aliasPairs
        let newAnalysis = oldAnalysis {
                            procArgAliases = alias2,
                            procArgAliasMap = aliaseMap3
                        }
        return $ def { procImpln = ProcDefPrim caller body newAnalysis }
checkEscapeDef def = return def -- ^XXX return (def, False)


-- Check alias created by prims of caller proc
aliasedByPrims :: PrimProto -> ProcBody -> AliasMap -> Compiler AliasMap
aliasedByPrims caller body initAliases = do
    let nonePhantomParams = protoNonePhantomParams caller
    let prims = bodyPrims body
    -- Analyse simple prims:
    -- (only process alias pairs incurred by move, access, cast)
    logAlias "\nAnalyse prims (aliasedByPrims):    "
    let aliasMap = List.foldr newUfItem initAliases nonePhantomParams
    let nonePhantomParams = protoNonePhantomParams caller
    foldM (aliasedByPrim nonePhantomParams) aliasMap prims


-- Build up alias pairs triggerred by proc calls
-- nonePhantomParams: caller's formal params
aliasedByPrim :: [PrimVarName] -> AliasMap -> Placed Prim -> Compiler AliasMap
aliasedByPrim nonePhantomParams aliasMap prim =
    case content prim of
        PrimCall spec args -> do
            -- | Analyse proc calls
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto _ analysis) = procImpln calleeDef
            let calleeParamAliases = procArgAliasMap analysis
            logAlias $ "--- call          " ++ show spec ++" (callee): "
            logAlias $ "" ++ show calleeProto
            logAlias $ "PrimCall args:    " ++ show args
            let paramArgMap = mapParamToArgVar calleeProto args
            -- calleeArgsAliasMap is the alias map of actual arguments passed
            -- into callee
            let calleeArgsAliases =
                    Map.foldrWithKey (transformUfKey paramArgMap)
                        initUnionFind calleeParamAliases
            combined <- aliasedArgsInPrimCall calleeArgsAliases nonePhantomParams
                                    aliasMap args
            logAlias $ "calleeArgsAliases:" ++ show calleeArgsAliases
            logAlias $ "current aliasMap: " ++ show aliasMap
            logAlias $ "combined:         " ++ show combined
            return combined
        _ -> do
            -- | Analyse simple prims
            logAlias $ "--- simple prim:  " ++ show prim
            maybeAliasPrimArgs (content prim) >>=
                aliasedArgsInSimplePrim nonePhantomParams aliasMap


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
aliasedByFork :: PrimProto -> ProcBody -> AliasMap -> Compiler AliasMap
aliasedByFork caller body aliasMap = do
    logAlias "\nAnalyse forks (aliasedByFork):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logAlias ">>> Forking:"
            foldM (\amap currBody -> do
                    aliasedByPrims caller currBody amap >>=
                        aliasedByFork caller currBody
                ) aliasMap fBodies
        _ -> do
            -- NoFork: analyse prims done
            logAlias ">>> No fork."
            return aliasMap


-- Build up maybe alised inputs and outputs triggerred by move, access, cast
-- instructions.
-- Not to compute aliasing from mutate instructions with the assumption that we
-- always try to do nondestructive update.
-- Returned triple ([PrimVarName], [PrimVarName], [PrimArg]) is
-- (maybeAliasedInput, maybeAliasedOutput, primArgs)
maybeAliasPrimArgs :: Prim -> Compiler ([PrimVarName], [PrimVarName], [PrimArg])
maybeAliasPrimArgs (PrimForeign _ "access" _ args) = _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign _ "cast" _ args)   = _maybeAliasPrimArgs args
maybeAliasPrimArgs (PrimForeign _ "move" _ args)   = _maybeAliasPrimArgs args
maybeAliasPrimArgs prim                            = return ([],[], primArgs prim)


-- Helper function for the above maybeAliasPrimArgs function
_maybeAliasPrimArgs :: [PrimArg]
                        -> Compiler ([PrimVarName], [PrimVarName], [PrimArg])
_maybeAliasPrimArgs args = do
    let inputArgs = List.filter (argVarIsFlowDirection FlowIn) args
    let outputArgs = List.filter (argVarIsFlowDirection FlowOut) args
    escapedInputs <- foldM (argsOfProcProto inArgVar2) [] inputArgs
    escapedVia <- foldM (argsOfProcProto outArgVar2) [] outputArgs
    return (escapedInputs, escapedVia, args)


-- Helper: compare if two AliasMaps are different
-- Have to ensure the aliasing map is canonical by converting the map to Alias
-- Pairs because the root could be different in two maps whereas the alias info
-- are the same
areDifferentMaps :: AliasMap -> AliasMap -> Bool
areDifferentMaps aliasMap1 aliasMap2 =
    let aliasPair1 = aliasMapToAliasPairs aliasMap1
        aliasPair2 = aliasMapToAliasPairs aliasMap2
    in aliasPair1 /= aliasPair2


-- Helper: get argvar names of aliased args of the prim
argsOfProcProto :: (PrimArg -> Compiler (Maybe PrimVarName))
                    -> [PrimVarName] -> PrimArg -> Compiler [PrimVarName]
argsOfProcProto varNameGetter escapedVars arg = do
    nm <- varNameGetter arg
    case nm of
        Just name -> return (name : escapedVars)
        Nothing   -> return escapedVars


-- Check Arg aliases in one of proc calls inside a ProcBody
-- nonePhantomParams: caller's formal params
-- primArgs: argument in current prim that being analysed
aliasedArgsInPrimCall :: AliasMap -> [PrimVarName] -> AliasMap -> [PrimArg]
                            -> Compiler AliasMap
aliasedArgsInPrimCall calleeArgsAliases nonePhantomParams currentAlias primArgs
    = do
        let combinedAliases1 = combineUf calleeArgsAliases currentAlias
        -- Gather variables in final use
        finals <- foldM (finalArgs nonePhantomParams) Set.empty primArgs
        -- Then remove them from aliasmap
        return $ removeFromUf finals combinedAliases1


-- Check Arg aliases in one of the prims of a ProcBody.
-- nonePhantomParams: caller's formal params;
-- (maybeAliasedInput, maybeAliasedOutput, primArgs): argument in current prim
-- that being analysed
aliasedArgsInSimplePrim :: [PrimVarName] -> AliasMap
                            -> ([PrimVarName], [PrimVarName], [PrimArg])
                            -> Compiler AliasMap
aliasedArgsInSimplePrim nonePhantomParams currentAlias ([],[], primArgs) = do
        -- No new aliasing incurred but still need to cleanup final args
        -- Gather variables in final use
        finals <- foldM (finalArgs nonePhantomParams) Set.empty primArgs
        -- Then remove them from aliasmap
        return $ removeFromUf finals currentAlias
aliasedArgsInSimplePrim nonePhantomParams currentAlias
    (maybeAliasedInput, maybeAliasedOutput, primArgs) = do
        let aliases = cartProd maybeAliasedInput maybeAliasedOutput
        let aliasMap1 = List.foldr (\(inArg, outArg) aMap ->
                            uniteUf aMap inArg outArg) currentAlias aliases
        -- Gather variables in final use
        finals <- foldM (finalArgs nonePhantomParams) Set.empty primArgs
        -- Then remove them from aliasmap
        return $ removeFromUf finals aliasMap1


-- Helper: map arguments in callee proc to its formal parameters so we can get
-- alias info of the arguments
mapParamToArgVar :: PrimProto -> [PrimArg] -> Map PrimVarName PrimVarName
mapParamToArgVar proto args =
    let formalParamNames = primProtoParamNames proto
        paramArgPairs = _zipParamToArgVar formalParamNames args
    in Map.fromList paramArgPairs


-- Helper: zip formal param to PrimArg with ArgVar data constructor
_zipParamToArgVar :: [PrimVarName] -> [PrimArg] -> [(PrimVarName, PrimVarName)]
_zipParamToArgVar (p:params) (ArgVar nm _ _ _ _:args) =
    (p, nm):_zipParamToArgVar params args
_zipParamToArgVar (_:params) (_:args) = _zipParamToArgVar params args
_zipParamToArgVar [] _ = []
_zipParamToArgVar _ [] = []


-- Helper: put final arg into the set
-- Don't add to finalset if the var is a formal parameter in caller's proto
-- nonePhantomParams: caller's formal params
finalArgs :: [PrimVarName] -> Set PrimVarName -> PrimArg
                -> Compiler (Set PrimVarName)
finalArgs nonePhantomParams finalSet fIn@(ArgVar inName _ _ _ final) =
    if List.notElem inName nonePhantomParams && final
    then return $ Set.insert inName finalSet
    else return finalSet
finalArgs _ finalSet _ = return finalSet


-- |Log a message, if we are logging optimisation activity.
logAlias :: String -> Compiler ()
logAlias = logMsg Analysis


----------------------------------------------------------------
--
-- Original Alias Analysis using Int pairs to represent alias info
-- TODO: to be deleted
--
----------------------------------------------------------------
-- Check alias created by prims of caller proc
checkEscapePrims :: PrimProto -> ProcBody -> [AliasPair]
                    -> Compiler [AliasPair]
checkEscapePrims caller body callerAlias = do
    let paramNames = primProtoParamNames caller
    let prims = bodyPrims body

    -- First pass (only process alias pairs incurred by move, mutate, access,
    -- cast)
    -- logAlias $ "\nAnalyse prims (checkEscapePrims): \n    "
    --             ++ List.intercalate "\n    " (List.map show prims)

    (bodyAliases, aliasPairs) <-
        foldM (\(bodyAliasedVars, pairs) prim -> do
                args <- escapablePrimArgs $ content prim
                (bodyAliasedVars', pairs') <-
                    aliasPairsFromArgs bodyAliasedVars args pairs
                return (bodyAliasedVars', pairs')
                ) (paramNames, []) prims
    -- logAlias $ "    ^^^ Aliased vars by prims: " ++ show bodyAliases
    let aliasPairs' =
            removeDupTuples $ transitiveTuples $ removeDupTuples aliasPairs
    let aliasSimplePrims = pruneTuples aliasPairs' (List.length paramNames)

    -- Second pass (handle alias pairs incurred by proc calls within
    -- caller)
    aliasNames <- foldM (escapeByProcCalls callerAlias) [] prims
    -- logAlias $ "    ^^^ Aliased vars by proc calls: " ++ show aliasNames
    -- convert alias name pairs to index pairs
    let aliasByProcCalls = _aliasNamesToPairs caller aliasNames

    let allPairs = aliasSimplePrims ++ aliasByProcCalls
    let allPairs' = removeDupTuples allPairs

    -- alias pairs are transitive
    let expandedPairs = removeDupTuples $ transitiveTuples allPairs'

    return $ callerAlias ++ expandedPairs


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
checkEscapeFork :: PrimProto -> ProcBody -> [AliasPair]
                    -> Compiler [AliasPair]
checkEscapeFork caller body aliases = do
    let fork = bodyFork body
    -- logAlias "\nAnalyse forks (checkEscapeFork):"
    case fork of
        PrimFork _ _ _ fBodies -> do
            -- logAlias "Forking:"
            aliases' <-
                foldM (\as currBody -> do
                        as' <- checkEscapePrims caller currBody as
                        let as1 = removeDupTuples $ transitiveTuples (as ++ as')
                        checkEscapeFork caller currBody as1
                    ) [] fBodies
            let aliases2
                    = removeDupTuples $ transitiveTuples (aliases ++ aliases')
            return aliases2
        _ -> do
            -- NoFork: analyse prims done
            -- logAlias "No fork."
            return aliases


-- Check Arg escape in one prim of prims of a ProcBody
aliasPairsFromArgs :: [PrimVarName] -> [PrimArg] -> [AliasPair]
                        -> Compiler ([PrimVarName], [AliasPair])
aliasPairsFromArgs bodyAliases [] pairs = return (bodyAliases, pairs)
aliasPairsFromArgs bodyAliases args pairs = do
    let inputArgs = List.filter (argVarIsFlowDirection FlowIn) args
    let outputArgs = List.filter (argVarIsFlowDirection FlowOut) args
    escapedInputs <- foldM (argsOfProcProto inArgVar2) [] inputArgs
    escapedVia <- foldM (argsOfProcProto outArgVar2) [] outputArgs
    let (bodyAliases1, inIndices) = _mapVarNameIdx bodyAliases escapedInputs
        (bodyAliases2, outIndices) = _mapVarNameIdx bodyAliases1 escapedVia
    return (bodyAliases2, cartProd inIndices outIndices ++ pairs)


-- Build up alias pairs triggerred by proc calls
escapeByProcCalls :: [AliasPair]
                    -> [(PrimVarName, PrimVarName)]
                    -> Placed Prim
                    -> Compiler [(PrimVarName, PrimVarName)]
escapeByProcCalls callerAlias aliasNames prim =
    case content prim of
        PrimCall spec args -> do
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto body analysis) = procImpln calleeDef
            let calleeAlias = procArgAliases analysis
            -- logAlias $ "\n    --- call " ++ show spec ++" (callee): "
            -- logAlias $ "    " ++ show calleeProto
            -- logAlias $ "    PrimCall args: " ++ show args
            -- logAlias $ "    callerAlias: " ++ show callerAlias
            -- logAlias $ "    calleeAlias: " ++ show calleeAlias
            let aliasNames' = aliasPairsToVarNames args
                                    (callerAlias ++ calleeAlias)
            -- logAlias $ "    names: " ++ show aliasNames'
            return $ aliasNames ++ aliasNames'
        _ ->
            return aliasNames


-- Build up alias pairs triggerred by move, mutate, access, cast instructions
escapablePrimArgs :: Prim -> Compiler [PrimArg]
escapablePrimArgs (PrimForeign _ "move" _ args)   = return args
-- escapablePrimArgs (PrimForeign _ "mutate" _ args) = return args
escapablePrimArgs (PrimForeign _ "access" _ args) = return args
escapablePrimArgs (PrimForeign _ "cast" _ args)   = return args
escapablePrimArgs _                               = return []


-- Helper: convert alias index pairs to var name pairs
aliasPairsToVarNames :: [PrimArg] -> [AliasPair]
                            -> [(PrimVarName, PrimVarName)]
aliasPairsToVarNames primCallArgs =
    List.foldr (\(p1,p2) aliasNames ->
        let v1 = primCallArgs !! p1
            v2 = primCallArgs !! p2
        in case (v1,v2) of
                (ArgVar n1 _ _ _ _, ArgVar n2 _ _ _ _) ->
                    (n1, n2) : aliasNames
                _ -> aliasNames
        ) []

-- Helper: convert aliased var names pair to arg index pair
_aliasNamesToPairs :: PrimProto -> [(PrimVarName, PrimVarName)] -> [AliasPair]
_aliasNamesToPairs caller aliasNames =
    let paramNames = primProtoParamNames caller
    in List.foldr (\(n1, n2) pairs ->
        let idexes = (List.elemIndex n1 paramNames, List.elemIndex n2 paramNames)
        in case idexes of
            (Just idx1, Just idx2) -> (idx1, idx2):pairs
            _                      -> pairs
        ) [] aliasNames


_mapVarNameIdx :: [PrimVarName] -> [PrimVarName] -> ([PrimVarName], [Int])
_mapVarNameIdx bodyAliases =
    List.foldl (
        \(varNames, indices) nm ->
            let elemIdx = List.elemIndex nm varNames
            in case elemIdx of
                Just idx -> (bodyAliases, idx : indices)
                Nothing ->
                    let bodyAliases' = bodyAliases ++ [nm]
                        newIdx = List.length bodyAliases' - 1
                    in (bodyAliases', newIdx : indices)
    ) (bodyAliases, [])


-- Helper: check if FlowIn variable is aliased after previous proc calls
isVarAliased :: PrimVarName -> [(PrimVarName, PrimVarName)] -> Bool
isVarAliased varName [] = False
isVarAliased varName ((n1,n2):as) =
    (varName == n1 || varName == n2) || isVarAliased varName as
