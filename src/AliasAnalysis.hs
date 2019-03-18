--  File     : AliasAnalysis.hs
--  Author   : Ting Lu
--  Origin   : Sun Sep 16 16:08:00 EST 2018
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.

module AliasAnalysis (aliasSccBottomUp, isVarAliased, aliasPairsToVarNames)
    where

import           AST
import           Control.Monad
import           Data.Graph
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Options       (LogSelection (Optimise))
import           Util


----------------------------------------------------------------
--                     Escape Analysis
----------------------------------------------------------------
aliasSccBottomUp :: SCC ProcSpec -> Compiler ()
aliasSccBottomUp procs = mapM_ aliasProcBottomUp $ sccElts procs

aliasProcBottomUp :: ProcSpec -> Compiler ()
aliasProcBottomUp pspec = do
    updateProcDefM (checkEscapeDef pspec) pspec
    return ()


-- Check any argument become stale after this proc call if this
-- proc is not inlined
checkEscapeDef :: ProcSpec -> ProcDef -> Compiler ProcDef
checkEscapeDef spec def
    | not (procInline def) = do
        let (ProcDefPrim caller body analysis) = procImpln def
        logAlias $ "\n>>> Alias analysis (Bottom-up): " ++ show spec
        logAlias $ show caller

        -- Analysis of current caller's prims
        alias1 <- checkEscapePrims caller body []
        (bodyPrimsAliases, finalSet1) <-
            aliasedByPrims caller body (initUnionFind, Set.empty)

        -- Analysis of caller's bodyFork
        alias2 <- checkEscapeFork caller body alias1
        (bodyForkAliases, finalSet2) <-
            aliasedByFork caller body (bodyPrimsAliases, finalSet1)

        -- Clean up summary of aliases by removing phantom params
        let nonePhantomParams = protoNonePhantomParams caller
        let bodyForkAliases' = Map.foldrWithKey (filterUfByKey nonePhantomParams)
                                        initUnionFind bodyForkAliases
        let (totalAliases, _) = Map.foldrWithKey (convertUfRoot finalSet2)
                                (initUnionFind, Map.empty) bodyForkAliases'

        -- Update proc analysis with new aliasPairs
        let analysis' = analysis {
                            procArgAliases = alias2,
                            procArgAliasMap = totalAliases
                        }
        logAlias $ ">>>  aliases: " ++ show alias2
        logAlias $ ">>>  analyse prims: " ++ show bodyPrimsAliases
        logAlias $ ">>>  and analyse forking: " ++ show bodyForkAliases
        logAlias $ ">>>  (pruned)': " ++ show bodyForkAliases'
        logAlias $ ">>>  finalset: " ++ show finalSet2
        logAlias $ ">>>  (final args removed)': " ++ show totalAliases

        return def { procImpln = ProcDefPrim caller body analysis'}

checkEscapeDef _ def = return def


-- Check alias created by prims of caller proc
aliasedByPrims :: PrimProto -> ProcBody -> (AliasMap, Set PrimVarName)
                    -> Compiler (AliasMap, Set PrimVarName)
aliasedByPrims caller body (initAliases, initFinalSet) = do
    let nonePhantomParams = protoNonePhantomParams caller
    let prims = bodyPrims body

    -- Analyse simple prims:
    -- (only process alias pairs incurred by move, mutate, access, cast)
    logAlias "\nAnalyse prims (aliasedByPrims):    "
                -- ++ List.intercalate "\n    " (List.map show prims)
    let aliasMap = List.foldr newUfItem initAliases nonePhantomParams
    primsAliases <- foldM aliasedByPrim (aliasMap, initFinalSet) prims
    logAlias $ "\n    ^^^ Aliased vars by prims: " ++ show primsAliases
    return primsAliases

-- Build up alias pairs triggerred by proc calls
aliasedByPrim :: (AliasMap, Set PrimVarName) -> Placed Prim
                    -> Compiler (AliasMap, Set PrimVarName)
aliasedByPrim (aliasMap, finalSet) prim =
    case content prim of
        PrimCall spec args -> do
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto body analysis) = procImpln calleeDef
            let calleeParamAliases = procArgAliasMap analysis
            logAlias $ "\n    --- call " ++ show spec ++" (callee): "
            logAlias $ "    " ++ show calleeProto
            logAlias $ "    PrimCall args: " ++ show args
            logAlias $ "    current aliasMap: " ++ show aliasMap
            logAlias $ "    calleeAlias: " ++ show calleeParamAliases
            let paramArgMap = mapParamToArgVar calleeProto args

            -- calleeArgsAliasMap is the alias map of actual arguments
            let calleeArgsAliases = Map.foldrWithKey (convertUfKey paramArgMap)
                                            initUnionFind calleeParamAliases
            let combinedAliases = combineUf calleeArgsAliases aliasMap
            return (combinedAliases, _finalArgs args finalSet)
        _ -> do
            logAlias "\n    --- none-primcall:"
            logAlias $ "    " ++ show prim
            -- return aliasMap
            escapablePrimArgs (content prim) >>=
                aliasedArgsByPrim (aliasMap, finalSet)


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
aliasedByFork :: PrimProto -> ProcBody -> (AliasMap, Set PrimVarName)
                    -> Compiler (AliasMap, Set PrimVarName)
aliasedByFork caller body (aliasMap, finalSet) = do
    logAlias "\nAnalyse forks (aliasedByFork):"
    case bodyFork body of
        PrimFork _ _ _ fBodies -> do
            logAlias "Forking:"
            foldM (\(amap, fset) currBody -> do
                    (amap', fset') <-
                        aliasedByPrims caller currBody (initUnionFind, Set.empty)
                    (amap'', fset'') <-
                        aliasedByFork caller currBody (amap', fset')
                    let combinedAliases = combineUf amap'' amap
                    let combinedFinalSet = Set.union fset fset''
                    return (combinedAliases, combinedFinalSet)
                ) (aliasMap, finalSet) fBodies
        _ -> do
            -- NoFork: analyse prims done
            logAlias "No fork."
            return (aliasMap, finalSet)


-- Build up alias pairs triggerred by move, mutate, access, case instructions
escapablePrimArgs :: Prim -> Compiler [PrimArg]
escapablePrimArgs (PrimForeign _ "move" _ args)   = return args
escapablePrimArgs (PrimForeign _ "mutate" _ args) = return args
escapablePrimArgs (PrimForeign _ "access" _ args) = return args
escapablePrimArgs (PrimForeign _ "cast" _ args)   = return args
escapablePrimArgs _                               = return []


-- Helper: get argvar names of aliased args of the prim
argsOfProcProto :: (PrimArg -> Compiler (Maybe PrimVarName))
                    -> [PrimVarName] -> PrimArg -> Compiler [PrimVarName]
argsOfProcProto varNameGetter escapedVars arg = do
    nm <- varNameGetter arg
    case nm of
        Just name -> return (name : escapedVars)
        Nothing   -> return escapedVars


-- Check Arg aliases in one of the prims of a ProcBody
-- args: argument in current prim that being analysed
aliasedArgsByPrim :: (AliasMap, Set PrimVarName) -> [PrimArg]
                        -> Compiler (AliasMap, Set PrimVarName)
aliasedArgsByPrim (aliasMap, finalSet) [] = return (aliasMap, finalSet)
aliasedArgsByPrim (aliasMap, finalSet) args = do
    let inputArgs = List.filter (argVarIsFlowDirection FlowIn) args
    let outputArgs = List.filter (argVarIsFlowDirection FlowOut) args
    escapedInputs <- foldM (argsOfProcProto inArgVar2) [] inputArgs
    escapedVia <- foldM (argsOfProcProto outArgVar2) [] outputArgs
    let aliases = cartProd escapedInputs escapedVia
    let aliasMap' = List.foldr (\(inArg, outArg) aMap ->
                        uniteUf aMap inArg outArg) aliasMap aliases
    return (aliasMap', _finalArgs args finalSet)


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


-- Helper: change mutate destructive flag to false if FlowIn variable is aliased
_updateMutateForAlias :: [(PrimVarName, PrimVarName)] -> [PrimArg] -> [PrimArg]
_updateMutateForAlias aliasNames
    [fIn@(ArgVar inName _ _ _ final), fOut@(ArgVar outName _ _ _ _), size,
    offset, ArgInt des typ, mem] =
        if isVarAliased inName aliasNames
            then [fIn, fOut, size, offset, ArgInt 0 typ, mem]
            else [fIn, fOut, size, offset, ArgInt des typ, mem]
_updateMutateForAlias _ args = args


-- Helper: check if FlowIn variable is aliased after previous proc calls
isVarAliased :: PrimVarName -> [(PrimVarName, PrimVarName)] -> Bool
isVarAliased varName [] = False
isVarAliased varName ((n1,n2):as) =
    (varName == n1 || varName == n2) || isVarAliased varName as


_finalArgs :: [PrimArg] -> Set PrimVarName -> Set PrimVarName
_finalArgs [fIn@(ArgVar inName _ _ _ final), _, _, _, _, _] finalSet =
    Set.insert inName finalSet
_finalArgs _ finalSet = finalSet


-- |Log a message, if we are logging optimisation activity.
logAlias :: String -> Compiler ()
logAlias = logMsg Optimise


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
    logAlias $ "\nAnalyse prims (checkEscapePrims): \n    "
                ++ List.intercalate "\n    " (List.map show prims)

    (bodyAliases, aliasPairs) <-
        foldM (\(bodyAliasedVars, pairs) prim -> do
                args <- escapablePrimArgs $ content prim
                (bodyAliasedVars', pairs') <-
                    aliasPairsFromArgs bodyAliasedVars args pairs
                return (bodyAliasedVars', pairs')
                ) (paramNames, []) prims
    logAlias $ "    ^^^ Aliased vars by prims: " ++ show bodyAliases
    let aliasPairs' =
            removeDupTuples $ transitiveTuples $ removeDupTuples aliasPairs
    let aliasSimplePrims = pruneTuples aliasPairs' (List.length paramNames)

    -- Second pass (handle alias pairs incurred by proc calls within
    -- caller)
    aliasNames <- foldM (escapeByProcCalls callerAlias) [] prims
    logAlias $ "    ^^^ Aliased vars by proc calls: " ++ show aliasNames
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
    logAlias "\nAnalyse forks (checkEscapeFork):"
    case fork of
        PrimFork _ _ _ fBodies -> do
            logAlias "Forking:"
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
            logAlias "No fork."
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
            logAlias $ "\n    --- call " ++ show spec ++" (callee): "
            logAlias $ "    " ++ show calleeProto
            logAlias $ "    PrimCall args: " ++ show args
            logAlias $ "    callerAlias: " ++ show callerAlias
            logAlias $ "    calleeAlias: " ++ show calleeAlias
            let aliasNames' = aliasPairsToVarNames args
                                    (callerAlias ++ calleeAlias)
            logAlias $ "    names: " ++ show aliasNames'
            return $ aliasNames ++ aliasNames'
        _ ->
            return aliasNames

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
