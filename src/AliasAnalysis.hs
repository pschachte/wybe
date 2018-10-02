--  File     : AliasAnalysis.hs
--  Author   : Ting Lu
--  Origin   : Sun Sep 16 16:08:00 EST 2018
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.

module AliasAnalysis (aliasSccBottomUp) where

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
    logAlias "\n>>> Alias analysis (Bottom-up):"
    updateProcDefM (checkEscapeDef pspec) pspec
    return ()


-- Helper: normalise alias pairs in order
normalise :: Ord a => (a,a) -> (a,a)
normalise t@(x,y)
    | y < x    = (y,x)
    | otherwise = t

-- Helper: then remove duplicated alias pairs
removeDupTuples :: Ord a => [(a,a)] -> [(a,a)]
removeDupTuples =
    List.map List.head . List.group . List.sort . List.map normalise

-- Helper: prune list of tuples with int larger than the range
pruneTuples :: Ord a => [(a,a)] -> a -> [(a,a)]
pruneTuples tuples upperBound =
    List.foldr (\(t1, t2) tps ->
                if t1 < upperBound && t2 < upperBound then (t1, t2):tps
                else tps) [] tuples

-- Helper: to expand alias pairs
-- e.g. Aliases [(1,2),(2,3),(3,4)] is expanded to
-- [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
-- items in pairs are sorted already
transitiveTuples :: [(Int,Int)] -> [(Int,Int)]
transitiveTuples [] = []
transitiveTuples pairs =
    let loBound = List.foldr (\(p1,p2) bound ->
                                if p1 < bound then p1
                                else bound) 0 pairs
        upBound = List.foldr (\(p1,p2) bound ->
                    if p2 > bound then p2
                    else bound) 0 pairs
        adj = buildG (loBound, upBound) pairs
        undirectedAdj = buildG (loBound, upBound) (edges adj ++ reverseE adj)
        elements = vertices undirectedAdj
    in List.foldr (\vertex tuples ->
        let reaches = reachable undirectedAdj vertex
            vertexPairs = [(vertex, r) | r <- reaches, r /= vertex]
        in vertexPairs ++ tuples
        ) [] elements


-- Helper: Cartesian product of escaped FlowIn vars to proc output
_cartProd :: [a] -> [a] -> [(a, a)]
_cartProd ins outs = [(i, o) | i <- ins, o <- outs]


-- Check any argument become stale after this proc call if this
-- proc is not inlined
checkEscapeDef :: ProcSpec -> ProcDef -> Compiler ProcDef
checkEscapeDef spec def
    | not (procInline def) = do
        let (ProcDefPrim caller body analysis) = procImpln def
        logAlias $ "****** " ++ show spec ++ " " ++ show caller

        -- Analysis of caller's prims
        (prims, alias1) <- checkEscapePrims caller body []

        -- Update body prims with correct destructive flag
        let body1 = body { bodyPrims = prims }

        -- Analysis of caller's bodyFork
        (body2, alias2) <- checkEscapeFork caller body1 alias1

        -- Update proc analysis with new aliasPairs
        let analysis' = analysis { procArgAliases = alias2 }
        logAlias $ "****** alias2: " ++ show alias2

        return def { procImpln = ProcDefPrim caller body2 analysis'}

checkEscapeDef _ def = return def


-- Check alias created by prims of caller proc
checkEscapePrims :: PrimProto -> ProcBody -> [AliasPair]
                    -> Compiler([Placed Prim], [AliasPair])
checkEscapePrims caller body callerAlias = do
    let paramNames = primProtoParamNames caller
    let prims = bodyPrims body

    -- First pass (only process alias pairs incurred by move and mutate)
    logAlias $ "\n    " ++ List.intercalate "\n    " (List.map show prims)

    (bodyAliases, aliasPairs) <- foldM
                    (\(bodyAliasedVars, pairs) prim -> do
                        args <- escapablePrimArgs $ content prim
                        (bodyAliasedVars', pairs') <- aliasPairsFromArgs bodyAliasedVars args pairs
                        return (bodyAliasedVars', pairs')
                        ) (paramNames, []) prims
    logAlias $ "^^^ Aliased vars by prims: " ++ show bodyAliases
    let aliasPairs' = removeDupTuples $ transitiveTuples $ removeDupTuples aliasPairs
    let prunedPairs = pruneTuples aliasPairs' (List.length paramNames)

    -- Second pass (handle alias pairs incurred by proc calls within
    -- caller)
    (prims', aliasNames) <- foldM (\(ps, as) prim ->
                                escapeByProcCalls (ps, as) prim callerAlias)
                                    ([], []) prims
    logAlias $ "^^^ Aliased vars by proc calls: " ++ show aliasNames

    -- convert alias name pairs to index pairs
    let aliasByProcCalls = _aliasNamesToPairs caller aliasNames
    let allPairs = prunedPairs ++ aliasByProcCalls
    let allPairs' = removeDupTuples allPairs

    -- alias pairs are transitive
    let expandedPairs = removeDupTuples $ transitiveTuples allPairs'

    return (prims', callerAlias ++ expandedPairs)


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
checkEscapeFork :: PrimProto -> ProcBody -> [AliasPair]
                    -> Compiler(ProcBody, [AliasPair])
checkEscapeFork caller body aliases = do
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            (fBodies', aliases') <-
                foldM (\(bs, as) currBody -> do
                        (ps, as') <- checkEscapePrims caller currBody as
                        let currBody1 = currBody { bodyPrims = ps }
                        let as1 = removeDupTuples $ transitiveTuples (as ++ as')
                        (currBody2, as2) <- checkEscapeFork caller currBody1 as1
                        return (bs ++ [currBody2], as2)
                    ) ([], []) fBodies
            let aliases2 = removeDupTuples $ transitiveTuples (aliases ++ aliases')
            return (body { bodyFork = fork {forkBodies=fBodies'} }, aliases2)
        _ -> do
            -- NoFork: analyse prims directly
            (ps, as') <- checkEscapePrims caller body aliases
            let as2 = removeDupTuples $ transitiveTuples (aliases ++ as')
            let body2 = body { bodyPrims = ps }
            return (body2, as2)


-- For first pass:
-- Build up alias pairs triggerred by move and mutate instructions
escapablePrimArgs :: Prim -> Compiler [PrimArg]
escapablePrimArgs (PrimForeign _ "move" _ args)   = return args
escapablePrimArgs (PrimForeign _ "mutate" _ args) = return args
escapablePrimArgs (PrimForeign _ "access" _ args) = return args
escapablePrimArgs (PrimForeign _ "cast" _ args)   = return args
escapablePrimArgs _                               = return []


-- get argvar names of aliased args of the prim
argsOfProcProto :: (PrimArg -> Compiler PrimVarName) -> [PrimArg]
                    -> Compiler [PrimVarName]
argsOfProcProto varNameGetter =
    foldM (\es arg -> do
            nm <- varNameGetter arg
            return (nm : es)) []


-- Check Arg escape in one prim of prims of a ProcBody
aliasPairsFromArgs :: [PrimVarName] -> [PrimArg] -> [AliasPair]
                        -> Compiler ([PrimVarName], [AliasPair])
aliasPairsFromArgs bodyAliases [] pairs = return (bodyAliases, pairs)
aliasPairsFromArgs bodyAliases args pairs = do
    let inputArgs = List.filter (argVarIsFlowDirection FlowIn) args
    let outputArgs = List.filter (argVarIsFlowDirection FlowOut) args
    escapedInputs <- argsOfProcProto inArgVar2 inputArgs
    escapedVia <- argsOfProcProto outArgVar2 outputArgs
    let (bodyAliases1, inIndices) = _mapVarNameIdx bodyAliases escapedInputs
        (bodyAliases2, outIndices) = _mapVarNameIdx bodyAliases1 escapedVia
    return (bodyAliases2, _cartProd inIndices outIndices ++ pairs)

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


-- For second pass:
-- Build up alias pairs triggerred by proc calls
-- Also update destructive flag in mutate prims following proc calls
escapeByProcCalls :: ([Placed Prim], [(PrimVarName, PrimVarName)])
                    -> Placed Prim
                    -> [AliasPair]
                    -> Compiler ([Placed Prim], [(PrimVarName, PrimVarName)])
escapeByProcCalls (prims, aliasNames)
    (Placed (PrimForeign lang "mutate" flags args) pos) _ =
        return (prims ++ [Placed (PrimForeign lang "mutate" flags args') pos],
            aliasNames)
                where args' = _updateMutateForAlias aliasNames args
escapeByProcCalls (prims, aliasNames)
    (Unplaced (PrimForeign lang "mutate" flags args)) _ =
        return (prims ++ [Unplaced (PrimForeign lang "mutate" flags args')],
            aliasNames)
                where args' = _updateMutateForAlias aliasNames args
escapeByProcCalls (prims, aliasNames) prim callerAlias =
    case content prim of
        PrimCall spec args -> do
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto body analysis) = procImpln calleeDef
            let calleeAlias = procArgAliases analysis
            logAlias $ "\ncall " ++ show spec ++" (callee): " ++ show calleeProto
            logAlias $ "PrimCall args: " ++ show args
            logAlias $ "callerAlias: " ++ show callerAlias
            logAlias $ "calleeAlias: " ++ show calleeAlias
            let aliasNames' = _aliasPairsToVarNames args
                                    (callerAlias ++ calleeAlias)
            logAlias $ "names: " ++ show aliasNames'
            return (prims ++ [prim], aliasNames ++ aliasNames')
        _ ->
            return (prims ++ [prim], aliasNames)

-- Helper: convert alias index pairs to var name pairs
_aliasPairsToVarNames :: [PrimArg] -> [AliasPair]
                            -> [(PrimVarName, PrimVarName)]
_aliasPairsToVarNames primCallArgs =
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

-- Helper: change mutate destructive flag to false if FlowIn variable is aliased
_updateMutateForAlias :: [(PrimVarName, PrimVarName)] -> [PrimArg] -> [PrimArg]
_updateMutateForAlias aliasNames
    [fIn@(ArgVar inName _ _ _ final), fOut@(ArgVar outName _ _ _ _), size,
    offset, ArgInt des typ, mem] =
        if _isVarAliased inName aliasNames
            then [fIn, fOut, size, offset, ArgInt 0 typ, mem]
            else [fIn, fOut, size, offset, ArgInt des typ, mem]
_updateMutateForAlias _ args = args

-- Helper: check if FlowIn variable is aliased after previous proc calls
_isVarAliased :: PrimVarName -> [(PrimVarName, PrimVarName)] -> Bool
_isVarAliased varName [] = False
_isVarAliased varName ((n1,n2):as) =
    (varName == n1 || varName == n2) || _isVarAliased varName as


-- |Log a message, if we are logging optimisation activity.
logAlias :: String -> Compiler ()
logAlias = logMsg Optimise
