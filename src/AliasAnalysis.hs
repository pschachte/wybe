--  File     : AliasAnalysis.hs
--  Author   : Ting Lu
--  Origin   : Sun Sep 16 16:08:00 EST 2018
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.

module AliasAnalysis (aliasSccBottomUp)
    where

import           AST
import           Control.Monad
import           Data.Graph
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Options       (LogSelection (Analysis))
import           Util


----------------------------------------------------------------
--                     Escape Analysis
----------------------------------------------------------------
-- PROC LEVEL ALIAS ANALYSIS
-- XXX aliasSccBottomUp :: SCC ProcSpec -> Compiler a
aliasSccBottomUp :: SCC ProcSpec -> Compiler ()
aliasSccBottomUp (AcyclicSCC single) =
    mapM_ aliasProcBottomUp [single]
    -- immediate fixpoint if no mutual dependency
-- gather all flags (indicating if any proc alias information changed or not) by
--     comparing transitive closure of the (key, value) pairs of the map; Only
--     cycclic procs need to reach a fixed point
-- False means alias info not changed; so that a fixed point is reached
aliasSccBottomUp procs@(CyclicSCC multi) = do
    changed <- mapM aliasProcBottomUp multi
    logAlias $ "\n>>> CyclicSCC procs alias changed? "
        ++ show (or changed) ++ " - " ++ show changed
    when (or changed) $ aliasSccBottomUp procs
    -- TODO: Is module level fixpoint of alias analysis needed? proc level
    -- analysis will reach fixpoint anyway??


-- XXX aliasProcBottomUp :: ProcSpec -> Compiler a
aliasProcBottomUp :: ProcSpec -> Compiler Bool
aliasProcBottomUp pspec = do
    logAlias $ "\n>>> Alias analysis (Bottom-up): " ++ show pspec
    oldDef <- getProcDef pspec
    let (ProcDefPrim _ _ oldAnalysis) = procImpln oldDef
    -- Update alias analysis info to this proc
    updateProcDefM checkEscapeDef pspec
    -- Get the new analysis info from the updated proc
    newDef <- getProcDef pspec
    let (ProcDefPrim _ _ newAnalysis) = procImpln newDef
    -- And compare if the alias map changed
    areDifferentMaps (procArgAliasMap oldAnalysis) (procArgAliasMap newAnalysis)
    -- ^XXX wrong way to do this?! Need to change type signatures of a bunch of
    -- functions start from checkEscapeDef which is called by updateProcDefM


-- Check if any argument become stale in this (not inlined) proc call
-- Return updated ProcDef and a flag (indicating if proc analysis info changed)
-- XXX checkEscapeDef :: ProcDef -> Compiler (ProcDef, a)
checkEscapeDef :: ProcDef -> Compiler ProcDef
checkEscapeDef def
    | not (procInline def) = do
        let (ProcDefPrim caller body oldAnalysis) = procImpln def
        logAlias $ show caller

        -- TODO: don't transform prims here; do it in Transform.hs and do it
        -- after fixedpoint analysis process finished

        -- (1) Analysis of current caller's prims
        alias1 <- checkEscapePrims caller body []
        (bodyPrimsAliases, finalSet1, newPrims) <-
            aliasedByPrims caller body (initUnionFind, Set.empty, [])
        -- Update bodyPrims of this procbody
        let body1 = body { bodyPrims = newPrims }

        -- (2) Analysis of caller's bodyFork
        alias2 <- checkEscapeFork caller body alias1
        -- Update body while checking alias incurred by bodyfork
        (bodyForkAliases, finalSet2, body2) <-
            aliasedByFork caller body1 (bodyPrimsAliases, finalSet1)

        if body1 /= body2
            then logAlias "BODY CHANGED AFTER CHECK ALIAS BY FORK"
            else logAlias "BODY NOT CHANGED"

        -- (3) Clean up summary of aliases by removing phantom params
        let nonePhantomParams = protoNonePhantomParams caller
        let bodyForkAliases' = Map.filterWithKey (\k _ -> List.elem
                                    k nonePhantomParams) bodyForkAliases
        -- finalSet3 contains all args in final use in this caller excluding
        -- formal parameters
        let finalSet3 = Set.difference finalSet2
                            $ Set.fromList $ primProtoParamNames caller
        -- Cleanup root that is final
        let (totalAliases, rootMap) = Map.foldrWithKey (convertUfRoot finalSet3)
                                (initUnionFind, Map.empty) bodyForkAliases'
        -- In case key is in final use, so cleanup again
        let (totalAliases', _) = Map.foldrWithKey (convertUfKey finalSet3)
                                (initUnionFind, rootMap) totalAliases

        -- Some logging
        logAlias $ "\n^^^  aliases (int pair):     " ++ show alias2
        logAlias $ "^^^  after analyse prims:    " ++ show bodyPrimsAliases
        logAlias $ "^^^  after analyse forks:    " ++ show bodyForkAliases
        logAlias $ "^^^  alias of formal params: " ++ show bodyForkAliases'
        logAlias $ "^^^  params in final:        " ++ show finalSet3
        logAlias $ "^^^  alias without finals:   " ++ show totalAliases'

        -- (4) Update proc analysis with new aliasPairs
        let newAnalysis = oldAnalysis {
                            procArgAliases = alias2,
                            procArgAliasMap = totalAliases'
                        }
        let newDef = def { procImpln = ProcDefPrim caller body2 newAnalysis }

        return newDef

checkEscapeDef def =
    -- XXX return (def, False)
    return def


-- Check alias created by prims of caller proc
aliasedByPrims :: PrimProto -> ProcBody
                    -> (AliasMap, Set PrimVarName, [Placed Prim])
                    -> Compiler (AliasMap, Set PrimVarName, [Placed Prim])
aliasedByPrims caller body (initAliases, initFinalSet, initPrims) = do
    let nonePhantomParams = protoNonePhantomParams caller
    let prims = bodyPrims body

    -- Analyse simple prims:
    -- (only process alias pairs incurred by move, mutate, access, cast)
    logAlias "\nAnalyse prims (aliasedByPrims):    "
                -- ++ List.intercalate "\n    " (List.map show prims)
    let aliasMap = List.foldr newUfItem initAliases nonePhantomParams
    foldM aliasedByPrim (aliasMap, initFinalSet, []) prims


-- Build up alias pairs triggerred by proc calls
aliasedByPrim :: (AliasMap, Set PrimVarName, [Placed Prim]) -> Placed Prim
                    -> Compiler (AliasMap, Set PrimVarName, [Placed Prim])
aliasedByPrim (aliasMap, finalSet, prims) prim =
    case content prim of
        PrimCall spec args -> do
            calleeDef <- getProcDef spec
            let (ProcDefPrim calleeProto _ analysis) = procImpln calleeDef
            let calleeParamAliases = procArgAliasMap analysis
            logAlias $ "\n    --- call " ++ show spec ++" (callee): "
            logAlias $ "    " ++ show calleeProto
            logAlias $ "    PrimCall args: " ++ show args
            logAlias $ "    current aliasMap: " ++ show aliasMap
            logAlias $ "    calleeAlias: " ++ show calleeParamAliases
            let paramArgMap = mapParamToArgVar calleeProto args

            -- calleeArgsAliasMap is the alias map of actual arguments passed
            -- into callee
            let calleeArgsAliases = Map.foldrWithKey (convertUfVal paramArgMap)
                                            initUnionFind calleeParamAliases
            let combinedAliases = combineUf calleeArgsAliases aliasMap
            return (combinedAliases, _finalArgs args finalSet, prims ++ [prim])
        _ -> do
            logAlias $ "    " ++ show prim
            -- escapablePrimArgs (content prim) >>=
            --     aliasedArgsInPrim (aliasMap, finalSet)
            escapableArgs <- escapablePrimArgs (content prim)
            -- Mutate destructive flag if this is a mutate instruction
            prim' <- mutateInstruction prim aliasMap
            -- Update alias map for escapable args
            (aliasMap', finalSet') <-
                aliasedArgsInPrim (aliasMap, finalSet) escapableArgs
            return (aliasMap', finalSet', prims ++ [prim'])


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
aliasedByFork :: PrimProto -> ProcBody
                    -> (AliasMap, Set PrimVarName)
                    -> Compiler (AliasMap, Set PrimVarName, ProcBody)
aliasedByFork caller body (aliasMap, finalSet) = do
    logAlias "\nAnalyse forks (aliasedByFork):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logAlias "Forking:"
            (aliasMap', finalSet', fBodies') <-
                foldM (\(amap, fset, bs) currBody -> do
                    (amap', fset', ps') <-
                        aliasedByPrims caller currBody (initUnionFind, Set.empty, [])
                    let currBody1 = currBody { bodyPrims = ps' }
                    (amap'', fset'', currBody2) <-
                        aliasedByFork caller currBody1 (amap', fset')
                    let combinedAliases = combineUf amap'' amap
                    let combinedFinalSet = Set.union fset fset''
                    return (combinedAliases, combinedFinalSet, bs++[currBody2])
                ) (aliasMap, finalSet, []) fBodies
            return (aliasMap', finalSet', body { bodyFork = fork {forkBodies=fBodies'} })
        _ -> do
            -- NoFork: analyse prims done
            logAlias "No fork."
            return (aliasMap, finalSet, body)


-- Build up alias pairs triggerred by move, mutate, access, cast instructions
escapablePrimArgs :: Prim -> Compiler [PrimArg]
escapablePrimArgs (PrimForeign _ "move" _ args)   = return args
escapablePrimArgs (PrimForeign _ "mutate" _ args) = return args
escapablePrimArgs (PrimForeign _ "access" _ args) = return args
escapablePrimArgs (PrimForeign _ "cast" _ args)   = return args
escapablePrimArgs _                               = return []


-- Helper: compare if two AliasMaps are different
-- Have to convert the map to Alias Pairs because the root could be different in
-- two maps whereas the alias info are the same instead
areDifferentMaps :: AliasMap -> AliasMap -> Compiler Bool
areDifferentMaps aliasMap1 aliasMap2 = do
    let aliasPair1 = aliasMapToAliasPairs aliasMap1
    let aliasPair2 = aliasMapToAliasPairs aliasMap2
    -- don't have to flag the change if the alias is changed from an empty list
    -- to another list because the list is always changed at the first time
    return $ not (List.null aliasPair1) && aliasPair1 /= aliasPair2


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
aliasedArgsInPrim :: (AliasMap, Set PrimVarName) -> [PrimArg]
                        -> Compiler (AliasMap, Set PrimVarName)
aliasedArgsInPrim (aliasMap, finalSet) [] = return (aliasMap, finalSet)
aliasedArgsInPrim (aliasMap, finalSet) args = do
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


-- Helper: put final arg into the set
_finalArgs :: [PrimArg] -> Set PrimVarName -> Set PrimVarName
_finalArgs [fIn@(ArgVar inName _ _ _ final), _, _, _, _, _] finalSet =
    Set.insert inName finalSet
_finalArgs _ finalSet = finalSet


-- Update mutate prim by checking if input is aliased
mutateInstruction :: Placed Prim -> AliasMap -> Compiler (Placed Prim)
mutateInstruction (Placed (PrimForeign lang "mutate" flags args) pos) aliasMap = do
    args' <- _updateMutateForAlias aliasMap args
    return (Placed (PrimForeign lang "mutate" flags args') pos)
mutateInstruction (Unplaced (PrimForeign lang "mutate" flags args)) aliasMap = do
    args' <- _updateMutateForAlias aliasMap args
    return (Unplaced (PrimForeign lang "mutate" flags args'))
mutateInstruction prim _ =  return prim


-- Helper: change mutate destructive flag to true if FlowIn variable is final
-- and not aliased and the original destructive flag is not 1 yet
_updateMutateForAlias :: AliasMap -> [PrimArg] -> Compiler [PrimArg]
_updateMutateForAlias aliasMap
    [fIn@(ArgVar inName _ _ _ final1), fOut, size, offset, ArgInt des typ,
    mem@(ArgVar memName _ _ _ final2)] =
        -- When the val is also a pointer
        if not (connectedToOthers aliasMap inName) && final1
            && not (connectedToOthers aliasMap memName) && final2
            && des /= 1
        then return [fIn, fOut, size, offset, ArgInt 1 typ, mem]
        else return [fIn, fOut, size, offset, ArgInt des typ, mem]
_updateMutateForAlias aliasMap
    [fIn@(ArgVar inName _ _ _ final), fOut, size, offset, ArgInt des typ, mem] =
        if not (connectedToOthers aliasMap inName) && final && des /= 1
        then return [fIn, fOut, size, offset, ArgInt 1 typ, mem]
        else return [fIn, fOut, size, offset, ArgInt des typ, mem]
_updateMutateForAlias _ args = return args


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
