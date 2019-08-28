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
    updateProcDefM aliasProcDef pspec
    -- Get the new analysis info from the updated proc
    newDef <- getProcDef pspec
    let (ProcDefPrim _ _ newAnalysis) = procImpln newDef
    -- And compare if the alias map changed.
    logAlias "================================================="
    logAlias $ "old: " ++ show (procArgAliasMap oldAnalysis)
    logAlias $ "new: " ++ show (procArgAliasMap newAnalysis)
    return $ areDifferentMaps (procArgAliasMap oldAnalysis) (procArgAliasMap newAnalysis)
    -- ^XXX wrong way to do this. Need to change type signatures of a bunch of
    -- functions start from aliasProcDef which is called by updateProcDefM


-- Check if any argument become stale in this (not inlined) proc call
-- Return updated ProcDef and a flag (indicating if proc analysis info changed)
-- XXX aliasProcDef :: ProcDef -> Compiler (ProcDef, a)
aliasProcDef :: ProcDef -> Compiler ProcDef
aliasProcDef def
    | not (procInline def) = do
        let (ProcDefPrim caller body oldAnalysis) = procImpln def
        logAlias $ show caller
        -- (1) Analysis of current caller's prims
        aliaseMap1 <- aliasedByPrims caller body initUnionFind
        -- (2) Analysis of caller's bodyFork
        aliaseMap2 <- aliasedByFork caller body aliaseMap1
        -- (3) Clean up summary of aliases by removing phantom params
        let nonePhantomParams = protoNonePhantomParams caller
        -- ^nonePhantomParams is a list of formal params of this caller
        let aliaseMap3 = Map.filterWithKey (\k _ -> List.elem
                            k nonePhantomParams) aliaseMap2
        -- Some logging
        logAlias $ "\n^^^  after analyse prims:    " ++ show aliaseMap1
        logAlias $ "^^^  after analyse forks:    " ++ show aliaseMap2
        logAlias $ "^^^  remove phantom params: " ++ show nonePhantomParams
        logAlias $ "^^^  alias of formal params: " ++ show aliaseMap3
        -- (4) Update proc analysis with new aliasPairs
        let newAnalysis = oldAnalysis {
                            procArgAliasMap = aliaseMap3
                        }
        return $ def { procImpln = ProcDefPrim caller body newAnalysis }
aliasProcDef def = return def -- ^XXX return (def, False)


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
            foldM (\amap currBody ->
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
maybeAliasPrimArgs prim@(PrimForeign _ "mutate" flags args) =
    if "noalias" `elem` flags
        then return ([],[], primArgs prim)
        else _maybeAliasPrimArgs args
maybeAliasPrimArgs prim =
    return ([],[], primArgs prim)


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
        logAlias $ "      primArgs:           " ++ show primArgs
        logAlias $ "      maybeAliasedInput:  " ++ show maybeAliasedInput
        logAlias $ "      maybeAliasedOutput: " ++ show maybeAliasedOutput
        let aliases = cartProd maybeAliasedInput maybeAliasedOutput
        let aliasMap1 = List.foldr (\(inArg, outArg) aMap ->
                            uniteUf aMap outArg inArg) currentAlias aliases
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
