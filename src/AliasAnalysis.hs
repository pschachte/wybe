--  File     : AliasAnalysis.hs
--  Author   : Ting Lu
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

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
import           Data.Maybe    (catMaybes)
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
        aliasMap1 <- aliasedByPrims caller body emptyDS
        -- (2) Analysis of caller's bodyFork
        aliasMap2 <- aliasedByFork caller body aliasMap1
        -- (3) Clean up summary of aliases by removing phantom params
        realParams <- (Set.fromList . (primParamName <$>))
                      <$> protoRealParams caller
        -- ^realParams is a list of formal params of this caller
        let aliasMap3 = filterDS (\x -> Set.member x realParams) aliasMap2
        -- Some logging
        logAlias $ "\n^^^  after analyse prims:    " ++ show aliasMap1
        logAlias $ "^^^  after analyse forks:    " ++ show aliasMap2
        logAlias $ "^^^  remove phantom params: " ++ show realParams
        logAlias $ "^^^  alias of formal params: " ++ show aliasMap3
        -- (4) Update proc analysis with new aliasPairs
        let newAnalysis = oldAnalysis {
                            procArgAliasMap = aliasMap3
                        }
        return $ def { procImpln = ProcDefPrim caller body newAnalysis }
aliasProcDef def = return def -- ^XXX return (def, False)


-- Check alias created by prims of caller proc
aliasedByPrims :: PrimProto -> ProcBody -> AliasMap -> Compiler AliasMap
aliasedByPrims caller body initAliases = do
    realParams <- (primParamName <$>) <$> protoRealParams caller
    let prims = bodyPrims body
    -- Analyse simple prims:
    -- (only process alias pairs incurred by move, access, cast)
    logAlias "\nAnalyse prims (aliasedByPrims):    "
    let aliasMap = List.foldr addOneToDS initAliases realParams
    -- realParams <- protoRealParams caller
    foldM (aliasedByPrim realParams) aliasMap prims


-- Build up alias pairs triggerred by proc calls
-- realParams: caller's formal params
aliasedByPrim :: [PrimVarName] -> AliasMap -> Placed Prim -> Compiler AliasMap
aliasedByPrim realParams aliasMap prim =
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
                    mapDS (\x -> 
                        case Map.lookup x paramArgMap of 
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
            aliasMaps <- 
                mapM (\currBody ->
                        aliasedByPrims caller currBody aliasMap >>=
                            aliasedByFork caller currBody
                    ) fBodies
            let aliasMap' = List.foldl combineTwoDS emptyDS aliasMaps
            return aliasMap'
        NoFork -> do
            -- NoFork: analyse prims done
            logAlias ">>> No fork."
            return aliasMap


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


-- Helper: compare if two AliasMaps are different
-- Have to ensure the aliasing map is canonical by converting the map to Alias
-- Pairs because the root could be different in two maps whereas the alias info
-- are the same
areDifferentMaps :: AliasMap -> AliasMap -> Bool
areDifferentMaps aliasMap1 aliasMap2 =
    let aliasPair1 = aliasMapToAliasPairs aliasMap1
        aliasPair2 = aliasMapToAliasPairs aliasMap2
    in aliasPair1 /= aliasPair2


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


-- |Log a message, if we are logging optimisation activity.
logAlias :: String -> Compiler ()
logAlias = logMsg Analysis
