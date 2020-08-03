--  File     : Transform.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Transform LPVM after alias analysis
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE LambdaCase #-}

module Transform (transformProc,
        generateSpeczVersionInProc, expandRequiredSpeczVersionsByMod) where

import           AliasAnalysis
import           AST
import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Bits     as Bits
import           Data.List     as List
import           Data.Map      as Map
import           Data.Maybe    as Maybe
import           Data.Set      as Set
import           Flow          ((|>))
import           Options       (LogSelection (Transform), optNoMultiSpecz)
import           Util


----------------------------------------------------------------
--
-- Transform mutate instructions with correct destructive flag
-- This is the extra pass after found the alais analysis fixed point
--
----------------------------------------------------------------
transformProc :: ProcDef -> Compiler ProcDef
transformProc def
    | not (procInline def) = do
        let (ProcDefPrim caller body analysis speczBodies) = procImpln def
        logTransform $ replicate 60 '~'
        logTransform $ show caller
        logTransform $ replicate 60 '~'

        -- transform the standard body
        -- In this case, all input params are aliased
        inputParams <- protoInputParamNames caller
        aliasMap <- initAliasMap caller Set.empty
        body' <- transformBody caller body (aliasMap, Map.empty)

        return def { procImpln = ProcDefPrim caller body' analysis speczBodies}

transformProc def = return def


-- For the given "ProcDef", generates all specz versions that are required but
-- haven't got generated.
generateSpeczVersionInProc :: ProcDef -> Compiler ProcDef
generateSpeczVersionInProc def
    | not (procInline def) = do
        let procImp = procImpln def
        let ProcDefPrim caller body analysis speczBodies = procImp
        if List.any isNothing (Map.elems speczBodies)
        then do -- missing required specz versions
            -- mark the current module as changed
            mod <- getModuleSpec
            updateCompiler (\st ->
                let unchanged = unchangedMods st |> Set.delete mod in
                    st {unchangedMods = unchanged})

            speczBodiesList <- mapM (\(ver, sbody) ->
                case sbody of 
                    Just b -> return (ver, Just b)
                    Nothing -> do
                        -- generate the specz version
                        aliasMap <- initAliasMap caller ver
                        logTransform $ replicate 60 '~'
                        logTransform $ "Generating specialized version: "
                                ++ show ver
                        sbody' <- transformBody caller body
                                (aliasMap, Map.empty)
                        return (ver, Just sbody')
                        ) (Map.toAscList speczBodies)
            let speczBodies' = Map.fromDistinctAscList speczBodiesList
            return $
                def {procImpln = ProcDefPrim caller body analysis speczBodies'}
        else
            return def

generateSpeczVersionInProc def = return def


-- init aliasMap based on the given "nonAliasedParams",
-- in the transform step, we don't have "MaybeAliasByParam".
initAliasMap :: PrimProto -> SpeczVersion -> Compiler AliasMapLocal
initAliasMap proto speczVersion = do
    let nonAliasedParams = Set.toList speczVersion
            |> Maybe.mapMaybe (\case 
                NonAliasedParam paramID -> Just $
                        parameterIDToVarName proto paramID
                _ -> Nothing
            )
    inputParams <- protoInputParamNames proto
    logTransform $ "inputParams:      " ++ show inputParams
    logTransform $ "nonAliasedParams: " ++ show nonAliasedParams
    return $ 
        List.foldl (\aliasMap param -> 
            if List.notElem param nonAliasedParams
                then unionTwoInDS (LiveVar param) (AliasByParam param) aliasMap
                else aliasMap
            ) emptyDS inputParams 


transformBody :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells)
        -> Compiler ProcBody
transformBody caller body (aliasMap, deadCells) = do
    -- (1) Analysis of current caller's prims
    ((aliaseMap', deadCells'), newPrims) <- 
            transformPrims caller body (aliasMap, deadCells)
    -- Update bodyPrims of this procbody
    let body' = body { bodyPrims = newPrims }

    -- (2) Analysis of caller's bodyFork
    -- Update body while checking alias incurred by bodyfork
    transformForks caller body' (aliaseMap', deadCells')

    -- XXX run (or re-run) optimizations here since after the transform, there
    -- might be some new opportunities.


-- Check alias created by prims of caller proc
transformPrims :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells) 
        -> Compiler ((AliasMapLocal, DeadCells), [Placed Prim])
transformPrims caller body (aliasMap, deadCells) = do
    let prims = bodyPrims body
    -- Transform simple prims:
    logTransform "\nTransform prims (transformPrims):   "
    foldM transformPrim ((aliasMap, deadCells), []) prims


-- Recursively transform forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
transformForks :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells)
        -> Compiler ProcBody
transformForks caller body (aliasMap, deadCells) = do
    logTransform "\nTransform forks (transformForks):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies -> do
            logTransform "Forking:"
            fBodies' <-
                mapM (\currBody -> 
                        transformBody caller currBody (aliasMap, deadCells)
                ) fBodies
            return body { bodyFork = fork {forkBodies=fBodies'} }
        NoFork -> do
            -- NoFork: transform prims done
            logTransform "No fork."
            return body


-- Build up alias pairs triggerred by proc calls
transformPrim :: ((AliasMapLocal, DeadCells), [Placed Prim])
        -> Placed Prim -> Compiler ((AliasMapLocal, DeadCells), [Placed Prim])
transformPrim ((aliasMap, deadCells), prims) prim = do
    -- XXX Redundent work here. We should change the current design.
    aliasMap' <- updateAliasedByPrim aliasMap prim
    logTransform $ "\n--- prim:           " ++ show prim
    let primc = content prim
    
    (primc', deadCells') <- case primc of
            PrimCall id spec args -> do
                noMultiSpecz <- gets (optNoMultiSpecz . options)
                spec' <- if noMultiSpecz
                    then return spec
                    else _updatePrimCallForSpecz spec args aliasMap
                return (PrimCall id spec' args, deadCells)
            PrimForeign "lpvm" "mutate" flags args -> do
                let args' = _updateMutateForAlias aliasMap args
                return (PrimForeign "lpvm" "mutate" flags args', deadCells)
            -- dead cell transform
            PrimForeign "lpvm" "access" _ args -> do
                deadCells' 
                    <- updateDeadCellsByAccessArgs (aliasMap, deadCells) args
                return (primc, deadCells')
            PrimForeign "lpvm" "alloc" _ args  -> do
                let (result, deadCells') = 
                        assignDeadCellsByAllocArgs deadCells args
                let primc' = case result of 
                        Nothing -> primc
                        Just (selectedCell, []) -> 
                            -- replace "alloc" with "move" by reusing the 
                            -- "selectedCell".
                            let [_, varOut] = args in
                            let varIn = 
                                    varOut {argVarName = selectedCell,
                                            argVarFlow = FlowIn,
                                            argVarFinal = True}
                            in
                            PrimForeign "llvm" "move" [] [varIn, varOut]
                        _ -> shouldnt "invalid aliasMap for transform"
                when (Maybe.isJust result) $ 
                        logTransform "replacing [alloc] with [move]."
                return (primc', deadCells')
            -- default case
            _ -> return (primc, deadCells)
    
    prim' <- updatePlacedM (\_ -> return primc') prim
    logTransform $ "--- transformed to: " ++ show prim'
    return ((aliasMap', deadCells'), prims ++ [prim'])


-- Update PrimCall to make it uses a better specialized version
-- than the general version based on the current [AliasMap]
_updatePrimCallForSpecz :: ProcSpec -> [PrimArg] -> AliasMapLocal
        -> Compiler ProcSpec
_updatePrimCallForSpecz spec args aliasMap = do
    calleeDef <- getProcDef spec
    let (ProcDefPrim calleeProto _ analysis _) = procImpln calleeDef
    let nonAliasedParamIDs = List.filter (\(arg, paramID) ->
                -- it should be an interesting param of callee
                Set.member (InterestingUnaliased paramID)
                        (procInterestingCallProperties analysis)
                -- it should be an interesting variable
                && Right [] == isArgVarInteresting aliasMap arg
                -- if a argument is used more than once,
                -- then it should be aliased
                && isArgVarUsedOnceInArgs arg args
            ) (List.zip args [0..]) |> List.map snd
    return 
        (if List.null nonAliasedParamIDs
        then spec
        else
            let speczVersion = nonAliasedParamIDs
                    |> List.map NonAliasedParam |> Set.fromList |> Just
            in
            spec { procSpeczVersion = speczVersion })


-- Helper: change mutate destructive flag to true if FlowIn variable is not
-- aliased and is dead after this program point and the original destructive
-- flag is not set to 1 yet
_updateMutateForAlias :: AliasMapLocal -> [PrimArg] -> [PrimArg]
_updateMutateForAlias aliasMap
    args@[fIn, fOut, offset, ArgInt des typ, size, offset2, mem] =
        if des /= 1 && Right [] == isArgVarInteresting aliasMap fIn
        then [fIn, fOut, offset, ArgInt 1 typ, size, offset2, mem]
        else args
_updateMutateForAlias _ args = args

----------------------------------------------------------------
--
-- Multiple specialization
--
----------------------------------------------------------------
-- To support a new kind of multiple specialization:
--   1. (optional) Record constrains and related info about specialized versions
--      in "InterestingCallProperty".
--   2. Update "CallSiteProperty" in "AST.hs" so it can record corresponding
--      info.
--   3. In Analysis pass, generate some "CallSiteProperty"s for each
--      "PrimCall" call site and add them into "MultiSpeczDepInfo".
--      (eg. see the call to "updateMultiSpeczDepInfo" in "AliasAnalysis.hs")
--   4. Update "CallProperty" in "AST.hs" for describing a new specialized
--      information.
--   5. Implement a new expansion that can generate those "CallProperty" for
--      each callee based on the caller's "SpeczVersion" and
--      "MultiSpeczDepInfo". Add the expansion to 
--      "expandRequiredSpeczVersionsByProcVersion".
--      (eg. expandSpeczVersionsAlias)
--   6. Update "generateSpeczVersionInProc" to generate specialized code based
--      on given "SpeczVersion".


-- Fix point processor for expanding required specz versions.
-- XXX This part can be optimized by using "getSccProcs" and tracking the diff
-- between each run.
expandRequiredSpeczVersionsByMod :: [ModSpec] -> ModSpec 
        -> Compiler (Bool,[(String,OptPos)])
expandRequiredSpeczVersionsByMod scc thisMod = do
    reenterModule thisMod
    logTransform $ "Expanding required specz versions for:" ++ show thisMod
    -- Get all specz versions that required by others
    procs <- getModuleImplementationField modProcs
    -- Go through all specz versions in this mod that required by others,
    -- expand those to find all required versions
    let requiredVersions = Map.foldlWithKey (\required procName procDefs ->
            List.foldl (\required (procDef, procId) -> 
                let (ProcDefPrim _ _ analysis speczBodies) = 
                        procImpln procDef
                in
                -- we always need the non-specialized version
                let speczVersions = 
                        Map.keysSet speczBodies
                        |> Set.insert Set.empty
                in
                -- for each specz version, expand it's dependencies
                Set.foldl (\required version ->
                    let depMatches = 
                            expandRequiredSpeczVersionsByProcVersion
                                analysis version
                    in
                        Set.union required depMatches
                    ) required speczVersions
                ) required (List.zip procDefs [0..])
            ) Set.empty procs
            |> Set.toAscList
    logTransform $ "requiredVersions: " ++ show requiredVersions
    reexitModule
    -- Update each module based on the requirements
    let requiredVersions' = List.map (\((mod, procName, procId), version) ->
            (mod, (procName, (procId, version)))) requiredVersions
    changedList <- mapM (\(mod, versions) -> do
            changed <- updateRequiredMultiSpeczInMod mod versions
            --  we only care about changes in current scc
            return $ changed && List.elem mod scc
        ) (groupByFst requiredVersions')

    return (or changedList, [])


-- For a given proc and a "SpeczVersion" of it, compute all specialized procs
-- it required.
-- XXX Add heuristic to select which specializations to use
expandRequiredSpeczVersionsByProcVersion :: ProcAnalysis -> SpeczVersion
        -> Set ((ModSpec, ProcName, Int), SpeczVersion)
expandRequiredSpeczVersionsByProcVersion procAnalysis callerVersion = 
    let multiSpeczDepInfo = procMultiSpeczDepInfo procAnalysis in
    -- go through dependencies and find matches
    List.map (\(_, (procSpec, items)) ->
            -- Add other expansion here and union the results
            let version = expandSpeczVersionsAlias callerVersion items in
            let ProcSpec mod procName procId _ = procSpec in
                ((mod, procName, procId), version)
            ) (Map.toList multiSpeczDepInfo)
    -- remove the standard version
    |> List.filter (not . Set.null . snd)
    |> Set.fromList


-- expand specz versions for global CTGC
expandSpeczVersionsAlias :: SpeczVersion -> Set CallSiteProperty 
        -> SpeczVersion
expandSpeczVersionsAlias callerVersion items =
    Maybe.mapMaybe (\case
        NonAliasedParamCond param requiredParams ->
            let meetCond = 
                    List.all (\x -> 
                        Set.member (NonAliasedParam x) callerVersion
                    ) requiredParams
            in
            if meetCond then Just param else Nothing
        _ -> Nothing
    ) (Set.toList items)
    |> List.map NonAliasedParam |> Set.fromList


-- Mark a list of specz versions as required in the given module.
-- It returns false if all the new versions already exist.
updateRequiredMultiSpeczInMod :: ModSpec  -> [(ProcName, (Int, SpeczVersion))] 
        -> Compiler Bool
updateRequiredMultiSpeczInMod mod versions = do
    logTransform $ "Updating specz requirements in mod: " ++ show mod
    reenterModule mod
    procMap <- getModuleImplementationField modProcs
    let procMap' = List.foldl (\procMap (procName, versions) ->
            let idToVersions =
                    versions |> groupByFst |> Map.fromAscList
            in
            Map.adjust (\procs ->
                List.zipWith (\proc id ->
                    case Map.lookup id idToVersions of
                        Nothing -> proc
                        Just versions ->
                            let procImp = procImpln proc in
                            let ProcDefPrim pp pb pa speczBodies = procImp in
                            let speczBodies' = List.foldl (\bodies version ->
                                    Map.insertWith (\_ old -> old) 
                                            version Nothing bodies
                                    ) speczBodies versions
                            in
                            proc {procImpln = ProcDefPrim pp pb pa speczBodies'}
                            ) procs [0..]
                ) procName procMap
            ) procMap (groupByFst versions)
    updateModImplementation (updateModProcs (const procMap'))
    reexitModule
    let changed = procMap /= procMap'
    when changed 
            (logTransform $ "new specz requirements in mod: " ++ show mod)
    return changed


-- Similar to "List.groupBy"
groupByFst :: Eq a => [(a, b)] -> [(a, [b])]
groupByFst l = 
    List.groupBy (\x y -> fst x == fst y) l
    |> List.map (\xs -> (fst(head xs), List.map snd xs))


-- |Log a message, if we are logging optimisation activity.
logTransform :: String -> Compiler ()
logTransform = logMsg Transform
