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
import           BodyBuilder
import           Callers       (getSccProcs)
import           Control.Monad
import           Control.Monad.Trans
                               (lift)
import           Control.Monad.Trans.State
import           Data.Graph    (SCC(..))
import           Data.List     as List
import           Data.Map      as Map
import           Data.Maybe    as Maybe
import           Data.Set      as Set
import           Flow          ((|>))
import           Options       (LogSelection (Transform),
                                OptFlag(MultiSpecz), optimisationEnabled)
import           Util
import           Snippets      (primMove)


----------------------------------------------------------------
--
-- Transform mutate instructions with correct destructive flag
-- This is the extra pass after found the alias analysis fixed point
--
----------------------------------------------------------------
transformProc :: ProcDef -> Int -> Compiler ProcDef
transformProc def _
    | not (procInline def) = do
        let impln = procImpln def
        let body = procImplnBody impln
        (body', tmp) <- transformProcBody def generalVersion
        return def {procImpln = impln{procImplnBody = body'}, procTmpCount=tmp}

transformProc def _ = return def


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


-- transform a proc based on a given specialized version, and return the body
-- of that specialization.
transformProcBody :: ProcDef -> SpeczVersion -> Compiler (ProcBody, Int)
transformProcBody procDef speczVersion = do
    when (procInline procDef) $ shouldnt "transforming an inline proc"

    let proto = procImplnProto $ procImpln procDef
    let body = procImplnBody $ procImpln procDef
    let analysis = procImplnAnalysis $ procImpln procDef
    logTransform $ replicate 60 '~'
    logTransform $ show proto
    logTransform $ "[" ++ show (speczVersionToId speczVersion) ++ "] :"
                    ++ show speczVersion
    logTransform $ replicate 60 '~'

    aliasMap <- initAliasMap proto speczVersion
    let callSiteMap =
            expandRequiredSpeczVersionsByProcVersion analysis speczVersion
    logTransform $ "callSiteMap: " ++ show callSiteMap

    let params = primProtoParams proto
    let outVarSubs = params
                    |> List.filter (isOutputFlow . primParamFlow)
                    |> List.map primParamName |> List.map (\x -> (x,x))
                    |> Map.fromList
    let tmp = procTmpCount procDef
    (_, tmp', _, _, _, body') <- buildBody tmp outVarSubs params $
                transformBody proto body (aliasMap, Map.empty) callSiteMap
    return (body', tmp')


transformBody :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells)
        -> Map CallSiteID ProcSpec -> BodyBuilder ()
transformBody caller body (aliasMap, deadCells) callSiteMap = do
    -- (1) Analysis of current caller's prims
    (aliaseMap', deadCells') <-
            transformPrims caller body (aliasMap, deadCells) callSiteMap

    -- (2) Analysis of caller's bodyFork
    -- Update body while checking alias incurred by bodyfork
    transformForks caller body (aliaseMap', deadCells') callSiteMap


-- Check alias created by prims of caller proc
transformPrims :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells)
        -> Map CallSiteID ProcSpec
        -> BodyBuilder (AliasMapLocal, DeadCells)
transformPrims caller body (aliasMap, deadCells) callSiteMap = do
    let prims = bodyPrims body
    -- Transform simple prims:
    lift $ logTransform "\nTransform prims (transformPrims):   "
    foldM (transformPrim callSiteMap) (aliasMap, deadCells) prims


-- Recursively transform forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
transformForks :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells)
        -> Map CallSiteID ProcSpec -> BodyBuilder ()
transformForks caller body (aliasMap, deadCells) callSiteMap = do
    lift $ logTransform "\nTransform forks (transformForks):"
    let fork = bodyFork body
    case fork of
        PrimFork var ty _ fBodies deflt -> do
            buildFork var ty
            lift $ logTransform "Forking:"
            mapM_ (\currBody -> do
                    beginBranch
                    transformBody caller currBody
                                (aliasMap, deadCells) callSiteMap
                    endBranch
                ) (fBodies ++ maybeToList deflt)
            completeFork
        MergedFork var ty last table body -> do
            lift $ logTransform "Unmerging fork:"
            let unmerged = List.transpose
                        $ List.map (\(var, ty, vals) -> List.map (\p -> Unplaced $ primMove p (ArgVar var ty FlowOut Ordinary True)) vals)
                        table
            let bodies = ProcBody [] $ PrimFork var ty last (List.map (`prependToBody` body) unmerged) Nothing
            transformForks caller bodies (aliasMap, deadCells) callSiteMap
        NoFork -> do
            -- NoFork: transform prims done
            lift $ logTransform "No fork."


-- Build up alias pairs triggerred by proc calls
transformPrim :: Map CallSiteID ProcSpec
        -> (AliasMapLocal, DeadCells) -> Placed Prim
        -> BodyBuilder (AliasMapLocal, DeadCells)
transformPrim callSiteMap (aliasMap, deadCells) prim = do
    -- XXX Redundent work here. We should change the current design.
    aliasMap' <- lift $ updateAliasedByPrim aliasMap prim
    lift $ logTransform $ "\n--- prim:           " ++ show prim
    let primc = content prim

    (primc', deadCells') <- case primc of
            PrimCall id spec impurity args gFlows -> do
                doMultiSpecz <- lift $ gets (optimisationEnabled MultiSpecz . options)
                let spec' = if doMultiSpecz
                    then Map.findWithDefault spec id callSiteMap
                    else spec
                return (PrimCall id spec' impurity args gFlows, deadCells)
            PrimForeign "lpvm" "mutate" flags args -> do
                let args' = _updateMutateForAlias aliasMap args
                return (PrimForeign "lpvm" "mutate" flags args', deadCells)
            -- dead cell transform
            PrimForeign "lpvm" "access" _ args -> do
                deadCells'
                    <- lift $ updateDeadCellsByAccessArgs (aliasMap, deadCells) args
                return (primc, deadCells')
            PrimForeign "lpvm" "alloc" _ args  -> do
                let (result, deadCells') =
                        assignDeadCellsByAllocArgs deadCells args
                let primc' = case result of
                        Nothing -> primc
                        Just ((selectedCell, startOffset), []) ->
                            -- avoid "alloc" by reusing the "selectedCell".
                            let [_, varOut] = args in
                            -- Be aware that this will make the previous final
                            -- flag of "selectedCell" outdated.
                            -- TODO: we should consider using BodyBuilder for
                            -- the transform.
                            PrimForeign "llvm" "sub" []
                                    [selectedCell, startOffset, varOut]
                        _ -> shouldnt "invalid aliasMap for transform"
                when (Maybe.isJust result) $
                        lift $ logTransform "avoid using [alloc]."
                return (primc', deadCells')
            -- default case
            _ -> return (primc, deadCells)

    let pos = place prim
    lift $ logTransform $ "--- transformed to: " ++ show (maybePlace primc' pos)
    instr primc' pos
    return (aliasMap', deadCells')


-- Helper: change mutate destructive flag to true if FlowIn variable is not
-- aliased and is dead after this program point and the original destructive
-- flag is not set to 1 yet
_updateMutateForAlias :: AliasMapLocal -> [PrimArg] -> [PrimArg]
_updateMutateForAlias aliasMap
    args@[fIn, fOut, offset, ArgInt des typ, size, offset2, mem] =
        if des /= 1 && Just [] == isArgUnaliased aliasMap fIn
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



-- Fix point processor for expanding required specz versions in the given mod.
expandRequiredSpeczVersionsByMod :: [ModSpec] -> ModSpec
        -> Compiler (Bool, [(String, OptPos)])
expandRequiredSpeczVersionsByMod scc thisMod = do
    reenterModule thisMod
    logTransform $ "Expanding required specz versions for: " ++ show thisMod
    -- get proc level SCCs in top-down order
    orderedProcsTopDown <- List.reverse <$> getSccProcs thisMod

    requiredVersions <- Set.toList <$>
            foldM expandRequiredSpeczVersionsByProcSCC
                    Set.empty orderedProcsTopDown

    logTransform $ "requiredVersions: " ++ show requiredVersions
    reexitModule

    -- Update each module based on the requirements
    let requiredVersions' = List.map (\(ProcSpec mod procName procId version) ->
            (mod, (procName, (procId, version)))) requiredVersions
    changedList <- mapM (\(mod, versions) -> do
            changed <- updateRequiredMultiSpeczInMod mod versions
            --  we only care about changes in current scc
            return $ changed && List.elem mod scc
        ) (groupByFst requiredVersions')

    return (or changedList, [])


-- Expand required specz versions for the given proc SCC until it reaches a
-- fixpoint. For the SCC, we consider procs without specialization.
expandRequiredSpeczVersionsByProcSCC :: Set ProcSpec -> SCC ProcSpec
        -> Compiler (Set ProcSpec)
expandRequiredSpeczVersionsByProcSCC required (AcyclicSCC pspec) = do
    required' <- expandRequiredSpeczVersionsByProc required pspec
    -- immediate fixpoint if no mutual dependency
    return required'

expandRequiredSpeczVersionsByProcSCC required scc@(CyclicSCC pspecs) = do
    required' <- foldM expandRequiredSpeczVersionsByProc required pspecs
    -- whether it reaches a fixpoint: is there any newly found required versions
    -- of procs in the current SCC.
    let fixpoint = Set.difference required' required
                    |> all (\p -> not (List.any (sameBaseProc p) pspecs))
    if fixpoint
    then return required'
    else expandRequiredSpeczVersionsByProcSCC required' scc


-- Expand required specz versions for the given proc.
expandRequiredSpeczVersionsByProc :: Set ProcSpec -> ProcSpec
        -> Compiler (Set ProcSpec)
expandRequiredSpeczVersionsByProc required pspec = do
    procDef <- getProcDef pspec
    let analysis = procImplnAnalysis $ procImpln procDef
    let speczBodies = procImplnSpeczBodies $ procImpln procDef
    -- get it's currently existed/required versions
    let speczVersions = Set.filter (sameBaseProc pspec) required
                        |> Set.map procSpeczVersion
                        |> Set.union (Map.keysSet speczBodies)
                        -- always need the non-specialized version
                        |> Set.insert generalVersion
    let required' = Set.foldl (\required version ->
            let versions = expandRequiredSpeczVersionsByProcVersion
                                    analysis version
                            |> Map.elems
                            -- remove general versions
                            |> List.filter
                                    ((/= generalVersion) . procSpeczVersion)
                            |> Set.fromList
            in
            Set.union required versions) required speczVersions
    return required'


-- Whether the two "ProcSpec"s are belong to the same proc without considering
-- specialization.
sameBaseProc :: ProcSpec -> ProcSpec -> Bool
sameBaseProc (ProcSpec mod1 name1 id1 _) (ProcSpec mod2 name2 id2 _) =
    mod1 == mod2 && name1 == name2 && id1 == id2


-- For a given proc and a "SpeczVersion" of it, compute all specialized procs
-- it required.
-- Returns a mapping from call site to the actual proc to call.
-- XXX Add heuristic to select which specializations to use
expandRequiredSpeczVersionsByProcVersion :: ProcAnalysis -> SpeczVersion
        -> Map CallSiteID ProcSpec
expandRequiredSpeczVersionsByProcVersion procAnalysis callerVersion =
    procMultiSpeczDepInfo procAnalysis
    |> Map.map (\(procSpec, items) ->
        -- Add other expansion here and union the results
        let version = expandSpeczVersionsAlias callerVersion items in
        let ProcSpec mod procName procId _ = procSpec in
        (ProcSpec mod procName procId version))


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
                            let speczBodies = procImplnSpeczBodies procImp in
                            let speczBodies' = List.foldl (\bodies version ->
                                    Map.insertWith (\_ old -> old)
                                            version Nothing bodies
                                    ) speczBodies versions in
                            let newProcImpln =
                                    procImp{procImplnSpeczBodies=speczBodies'}
                            in
                            proc {procImpln=newProcImpln}
                            ) procs [0..]
                ) procName procMap
            ) procMap (groupByFst versions)
    updateModImplementation (updateModProcs (const procMap'))
    reexitModule
    let changed = procMap /= procMap'
    when changed
            (logTransform $ "new specz requirements in mod: " ++ show mod)
    return changed


-- For the given "ProcDef", generates all specz versions that are required but
-- haven't got generated.
generateSpeczVersionInProc :: ProcDef -> Int -> Compiler ProcDef
generateSpeczVersionInProc def@ProcDef{procTmpCount=tmp} _
    | not (procInline def) = do
        let procImp = procImpln def
        let speczBodies = procImplnSpeczBodies procImp
        if List.any isNothing (Map.elems speczBodies)
        then do -- missing required specz versions
            -- mark the current module as changed
            mod <- getModuleSpec
            updateCompiler (\st ->
                let unchanged = unchangedMods st |> Set.delete mod in
                    st {unchangedMods = unchanged})

            speczBodiesList <- mapM (\(ver, sbody) ->
                case sbody of
                    Just b -> return (ver, Just (b, tmp))
                    Nothing -> do
                        -- generate the specz version
                        sbody' <- transformProcBody def ver
                        return (ver, Just sbody')
                        ) (Map.toAscList speczBodies)
            let speczBodies' = Map.fromDistinctAscList speczBodiesList
            return $
                def {procImpln=procImp{procImplnSpeczBodies=(fst <$>) <$> speczBodies'}, 
                     procTmpCount=maximum $ tmp : List.map snd (Maybe.mapMaybe snd speczBodiesList)}
        else
            return def

generateSpeczVersionInProc def _ = return def


-- Similar to "List.groupBy"
groupByFst :: Eq a => [(a, b)] -> [(a, [b])]
groupByFst l =
    List.groupBy (\x y -> fst x == fst y) l
    |> List.map (\xs -> (fst (head xs), List.map snd xs))


-- |Log a message, if we are logging optimisation activity.
logTransform :: String -> Compiler ()
logTransform = logMsg Transform
