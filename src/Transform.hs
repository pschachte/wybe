--  File     : Transform.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Transform LPVM after alias analysis
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

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
                                OptFlag(MultiSpecz, StackAlloc),
                                optimisationEnabled,
                                optStackAllocLimit)
import           Util
import           Snippets      (primMove)
import           Data.Tuple.HT (mapFst)


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


-- | Collect all prims from a body, including all fork branches (conservative).
collectAllBodyPrims :: ProcBody -> [Prim]
collectAllBodyPrims = foldBodyPrims (\_ p ps -> p : ps) [] (++)


-- | Returns True if this prim is lpvm alloc or lpvm mutate.
isAllocOrMutate :: Prim -> Bool
isAllocOrMutate (PrimForeign "lpvm" "alloc"  _ _) = True
isAllocOrMutate (PrimForeign "lpvm" "mutate" _ _) = True
isAllocOrMutate _                                  = False

-- | True for calls whose callee we cannot analyse: user-defined calls
-- (PrimCall), higher-order calls (PrimHigher), and foreign calls to languages
-- other than llvm/lpvm (e.g. C).  Any pointer passed as an input to such a call
-- must be treated as escaping (see computeEscapedVars).
isConservativeCall :: Prim -> Bool
isConservativeCall PrimCall{}               = True
isConservativeCall PrimHigher{}             = True
isConservativeCall (PrimForeign lang _ _ _) = lang /= "llvm" && lang /= "lpvm"

-- | True for ops that copy an address into a (possibly different-typed) result
-- without dereferencing it, so escape must propagate from output to input
-- regardless of type.  lpvm cast changes the type while preserving the
-- value/address; llvm move copies it unchanged.
isValuePreserving :: Prim -> Bool
isValuePreserving (PrimForeign "lpvm" "cast" _ _) = True
isValuePreserving (PrimForeign "llvm" "move" _ _) = True
isValuePreserving _                                = False

-- | Compute the set of variables that may escape the procedure body, i.e.,
-- variables whose values could possibly be referred to after the procedure
-- returns.  A variable escapes if it is an output parameter, or if its pointer
-- reaches an escaping variable through the mutation/pass-through graph.  This
-- is a conservative backward reachability analysis; allocs NOT in this set are
-- safe to stack-allocate.
-- Note: stack-allocated values passed as pointer arguments to callees will
-- prevent LLVM from using tail-call optimisation on those call sites.
computeEscapedVars :: PrimProto -> ProcBody -> Set PrimVarName
computeEscapedVars proto body =
    let prims = collectAllBodyPrims body
        -- Seed (1): every output parameter escapes by definition.
        outParamEsc = [ primParamName p
                      | p <- primProtoParams proto
                      , isOutputFlow (primParamFlow p) ]
        -- Seed (2): every pointer passed as an INPUT argument to a call we
        -- cannot see into (PrimCall / PrimHigher / foreign-C) escapes
        -- UNCONDITIONALLY, for two reasons:
        --   • the callee may store the pointer somewhere that outlives this
        --     proc (a global, the heap, an output it returns); and
        --   • the call may be tail-call-optimised, in which case this frame
        --     (and any stack allocation in it) is torn down while the callee
        --     keeps using the pointer.
        -- Tail-position is only decided later in the LLVM backend, so we are
        -- conservative here: a value reaching any such call argument is never
        -- stack-allocated.  This subsumes the weaker "input escapes if some
        -- output escapes" rule for these calls.
        callArgEsc = [ argVarName arg
                     | prim <- prims
                     , isConservativeCall prim
                     , let (allArgs, _) = primArgs prim
                     , arg@ArgVar{argVarFlow=inFlow} <- allArgs
                     , not (isOutputFlow inFlow) ]
        -- Seed (3): every pointer written into a global variable escapes.
        -- "lpvm store" stores its first argument into a global, which outlives
        -- this procedure.  This MUST be seeded here rather than relying on the
        -- alias map: the alias map is accumulated forward as the body is
        -- traversed, so at an alloc site it cannot see a store that occurs
        -- LATER in the body (the usual case — you build a value, then store it).
        storeEsc = [ argVarName val
                   | PrimForeign "lpvm" "store" _ (val:_) <- prims
                   , argIsVar val ]
        escaped0 = Set.fromList (outParamEsc ++ callArgEsc ++ storeEsc)
        -- For mutate(fIn, fOut, offset, destr, size, startOff, member, ...),
        -- if fOut escapes then:
        --   (a) fIn escapes (same struct, just a new version).  Note: this
        --       analysis runs before the destructive-update transformation sets
        --       the destr flag, so we conservatively treat fIn as escaping even
        --       for non-destructive mutates.  For a truly non-destructive mutate
        --       fIn would not escape (since fOut is a fresh copy), but we cannot
        --       determine that here.  This limits stack allocation for fIn in
        --       such cases.
        --   (b) any field value (member) stored into it also escapes,
        --       because that pointer will be embedded in the escaping struct.
        mutateEdges = [ (argVarName fOut, argVarName vin)
                | PrimForeign "lpvm" "mutate" _ args@(fIn:fOut:_) <- prims
                , argIsVar fIn
                , argIsVar fOut
                , vin <- fIn : [ m | m <- List.drop 6 args, argIsVar m ] ]
        -- For each remaining llvm/lpvm op, propagate escape backward from an
        -- output to an input.  An input escapes if an output of the SAME type
        -- escapes, OR if the op is value-preserving (lpvm cast / llvm move),
        -- which carries the same address into a result of a different type.
        -- (Conservative calls are handled by the callArgEsc seed above.)
        passEdges = [ (outName, inName)
                    | prim <- prims
                    , not (isAllocOrMutate prim)
                    , not (isConservativeCall prim)
                    , let (allArgs, _) = primArgs prim
                    , let valuePreserving = isValuePreserving prim
                    , ArgVar{argVarName=outName, argVarType=outType,
                             argVarFlow=outFlow} <- allArgs
                    , isOutputFlow outFlow
                    , ArgVar{argVarName=inName, argVarType=inType,
                             argVarFlow=inFlow} <- allArgs
                    , not (isOutputFlow inFlow)
                    , valuePreserving || inType == outType ]
        allEdges = mutateEdges ++ passEdges
        go escaped =
            let newEsc = Set.fromList
                            [ vin | (vout, vin) <- allEdges
                                  , Set.member vout escaped ]
                escaped' = Set.union escaped newEsc
            in if Set.size escaped' == Set.size escaped
               then escaped
               else go escaped'
    in go escaped0


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

    let escapedVars = computeEscapedVars proto body
    logTransform $ "escapedVars: " ++ show escapedVars

    let params = primProtoParams proto
    let outVarSubs = params
                    |> List.filter (isOutputFlow . primParamFlow)
                    |> List.map primParamName |> List.map (\x -> (x,x))
                    |> Map.fromList
    let tmp = procTmpCount procDef
    (_, tmp', _, _, _, body') <- buildBody tmp outVarSubs params $
                transformBody proto body (aliasMap, Map.empty, Set.empty)
                        callSiteMap escapedVars
    return (body', tmp')


-- The third component of the state tuple, "stackVars", is the set of variables
-- that denote stack-allocated memory (the result of a "{stack}" alloc, and
-- anything that shares that memory through a destructive mutate or a
-- value-preserving op).  It is used to forbid reusing a stack cell as a dead
-- cell (see "transformPrim"): handing stack memory to a fresh value is unsound
-- because that value may escape (or be passed to a tail call), leaving a live
-- pointer into a torn-down frame.
transformBody :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells, Set PrimVarName)
        -> Map CallSiteID ProcSpec -> Set PrimVarName -> BodyBuilder ()
transformBody caller body (aliasMap, deadCells, stackVars) callSiteMap escapedVars = do
    -- (1) Analysis of current caller's prims
    (aliaseMap', deadCells', stackVars') <-
            transformPrims caller body (aliasMap, deadCells, stackVars)
                    callSiteMap escapedVars

    -- (2) Analysis of caller's bodyFork
    -- Update body while checking alias incurred by bodyfork
    transformForks caller body (aliaseMap', deadCells', stackVars')
            callSiteMap escapedVars


-- Check alias created by prims of caller proc
transformPrims :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells, Set PrimVarName)
        -> Map CallSiteID ProcSpec -> Set PrimVarName
        -> BodyBuilder (AliasMapLocal, DeadCells, Set PrimVarName)
transformPrims caller body (aliasMap, deadCells, stackVars) callSiteMap escapedVars = do
    let prims = bodyPrims body
    -- Transform simple prims:
    lift $ logTransform "\nTransform prims (transformPrims):   "
    foldM (transformPrim callSiteMap escapedVars) (aliasMap, deadCells, stackVars) prims


-- Recursively transform forked body's prims
-- PrimFork only appears at the end of a ProcBody
-- PrimFork = NoFork | PrimFork {}
transformForks :: PrimProto -> ProcBody -> (AliasMapLocal, DeadCells, Set PrimVarName)
        -> Map CallSiteID ProcSpec -> Set PrimVarName -> BodyBuilder ()
transformForks caller body (aliasMap, deadCells, stackVars) callSiteMap escapedVars = do
    lift $ logTransform "\nTransform forks (transformForks):"
    let fork = bodyFork body
    case fork of
        PrimFork var ty _ fBodies deflt -> do
            buildFork var ty
            lift $ logTransform "Forking:"
            mapM_ (\(brNum, currBody) -> do
                    beginBranch brNum
                    transformBody caller currBody
                                (aliasMap, deadCells, stackVars) callSiteMap escapedVars
                    endBranch
                ) (List.map (mapFst Just) fBodies ++ maybeToList ((Nothing,) <$> deflt))
            completeFork
        MergedFork{} -> do
            lift $ logTransform "Unmerging fork:"
            fork' <- lift $ unMergeFork fork
            transformForks caller body{bodyFork=fork'} (aliasMap, deadCells, stackVars) callSiteMap escapedVars
        NoFork -> do
            -- NoFork: transform prims done
            lift $ logTransform "No fork."


-- Build up alias pairs triggerred by proc calls
transformPrim :: Map CallSiteID ProcSpec -> Set PrimVarName
        -> (AliasMapLocal, DeadCells, Set PrimVarName) -> Placed Prim
        -> BodyBuilder (AliasMapLocal, DeadCells, Set PrimVarName)
transformPrim callSiteMap escapedVars (aliasMap, deadCells, stackVars) prim = do
    -- XXX Redundent work here. We should change the current design.
    aliasMap' <- lift $ updateAliasedByPrim aliasMap prim
    lift $ logTransform $ "\n--- prim:           " ++ show prim
    let primc = content prim

    (primc', deadCells', stackVars') <- case primc of
            PrimCall id spec impurity args gFlows -> do
                doMultiSpecz <- lift $ gets (optimisationEnabled MultiSpecz . options)
                let spec' = if doMultiSpecz
                    then Map.findWithDefault spec id callSiteMap
                    else spec
                return (PrimCall id spec' impurity args gFlows, deadCells, stackVars)
            PrimForeign "lpvm" "mutate" flags args -> do
                let args' = _updateMutateForAlias aliasMap args
                -- A destructive mutate writes "fIn" in place, so "fOut" denotes
                -- the same memory: propagate stack-ness from fIn to fOut.
                let stackVars'' = propagateStackThroughMutate stackVars args'
                return (PrimForeign "lpvm" "mutate" flags args', deadCells, stackVars'')
            -- value-preserving ops carry the same address into their result, so
            -- stack-ness propagates from input to output (mirrors the
            -- pass-through edges in computeEscapedVars).
            PrimForeign "lpvm" "cast" _ args ->
                return (primc, deadCells, propagateStackThroughCopy stackVars args)
            PrimForeign "llvm" "move" _ args ->
                return (primc, deadCells, propagateStackThroughCopy stackVars args)
            -- dead cell transform
            PrimForeign "lpvm" "access" _ args -> do
                deadCells'
                    <- lift $ updateDeadCellsByAccessArgs (aliasMap, deadCells) args
                return (primc, deadCells', stackVars)
            PrimForeign "lpvm" "alloc" flags args  -> do
                let (result, deadCellsReused) =
                        assignDeadCellsByAllocArgs deadCells args
                -- [Stack allocation via escape analysis]
                -- Check if the alloc result escapes via:
                --   (a) the incremental alias map (globals, aliased params)
                --   (b) the pre-computed mutation-chain escape set
                let [sizeArg, outVar] = args
                -- NOTE: escapedByAlias is effectively INERT and never fires for
                -- an alloc's own result.  isArgEscaped queries `aliasMap`, the
                -- forward-accumulated map as it stands *before* this alloc; but
                -- outVar is created *by* this alloc, so it cannot yet be
                -- connected to any global/param in that map.  Empirically it is
                -- False for every alloc across the whole test suite.  The
                -- authoritative, sound check is escapedByMutation
                -- (computeEscapedVars), which scans the whole body and so sees
                -- escapes that occur after the alloc (the usual case: build a
                -- value, then store/return it).  escapedByAlias is kept only as
                -- a cheap, order-dependent early check that can add escapes but
                -- never remove them, so it cannot affect soundness.  See §4/§9
                -- of escape_analysis.md.
                let escapedByAlias = isArgEscaped aliasMap outVar
                let escapedByMutation = case outVar of
                        ArgVar{argVarName=n} -> Set.member n escapedVars
                        _                   -> True
                let escaped   = escapedByAlias || escapedByMutation
                -- NOTE: We only stack-allocate constant-sized allocs. LLVM does
                -- support variable-sized alloca (for C99 VLAs), but it forces a
                -- frame pointer, blocking tail-call optimisation. It also makes
                -- --stack-alloc-limit unenforceable at compile time. In practice
                -- this is not a limitation: Wybe types are always statically sized.
                let constSize = argIsConst sizeArg
                let alreadyStack = "stack" `List.elem` flags
                doStackAlloc <- lift $ gets (optimisationEnabled StackAlloc . options)
                stackLimit <- lift $ gets (optStackAllocLimit . options)
                let withinLimit = maybe False (<= stackLimit) (argIntVal sizeArg)
                -- A dead cell we'd reuse may itself be stack memory (it traces
                -- back through destructive mutates / casts to a "{stack}"
                -- alloc).  Reusing stack memory for a fresh value is unsound:
                -- that value may escape or reach a tail call, leaving a live
                -- pointer into a torn-down frame (the dead-cell reuse path does
                -- NOT otherwise consult the escape analysis).  So we refuse to
                -- reuse a stack cell and fall back to a fresh allocation, which
                -- the escape check then heap- or stack-allocates correctly.
                let reuseIsStack = case result of
                        Just ((selectedCell, _), _) ->
                            argIsStackVar stackVars selectedCell
                        Nothing -> False
                let doReuse = Maybe.isJust result && not reuseIsStack
                let willStackAlloc = not escaped && constSize && withinLimit
                                        && not alreadyStack && doStackAlloc
                                        && not doReuse
                lift $ logTransform $ "alloc result: " ++ show outVar
                        ++ " | escapedByAlias=" ++ show escapedByAlias
                        ++ " | escapedByMutation=" ++ show escapedByMutation
                        ++ " | constSize=" ++ show constSize
                        ++ " | withinLimit=" ++ show withinLimit
                        ++ " | alreadyStack=" ++ show alreadyStack
                        ++ " | reuseAvailable=" ++ show (Maybe.isJust result)
                        ++ " | reuseIsStack=" ++ show reuseIsStack
                        ++ (if doReuse then " => reuse dead cell"
                            else if willStackAlloc then " => stack-allocate"
                            else " => heap-allocate")
                let (primc', deadCells', stackVars'') =
                        if doReuse
                        then case result of
                            Just ((selectedCell, startOffset), []) ->
                                -- avoid "alloc" by reusing the "selectedCell".
                                let [_, varOut] = args in
                                -- Be aware that this will make the previous final
                                -- flag of "selectedCell" outdated.
                                -- TODO: we should consider using BodyBuilder for
                                -- the transform.
                                (PrimForeign "llvm" "sub" []
                                    [selectedCell, startOffset, varOut],
                                 deadCellsReused, stackVars)
                            _ -> shouldnt "invalid aliasMap for transform"
                        else if willStackAlloc
                        then ( PrimForeign "lpvm" "alloc" ("stack":flags) args
                             , deadCells
                             , case outVar of
                                 ArgVar{argVarName=n} -> Set.insert n stackVars
                                 _                    -> stackVars )
                        else (primc, deadCells, stackVars)
                when doReuse $
                        lift $ logTransform "avoid using [alloc]."
                return (primc', deadCells', stackVars'')
            -- default case
            _ -> return (primc, deadCells, stackVars)

    let pos = place prim
    lift $ logTransform $ "--- transformed to: " ++ show (maybePlace primc' pos)
    instr primc' pos
    return (aliasMap', deadCells', stackVars')


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


-- | True if the given arg is a variable denoting stack-allocated memory.
argIsStackVar :: Set PrimVarName -> PrimArg -> Bool
argIsStackVar stackVars ArgVar{argVarName=n} = Set.member n stackVars
argIsStackVar _ _                            = False


-- | Propagate stack-ness across a (possibly just-made-destructive) mutate.
-- A destructive mutate updates "fIn" in place and yields "fOut" as the same
-- memory, so if "fIn" is stack memory then "fOut" is too.  A non-destructive
-- mutate allocates a fresh copy for "fOut", so stack-ness does NOT carry over.
propagateStackThroughMutate :: Set PrimVarName -> [PrimArg] -> Set PrimVarName
propagateStackThroughMutate stackVars
    [fIn, ArgVar{argVarName=fOut}, _, ArgInt 1 _, _, _, _]
    | argIsStackVar stackVars fIn = Set.insert fOut stackVars
propagateStackThroughMutate stackVars _ = stackVars


-- | Propagate stack-ness across a value-preserving op (lpvm cast / llvm move),
-- whose standard form is [input, ?output]: if the input is stack memory, so is
-- the output (it holds the same address).
propagateStackThroughCopy :: Set PrimVarName -> [PrimArg] -> Set PrimVarName
propagateStackThroughCopy stackVars [inp, ArgVar{argVarName=out, argVarFlow=FlowOut}]
    | argIsStackVar stackVars inp = Set.insert out stackVars
propagateStackThroughCopy stackVars _ = stackVars

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
