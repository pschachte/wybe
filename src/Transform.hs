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

--  BEGIN MAJOR DOC
-- # Escape Analysis & Stack Allocation in the Wybe Compiler
--
-- This document explains how the Wybe compiler decides that some heap allocations
-- can safely become *stack* allocations, and how that decision is carried through
-- to the LLVM backend. It starts with the intuition and builds up to the precise
-- algorithm, the soundness argument, and the known limitations.
--
-- The relevant code lives in:
--
-- - [`src/Transform.hs`](/src/Transform.hs) — the analysis and the alloc-site decision.
-- - [`src/AliasAnalysis.hs`](/src/AliasAnalysis.hs) — the supporting alias check (`isArgEscaped`).
-- - [`src/LLVM.hs`](/src/LLVM.hs) — lowering a `{stack}` alloc to an `alloca`, and the tail-call interaction.
-- - [`src/Options.hs`](/src/Options.hs) — the `stack-alloc` optimisation flag and `--stack-alloc-limit`.
--
-- ---
--
-- ## 1. The intuition
--
-- When a Wybe program builds a structure — a tuple, a record, a list cell — the
-- compiler emits an `lpvm alloc` instruction that, by default, calls
-- `wybe_malloc` and gets memory from the **heap**. Heap memory is managed by the
-- Boehm garbage collector: it lives until nothing references it any more, and
-- reclaiming it costs CPU time.
--
-- But a great many allocations don't need to live that long. Consider:
--
-- ```wybe
-- def {noinline} distance(x1:int, y1:int, x2:int, y2:int):int use !io {
--     ?p = point(x1, y1)        # allocate a point
--     ?q = point(x2, y2)        # allocate another
--     (p^x - q^x) + (p^y - q^y) # read both, then we're done with them
-- }
-- ```
--
-- Here `p` and `q` are created, read a few times, and then forgotten. Nothing
-- outside `distance` ever sees them. Their lifetime is exactly the lifetime of
-- the call. That is *precisely* what the machine stack is for: memory that is
-- born when a function is entered and dies when it returns, reclaimed for free by
-- popping the stack frame.
--
-- So the optimisation is: **if a structure cannot outlive the procedure call that
-- created it, allocate it on the stack instead of the heap.** This removes GC
-- pressure and is usually faster.
--
-- The catch is the word *cannot*. If we put a structure on the stack and the
-- program keeps a pointer to it after the procedure returns, that pointer now
-- points into a stack frame that has been torn down and reused — a classic
-- **use-after-free**. Getting this wrong does not produce a compile error or a
-- clean crash; it produces silent garbage. So the analysis must be **sound**: it
-- may keep something on the heap that could have gone on the stack (a missed
-- optimisation), but it must **never** put something on the stack that escapes.
--
-- The analysis that answers "can this structure outlive its procedure?" is called
-- **escape analysis**. A structure *escapes* if a reference to it can survive past
-- the procedure's return.
--
-- ---
--
-- ## 2. How a value can escape
--
-- A pointer created inside a procedure can outlive that procedure in only a few
-- ways. The analysis must catch every one of them:
--
-- 1. **It is returned.** The pointer is written to an output parameter, so the
--    caller receives it.
--
-- 2. **It is passed to a call we can't see into.** Once a pointer is handed to
--    another procedure (a Wybe `PrimCall`), a higher-order call (`PrimHigher`), or
--    a foreign C function, that callee might stash it in a global, the heap, or
--    one of its own outputs. From this procedure's point of view, the pointer has
--    left the building.
--
-- 3. **It is stored into a global.** Wybe has no raw globals, but it has
--    *resources*, which lower to global variables. Writing a pointer into a
--    resource (`lpvm store` to a global) lets it outlive any single call.
--
-- 4. **It is embedded in another structure that escapes.** If we store pointer
--    `a` into structure `b` (via `lpvm mutate`), and `b` later escapes by any of
--    the routes above, then `a` escapes too — the escaping `b` carries `a` out
--    with it.
--
-- If none of these apply, the pointer is *captured* — confined to the procedure —
-- and is a candidate for stack allocation.
--
-- ---
--
-- ## 3. Where the analysis runs in the pipeline
--
-- Escape analysis is part of the **Transform** pass
-- ([`transformProcBody`](/src/Transform.hs)), which runs after alias analysis has
-- reached its fixed point. Transform already walks every procedure body to set
-- the *destructive* flag on `mutate` instructions (the in-place-update
-- optimisation). Stack allocation piggy-backs on that same walk.
--
-- For each (non-inline) procedure, Transform:
--
-- 1. Computes `escapedVars`, the set of variables that may escape — see
--    [`computeEscapedVars`](/src/Transform.hs) (§5). This is computed **once**,
--    up front, over the whole body.
-- 2. Walks the body instruction by instruction
--    ([`transformPrim`](/src/Transform.hs)), maintaining an incremental alias map.
-- 3. At each `lpvm alloc`, decides heap vs stack (§6).
--
-- One ordering fact matters a great deal and is the source of a subtle bug class
-- (see §9): the alias map in step 2 is built **forward** — at the point we reach
-- an alloc, it reflects only the parameters and the instructions *before* the
-- alloc. An escape caused by an instruction *after* the alloc is invisible to the
-- alias map. That is exactly why the up-front, whole-body `computeEscapedVars`
-- exists, and why it must be complete on its own.
--  END MAJOR DOC


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
                -- of this module's documentation.
                let escapedByAlias = isArgEscaped aliasMap outVar
                let escapedByMutation = case outVar of
                        ArgVar{argVarName=n} -> Set.member n escapedVars
                        _                   -> True
                let escaped   = escapedByAlias || escapedByMutation
                -- NOTE: We only stack-allocate constant-sized allocs. LLVM does
                -- support variable-sized alloca (for C99 VLAs), but it forces a
                -- frame pointer, blocking tail-call optimisation. It also makes
                -- --stack-alloc-limit unenforceable at compile time. In practice
                -- this is not much of a limitation: types defined through
                -- constructors are always statically sized, so their allocs have
                -- constant size. The variable-sized types (array, c_array,
                -- c_string) allocate a runtime-computed size and are correctly
                -- excluded here by the constSize check below.
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


--  BEGIN MAJOR DOC
-- ---
--
-- ## 4. The two escape checks
--
-- At an alloc site the analysis combines two independent checks
-- ([`transformPrim`, the `lpvm alloc` case](/src/Transform.hs)):
--
-- ```haskell
-- let escapedByAlias    = isArgEscaped aliasMap outVar
-- let escapedByMutation = Set.member n escapedVars
-- let escaped           = escapedByAlias || escapedByMutation
-- ```
--
-- - **`escapedByAlias`** ([`isArgEscaped` in `AliasAnalysis.hs`](/src/AliasAnalysis.hs)):
--   consults the *incremental* alias map. It returns `True` if the alloc result
--   is aliased to a global (`AliasByGlobal`), a parameter (`AliasByParam`), or a
--   maybe-aliased parameter (`MaybeAliasByParam`). Because the map is built
--   forward (§3), this check only catches aliasing established *before* the
--   alloc. It is therefore best understood as an *opportunistic early* check, not
--   the authoritative one.
--
--   **In practice this check is inert — it is always `False` for an alloc's own
--   result.** `isArgEscaped` queries the alias map *as it stands before this
--   alloc*, but `outVar` is created *by* this alloc, so it cannot yet be connected
--   to any global or parameter in that map. A sweep of the whole final-dump suite
--   confirms it: `escapedByAlias=True` appears in **zero** of the 57 alloc
--   decisions, while genuinely-escaping allocs are all caught by
--   `escapedByMutation`. The stored whole-body `procArgAliasMap` would not help
--   either — it is *parameter-level* and does not track local alloc temporaries.
--
--   It is kept (rather than deleted) because it is harmless: being part of an
--   `||`, it can only *add* escapes, never remove them, so it cannot make the
--   analysis unsound. But it must **not** be mistaken for a safety net covering
--   the global/parameter routes — it provides no such coverage. Treating it as
--   one is precisely the misconception that produced the original global-store
--   bug (§9): the authoritative, complete check is `escapedByMutation` alone.
--
-- - **`escapedByMutation`** ([`computeEscapedVars`](/src/Transform.hs)): the
--   whole-body, order-independent analysis. This is the authoritative check and
--   carries the soundness guarantee.
--
-- An alloc is stack-allocated only if **neither** check fires (and the size
-- constraints in §6 hold).
--
-- ---
--
-- ## 5. `computeEscapedVars` in detail
--
-- This function answers, for one procedure body, "which variables may escape?".
-- It works in two parts: **seeds** (variables that definitely escape) and
-- **edges** (a may-point-to graph along which escape propagates backward). It then
-- takes the least fixed point.
--
-- ### 5.1 Collecting the instructions
--
-- ```haskell
-- prims = collectAllBodyPrims body
-- ```
--
-- [`collectAllBodyPrims`](/src/Transform.hs) flattens every instruction in the
-- body, **including all branches of every fork**. This is deliberately
-- conservative: the analysis ignores control flow entirely and treats the body as
-- one flat bag of instructions. If a value escapes on *any* path, it is treated
-- as escaping on *all* paths. (Recall LPVM is roughly SSA — variables are uniquely
-- named — so merging branches into one set does not conflate distinct values.)
--
-- ### 5.2 The seeds — variables that definitely escape
--
-- ```haskell
-- escaped0 = Set.fromList (outParamEsc ++ callArgEsc ++ storeEsc)
-- ```
--
-- **Seed 1 — output parameters** (`outParamEsc`). Every output parameter escapes
-- by definition: the caller receives its value.
--
-- **Seed 2 — arguments to opaque calls** (`callArgEsc`). Every pointer passed as a
-- non-output argument to a call we cannot analyse escapes *unconditionally*. The
-- predicate is [`isConservativeCall`](/src/Transform.hs):
--
-- ```haskell
-- isConservativeCall PrimCall{}               = True   -- user-defined Wybe call
-- isConservativeCall PrimHigher{}             = True   -- higher-order call
-- isConservativeCall (PrimForeign lang _ _ _) = lang /= "llvm" && lang /= "lpvm"  -- e.g. C
-- ```
--
-- There are two reasons this is unconditional, not "escapes only if the call's
-- output escapes":
--
-- - The callee may retain the pointer (store it in a global, the heap, or an
--   output).
-- - The call may be **tail-call optimised**. TCO reuses the current stack frame
--   for the callee. If a stack-allocated pointer from this frame were passed to a
--   tail call, the frame — and the allocation — would be torn down while the
--   callee still uses it. Tail position is only decided much later, in the LLVM
--   backend, so we cannot know here which calls will be tail calls. Treating every
--   pointer reaching such a call as escaping side-steps the question entirely.
--
-- **Seed 3 — values stored into globals** (`storeEsc`). Every pointer that is the
-- value argument of an `lpvm store` escapes. `lpvm store` writes into a global
-- variable (a Wybe resource), which outlives any single call:
--
-- ```haskell
-- storeEsc = [ argVarName val
--            | PrimForeign "lpvm" "store" _ (val:_) <- prims
--            , argIsVar val ]
-- ```
--
-- This seed *must* live here rather than relying on the alias map. The store that
-- makes a value escape almost always comes *after* the value is built (`?c =
-- cell(...)` then `?global = c`), so the forward alias map at the alloc site
-- cannot see it. `computeEscapedVars` scans the whole body, so it does.
--
-- ### 5.3 The edges — how escape propagates
--
-- Escape flows *backward*: if a value escapes, the values that flow *into* it also
-- escape. There are two kinds of edge.
--
-- **Mutate edges.** For `mutate(fIn, fOut, offset, destr, size, startOff,
-- member)` — which produces `fOut`, a copy of `fIn` with one field set to
-- `member`:
--
-- ```haskell
-- mutateEdges = [ (argVarName fOut, argVarName vin)
--         | PrimForeign "lpvm" "mutate" _ args@(fIn:fOut:_) <- prims
--         , argIsVar fIn, argIsVar fOut
--         , vin <- fIn : [ m | m <- List.drop 6 args, argIsVar m ] ]
-- ```
--
-- The edge `(fOut, vin)` means "if `fOut` escapes, then `vin` escapes." Two things
-- flow in:
--
-- - `fIn` — the struct being updated. `fOut` is just a new version of it, so if
--   the new version escapes, so does the old. (This is conservative for
--   *non-destructive* mutates, where `fOut` is genuinely a fresh copy and `fIn`
--   need not escape — but escape analysis runs *before* the destructive-update
--   transformation sets the `destr` flag, so it cannot yet tell the two apart.
--   See §9.)
-- - `member` — the field value being stored *into* the struct. If the struct
--   escapes, the embedded pointer escapes with it. This is route 4 from §2.
--
-- Because mutates form a chain (`s0 = alloc; s1 = mutate s0; s2 = mutate s1; …`),
-- these edges chain too: if the final version `sN` escapes, escape propagates back
-- through every intermediate version and every member stored along the way.
--
-- **Pass-through edges.** For any other `llvm`/`lpvm` instruction that is not an
-- alloc, mutate, or opaque call:
--
-- ```haskell
-- passEdges = [ (outName, inName)
--             | prim <- prims
--             , not (isAllocOrMutate prim)
--             , not (isConservativeCall prim)
--             , ...
--             , ArgVar{...outName, outType, outFlow} <- allArgs, isOutputFlow outFlow
--             , ArgVar{...inName,  inType,  inFlow}  <- allArgs, not (isOutputFlow inFlow)
--             , valuePreserving || inType == outType ]
-- ```
--
-- This adds an edge from each output to each input when either:
--
-- - the instruction is **value-preserving** ([`isValuePreserving`](/src/Transform.hs)
--   — `lpvm cast` or `llvm move`), which carries the *same address* into a result
--   of a possibly different type; or
-- - the input and output have the **same type**, a conservative proxy for "the
--   address might be passed through."
--
-- ### 5.4 The fixed point
--
-- ```haskell
-- go escaped =
--     let newEsc = Set.fromList [ vin | (vout, vin) <- allEdges, Set.member vout escaped ]
--         escaped' = Set.union escaped newEsc
--     in if Set.size escaped' == Set.size escaped then escaped else go escaped'
-- ```
--
-- Starting from the seeds, repeatedly add any `vin` whose `vout` is already known
-- to escape, until nothing new is added. The result is every variable from which
-- an escaping value is reachable backward through the graph. Allocs whose result
-- is **not** in this set are escape-free.
--
-- ---
--
-- ## 6. The alloc-site decision
--
-- Back in [`transformPrim`](/src/Transform.hs), for `lpvm alloc(size, ?out)`:
--
-- ```haskell
-- let escaped      = escapedByAlias || escapedByMutation
-- let constSize    = argIsConst sizeArg               -- size known at compile time?
-- let alreadyStack = "stack" `elem` flags
-- let withinLimit  = maybe False (<= stackLimit) (argIntVal sizeArg)
-- -- (stackLimit and doStackAlloc are read from the compiler options)
-- ```
--
-- The alloc becomes a stack alloc — tagged with a `{stack}` flag — only when **all**
-- of:
--
-- - `not escaped` — the escape analysis cleared it;
-- - `constSize` — the size is a compile-time constant;
-- - `withinLimit` — the size is at or below `--stack-alloc-limit` (default 4096
--   bytes, see [`Options.hs`](/src/Options.hs));
-- - `not alreadyStack` — idempotence;
-- - `doStackAlloc` — the `stack-alloc` optimisation is enabled.
--
-- Otherwise it stays a heap alloc.
--
-- **Why require a constant size?** LLVM can do variable-sized `alloca` (C99 VLAs),
-- but a dynamic `alloca` forces a frame pointer, which blocks tail-call
-- optimisation, and makes `--stack-alloc-limit` impossible to enforce at compile
-- time. In practice this costs nothing: Wybe types are always statically sized.
--
-- **Why a size limit?** Stack space is finite and a single oversized `alloca` (or
-- one inside a deep recursion) can blow the stack. The limit keeps stack usage
-- bounded; anything larger falls back to the heap.
--
-- ---
--
-- ## 7. Lowering to LLVM
--
-- A `{stack}`-tagged alloc reaches the backend in
-- [`writeLPVMCall "alloc"`](/src/LLVM.hs):
--
-- ```haskell
-- if "stack" `elem` flags
-- then case argIntVal sz of
--     Just sizeVal -> do
--         (writeTmp, readTmp) <- freshTempArgs $ Representation CPointer
--         stackAlloc writeTmp (fromIntegral sizeVal)   -- emit `alloca i8, i64 N`
--         typeConvert readTmp out                      -- ptrtoint to the i64 Wybe uses
--     Nothing -> shouldnt "stack alloc with non-constant size"
-- else heapAlloc out sz pos                            -- the normal wybe_malloc path
-- ```
--
-- [`stackAlloc`](/src/LLVM.hs) emits the `alloca` and records the result in
-- `stackAllocedVars`. Wybe represents pointers as `i64`, so the raw `ptr` from
-- `alloca` is immediately `ptrtoint`-converted to the variable the rest of the
-- code expects.
--
-- ### Keeping track of stack-allocated addresses
--
-- The backend maintains a set, `stackAllocedVars`, of variables that hold a
-- stack address:
--
-- - [`recordStackAlloced`](/src/LLVM.hs) adds the `alloca` result.
-- - [`propagateStackAlloced`](/src/LLVM.hs), called from `typeConvert`, follows the
--   address through moves and pointer conversions (`ptrtoint`, casts) so that
--   LLVM-level renaming doesn't lose track of which `i64` values are really stack
--   addresses. It is also called explicitly across the `llvm add` that forms a
--   non-zero-offset *interior* pointer in the `mutate` lowering (which does not go
--   through `typeConvert`), so that the address of a field of a stack struct is
--   tracked as a stack address too — see §9, point 5.
--
-- This set powers the tail-call check (§8).
--
-- ---
--
-- ## 8. Interaction with tail calls
--
-- Tail-call optimisation reuses the current frame for the callee. That is fatal if
-- the callee receives a pointer into the current frame's `alloca` space — the
-- frame is gone but the pointer is still used.
--
-- Earlier the backend used a single boolean `doesAlloca`: *any* `alloca` in a body
-- blocked *all* tail calls in it. The current design is more precise. At each call,
-- [`tailMarker`](/src/LLVM.hs) checks whether any input argument *actually*
-- references a stack-allocated variable:
--
-- ```haskell
-- tailMarker must ins = do
--     stackVars <- gets stackAllocedVars
--     let passesStackVar = any (\arg -> case arg of
--             ArgVar{argVarName=n} -> Set.member n stackVars
--             _                    -> False) ins
--     return $ case (passesStackVar, must) of
--         (True,_)      -> ""            -- stack address flows in: no tail marker
--         (False,True)  -> "musttail "
--         (False,False) -> "tail "
-- ```
--
-- If no input references a stack address, TCO is still safe even when the body
-- contains other `alloca`s, because escape analysis has already guaranteed those
-- allocations do not reach this callee.
--
-- (Note the two layers reinforce each other: escape analysis already refuses to
-- stack-allocate anything passed to a Wybe/foreign call — seed 2 — so in practice
-- a stack address rarely reaches a call argument at all. The `tailMarker` check is
-- the backend's belt-and-suspenders guarantee for the addresses that legitimately
-- flow into inlined `llvm`/`lpvm` operations.)
--
-- ---
--
-- ## 9. Known conservative limitations
--
-- These are *imprecisions*, not *unsoundness* — they cause missed optimisations,
-- never use-after-free.
--
-- 1. **Non-destructive mutate treats `fIn` as escaping.** Because escape analysis
--    runs before the destructive-update transformation, it cannot tell a
--    destructive mutate (writes `fIn` in place) from a non-destructive one
--    (produces a fresh `fOut`). For a truly non-destructive mutate, `fIn` need not
--    escape when `fOut` does. Recovering this would need either a preliminary
--    sub-pass to annotate `destr` flags before escape analysis, or marking
--    stack-friendly mutates directly (`{stack}` on the mutate).
--
-- 2. **Pass-through to opaque calls is always an escape.** A value passed to a
--    `pass_back(p, ?q)`-style call that merely returns its argument is treated as
--    escaping, even when the result is used purely locally. Recovering this
--    soundly requires interprocedural escape *summaries* plus tail-position
--    analysis (a later, more precise pass).
--
-- 3. **Branch-insensitivity.** Escaping on any path marks a value as escaping on
--    all paths (§5.1).
--
-- ### Bugs this design originally had (now fixed)
--
-- **Bug 1 — stores into a global were missed.** `computeEscapedVars` did not have
-- seed 3, and so missed pointers stored into a global *after* their alloc — the
-- forward alias map couldn't see the later store either, so such a value was
-- wrongly stack-allocated. The symptom was a global resource pointing into a
-- freed stack frame:
--
-- ```wybe
-- resource saved:cell = cell(0, 0)
-- def {noinline} stash(x:int) use !saved {
--     ?c = cell(x, x)    # built locally...
--     ?saved = c         # ...then stored into a global: it ESCAPES
-- }
-- ```
--
-- Adding seed 3 (`storeEsc`) closed the hole. The regression tests are
-- [`test-cases/execution/stack_alloc_global_escape.wybe`](/test-cases/execution/stack_alloc_global_escape.wybe)
-- (catches the miscompilation at runtime) and
-- [`test-cases/final-dump/stack_alloc_global.wybe`](/test-cases/final-dump/stack_alloc_global.wybe)
-- (asserts no stray `{stack}` flag in the IR).
--
-- **Bug 2 — dead-cell reuse handed stack memory to an escaping value.** This one
-- is the most subtle, and it is a three-way interaction between stack allocation,
-- the *destructive-update* transformation, and *dead-cell reuse* (CTGC) — all of
-- which happen in the same Transform pass, in that order, **after**
-- `computeEscapedVars`.
--
-- Wybe already has a compile-time-garbage-collection optimisation: when a
-- structure is provably dead (read by an `lpvm access` while unaliased and final),
-- its memory is recorded as a *dead cell* and the next same-sized `alloc` is
-- rewritten to **reuse** it (an `llvm sub` off the dead cell's address) instead of
-- allocating fresh. Crucially, that reuse path in
-- [`transformPrim`](/src/Transform.hs) does **not** consult the escape analysis.
--
-- Now consider:
--
-- ```wybe
-- resource saved:cell = cell(0, 0)
-- def {noinline} stash(x:int) use !saved {
--     ?c = cell(x, x)    # c is local -> escape analysis STACK-allocates it
--     ?tmp = c^a         # read c -> c is now a dead cell
--     ?d = cell(tmp, x)  # same size as c -> reuses c's memory
--     ?saved = d         # d ESCAPES via the global
-- }
-- ```
--
-- The two field writes that build `c` become *destructive* mutates (set after
-- escape analysis), so the dead cell's memory *is* `c`'s stack slot. Dead-cell
-- reuse then gives that stack memory to `d` — which escapes into `saved`. The
-- global ends up pointing into a torn-down frame: a use-after-free that prints
-- silent garbage (and only with `stack-alloc` enabled).
--
-- The fix threads a set of **stack variables** through the transform: the result
-- of every `{stack}` alloc, plus anything that comes to share that memory through
-- a destructive mutate or a value-preserving op (`lpvm cast` / `llvm move`). At a
-- reuse site, if the dead cell is a stack variable the reuse is **refused** and a
-- fresh allocation is emitted instead — which the escape check then heap-allocates
-- (because the new value escapes) or stack-allocates afresh (if it is local).
-- Reuse of *heap* dead cells — the common and valuable CTGC case, e.g. a
-- functional update that returns the updated record — is unaffected, because such
-- dead cells never enter the stack-variable set.
--
-- The regression test is
-- [`test-cases/execution/stack_alloc_reuse_escape.wybe`](/test-cases/execution/stack_alloc_reuse_escape.wybe)
-- (catches the miscompilation at runtime; the bug is invisible in the dumped IR
-- beyond the presence of an `llvm sub` reuse).
--
-- ### Audit of every transformation that runs *after* the escape decision
--
-- Both bugs above were *later passes re-routing memory the escape analysis had
-- already judged*. To be confident there are no more, here is every transformation
-- that touches a proc body after `computeEscapedVars` has fixed the `{stack}` flag,
-- with the reason each is sound. (Pass order, from
-- [`Builder.hs`](/src/Builder.hs): OPTIMISE/inlining → ANALYSIS → TRANSFORM/escape
-- analysis → LAST CALL ANALYSIS, then later the top-down multi-specialisation pass
-- re-runs TRANSFORM.)
--
-- 1. **Inlining** runs *before* escape analysis, so an inlined alloc is judged in
--    the caller's context. Inline procs are themselves never transformed
--    (`transformProcBody` rejects them). Nothing to break.
-- 2. **Destructive-update transformation** (same pass, after the escape set is
--    computed). `computeEscapedVars` already treats a mutate's input as escaping
--    whenever its output does, *regardless of the destr flag*, so turning a mutate
--    destructive never enlarges the set of reachable-after-return values.
-- 3. **Dead-cell reuse (CTGC)** — Bug 2. Fixed by the stack-variable set.
-- 4. **Last-call analysis: `FlowOut` → `FlowOutByReference` on the proc's output
--    param.** When the specz pass re-runs `computeEscapedVars` on the rewritten
--    body, `isOutputFlow FlowOutByReference` is `True`, so the param is still seed 1
--    — the escaped set cannot shrink.
-- 5. **Last-call analysis: `FlowTakeReference` on a mutate member + a resulting
--    tail call.** This hands the *address of a struct field* to the callee. It is
--    sound because **every struct LCA take-references is connected to the proc's
--    output** (that connection is precisely why the deferral is valid), so escape
--    analysis always heap-allocates it — verified empirically: the canonical
--    "build a struct, fill its non-first field with the last call's result, return
--    it" pattern emits `wybe_malloc`, never `{stack}`. The only way to get a *local*
--    (non-escaping) struct in that position is for its post-call write to be dead,
--    and a dead mutate is eliminated by the backward pass *before* LCA sees it
--    (also verified: the body collapses to just the tail call). A latent
--    fragility remains — `propagateStackAlloced` (§8) was not applied across the
--    `llvm add` that computes a non-zero-offset interior pointer, so the LLVM-level
--    tail-call guard had an asymmetry (offset 0 protected, offset ≠ 0 not). It is
--    unreachable today for the reason just given, but a one-line defensive
--    propagation now closes it so the guard does not silently depend on the
--    escape-analysis ⟺ LCA invariant holding forever.
-- 6. **`convertOutByRefArg` allocating a fresh slot** for an out-by-reference arg
--    at a *non*-tail call site stack-allocates a temporary, records it, and
--    suppresses the call's tail marker (it must load the result afterward). Sound.
-- 7. **The multi-specialisation top-down re-run of TRANSFORM.** It re-runs the same
--    conservative `computeEscapedVars` on the LCA-rewritten body. A specialised
--    alias map can only make *more* mutates destructive or enable *more* reuse —
--    neither of which shrinks the escaped set (point 2) and the latter is guarded
--    (point 3). It cannot newly stack-allocate something an earlier pass kept on the
--    heap and LCA then relied on.
-- 8. **LLVM tail-call optimisation** itself is the headline interaction, handled by
--    `tailMarker`/`stackAllocedVars` — see §8.
--
-- The thread common to all of these: a later pass is only dangerous if it lets a
-- stack address reach a point the escape analysis did not model. Each one either
-- runs before the analysis, preserves the conservative escaped set when the
-- analysis is re-run, or is caught by a dedicated guard (the stack-variable set in
-- TRANSFORM, and `stackAllocedVars` in LLVM lowering).
--
-- ---
--
-- ## 10. Soundness, informally
--
-- Stack allocation of an alloc `A` is sound iff `A`'s address cannot be referenced
-- after the procedure returns. The analysis guarantees this by ensuring that if
-- `A` could be referenced afterward, `A`'s result variable lands in `escaped`:
--
-- - **Returned** → the variable flows to an output parameter; output params are
--   seed 1, and mutate/pass-through edges propagate escape backward to `A`.
-- - **Passed to an opaque call** → seed 2 marks it directly.
-- - **Stored to a global** → seed 3 marks the stored value; mutate edges propagate
--   to anything embedded in it.
-- - **Embedded in an escaping struct** → mutate edges propagate from the struct to
--   the member.
--
-- Every escape route from §2 maps onto a seed or an edge, and the seeds are all
-- computed over the *whole* body (order-independent), so an escape anywhere in the
-- procedure is caught regardless of where the alloc sits relative to it. The
-- soundness guarantee therefore rests entirely on `escapedByMutation`
-- (`computeEscapedVars`); the order-dependent `escapedByAlias` check is inert for
-- alloc results (§4) and contributes nothing, but since it sits in an `||` it can
-- only ever *add* escapes, so its presence cannot break soundness.
--
-- One caveat completes the argument: a *later* transform must not re-route a
-- stack address to a value the escape analysis never saw. Dead-cell reuse (CTGC)
-- can do exactly that — it rewrites a fresh alloc to reuse dead memory without
-- re-checking escape — so soundness additionally requires that **a stack-allocated
-- dead cell is never reused** (§9, Bug 2). With that rule in place, every value
-- that reuses memory either reuses heap memory (which outlives the frame) or is
-- allocated afresh and re-judged by the escape check.
--
-- ---
--
-- ## 11. Trying it yourself
--
-- Dump the analysis decisions for a file:
--
-- ```sh
-- cd test-cases
-- ../wybemk --log=Transform --force-all -n -L ../wybelibs final-dump/stack_alloc.o 2>&1 \
--     | grep -E "escapedVars:|alloc result:"
-- ```
--
-- Each alloc prints a line like:
--
-- ```
-- alloc result: ?tmp#3##0:... | escapedByAlias=False | escapedByMutation=False
--     | constSize=True | withinLimit=True | alreadyStack=False
--     | reuseAvailable=False | reuseIsStack=False => stack-allocate
-- ```
--
-- The decision suffix is one of `=> reuse dead cell`, `=> stack-allocate`, or
-- `=> heap-allocate`. `reuseIsStack=True` is the Bug 2 guard firing: a dead cell
-- that traces back to a `{stack}` alloc is refused for reuse (so `reuseAvailable`
-- is `True` but the alloc still stack- or heap-allocates afresh).
--
-- Toggle the optimisation off to compare behaviour:
--
-- ```sh
-- ../wybemk --force-all -x no-stack-alloc -L ../wybelibs execution/<name>
-- ```
--
-- Adjust the size threshold:
--
-- ```sh
-- ../wybemk --force-all --stack-alloc-limit 256 -L ../wybelibs <target>
-- ```
--  END MAJOR DOC
