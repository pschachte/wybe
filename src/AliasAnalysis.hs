--  File     : AliasAnalysis.hs
--  Author   : Ting Lu, Zed(Zijun) Chen
--  Purpose  : Alias analysis for a single module
--  Copyright: (c) 2018-2019 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE LambdaCase #-}

module AliasAnalysis (
    AliasMapLocal, aliasSccBottomUp, currentAliasInfo,
    isAliasInfoChanged, updateAliasedByPrim, isArgUnaliased, isArgEscaped,
    isArgVarUsedOnceInArgs, DeadCells, updateDeadCellsByAccessArgs,
    assignDeadCellsByAllocArgs
    ) where

import           AST
import           Control.Monad
import           Data.Graph    (SCC(..))
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Data.Maybe    as Maybe
import           Data.Tuple.Extra
import           Flow          ((|>))
import           Options       (LogSelection (Analysis))
import           PointsToGraph
import           Util
import           Config        (specialName2)
import Data.Maybe.HT (toMaybe)


-- The intraprocedural working state is a field- and direction-sensitive
-- "PointsToGraph" (see "PointsToGraph.hs"), replacing the old Steensgaard-style
-- union-find.  At proc exit it is projected ("projectSummary") onto the
-- serialized "ProcPTGSummary" (defined in "AST.hs"): a portable, field/
-- direction/escape-sensitive projection of the graph onto the nodes visible
-- across the call boundary.  This replaces the old coarse "AliasMap"
-- ("DisjointSet PrimVarName" of may-alias params), carrying far more
-- information to callers (and future analyses).  A call site re-inflates the
-- summary onto the caller's graph via "instantiateSummary".  See
-- "points_to_graph.md" §5.
type AliasMapLocal = PointsToGraph


-- For each size, record all reusable cells, more on this can be found under
-- the "Dead Memory Cell Analysis" section below.
-- Each reusable cell is recorded as "((var, startOffset), requiredParams)".
-- "var" is the variable (copy from it's last access) that can be reused
-- and requiredParams is a list of parameters that need to be non-aliased
-- before reusing that cell (caused by "MaybeAliasByParam").
type DeadCells = Map Int [((PrimArg, PrimArg), [PrimVarName])]


-- Intermediate data structure used during the analysis
type AnalysisInfo =
    (AliasMapLocal, Set InterestingCallProperty, MultiSpeczDepInfo, DeadCells)


aliasSccBottomUp :: SCC ProcSpec -> Compiler ()
aliasSccBottomUp (AcyclicSCC single) = do
    _ <- aliasProcBottomUp single -- immediate fixpoint if no mutual dependency
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


currentAliasInfo :: SCC ProcSpec
        -> Compiler [(ProcPTGSummary, Set InterestingCallProperty)]
currentAliasInfo (AcyclicSCC single) = do
    def <- getProcDef single
    let ProcDefPrim{procImplnAnalysis = analysis} = procImpln def
    return [extractAliasInfoFromAnalysis analysis]
currentAliasInfo procs@(CyclicSCC multi) =
    foldM (\info pspec -> do
        def <- getProcDef pspec
        let ProcDefPrim{procImplnAnalysis = analysis} = procImpln def
        return $ info ++ [extractAliasInfoFromAnalysis analysis]
        ) [] multi


-- extract "ProcPTGSummary" and "Set InterestingCallProperty" from
-- the given "ProcAnalysis"
extractAliasInfoFromAnalysis :: ProcAnalysis
        -> (ProcPTGSummary, Set InterestingCallProperty)
extractAliasInfoFromAnalysis analysis =
    (procArgPTGSummary analysis, procInterestingCallProperties analysis)

-- This comparison is CRUCIAL. The underlying data struct should
-- handle equal CORRECTLY.
isAliasInfoChanged :: (ProcPTGSummary, Set InterestingCallProperty)
                    -> (ProcPTGSummary, Set InterestingCallProperty) -> Bool
isAliasInfoChanged = (/=)

aliasProcBottomUp :: ProcSpec -> Compiler Bool
aliasProcBottomUp pspec = do
    logAlias $ replicate 50 '-'
    logAlias $ "Alias analysis proc (Bottom-up): " ++ show pspec
    logAlias $ replicate 50 '-'

    oldDef <- getProcDef pspec
    let ProcDefPrim{procImplnAnalysis = oldAnalysis} = procImpln oldDef
    -- Update alias analysis info to this proc
    updateProcDefM aliasProcDef pspec
    -- Get the new analysis info from the updated proc
    newDef <- getProcDef pspec
    let ProcDefPrim{procImplnAnalysis = newAnalysis} = procImpln newDef
    -- And compare if the [AliasInfo] changed.
    let oldAliasInfo = extractAliasInfoFromAnalysis oldAnalysis
    let newAliasInfo = extractAliasInfoFromAnalysis newAnalysis
    logAlias "================================================="
    logAlias $ "old: " ++ show oldAliasInfo
    logAlias $ "new: " ++ show newAliasInfo
    return $ isAliasInfoChanged oldAliasInfo newAliasInfo
    -- XXX wrong way to do this. Need to change type signatures of a bunch of
    -- functions start from aliasProcDef which is called by updateProcDefM


-- Check if any argument become stale in this (not inlined) proc call
-- Return updated ProcDef and a flag (indicating if proc analysis info changed)
aliasProcDef :: ProcDef -> Compiler ProcDef
aliasProcDef def
    | not (procInline def) = do
        let oldImpln@(ProcDefPrim _ caller body oldAnalysis speczBodies) =
             procImpln def
        logAlias $ show caller

        realParams <- (primParamName <$>) <$> protoRealParams caller
        -- Seed the entry graph: every real parameter is a maybe-aliased external
        -- node (its external aliasing is unknown until multi-spec proves it).
        let initAliasMap = List.foldl (flip seedParam) emptyPTG realParams

        -- Actual analysis
        (aliasMap, interestingCallProperties, multiSpeczDepInfo, _) <-
                aliasedByBody caller body
                    (initAliasMap, Set.empty, Map.empty, Map.empty)

        -- Project the final points-to graph onto the serialized, portable
        -- summary carrying field edges / pass-through aliases / escape.
        let summary = projectSummary caller aliasMap
        logAlias $ "^^^  PTG summary: " ++ showProcPTGSummary summary
        -- Update proc analysis with the new summary
        let newAnalysis =
                oldAnalysis {
                    procArgPTGSummary = summary,
                    procInterestingCallProperties = interestingCallProperties,
                    procMultiSpeczDepInfo = multiSpeczDepInfo}
        return $
            def { procImpln = oldImpln { procImplnAnalysis = newAnalysis } }
aliasProcDef def = return def


-- Analysis a "ProcBody".
aliasedByBody :: PrimProto -> ProcBody -> AnalysisInfo -> Compiler AnalysisInfo
aliasedByBody caller body analysisInfo =
    aliasedByPrims caller body analysisInfo >>=
    aliasedByFork caller body


-- Check alias created by prims of caller proc
aliasedByPrims :: PrimProto -> ProcBody -> AnalysisInfo -> Compiler AnalysisInfo
aliasedByPrims caller body analysisInfo = do
    let prims = bodyPrims body
    -- Analyse simple prims:
    -- (only process alias pairs incurred by move, access, cast)
    logAlias "\nAnalyse prims (aliasedByPrims):    "
    foldM (aliasedByPrim caller) analysisInfo prims


-- Recursively analyse forked body's prims
-- PrimFork only appears at the end of a ProcBody
aliasedByFork :: PrimProto -> ProcBody -> AnalysisInfo -> Compiler AnalysisInfo
aliasedByFork caller body analysisInfo = do
    logAlias "\nAnalyse forks (aliasedByFork):"
    let fork = bodyFork body
    case fork of
        PrimFork _ _ _ fBodies deflt -> do
            logAlias ">>> Forking:"
            analysisInfos <-
                mapM (\body' -> aliasedByBody caller body' analysisInfo)
                    $ List.map snd fBodies ++ maybeToList deflt
            return $ mergeAnalysisInfo analysisInfos
        MergedFork{} -> do
            logAlias ">>> Merged fork:"
            fork' <- unMergeFork fork
            aliasedByFork caller body{bodyFork=fork'} analysisInfo
        NoFork -> do
            logAlias ">>> No fork."
            -- drop "deadCells", we don't need it after fork
            return analysisInfo


aliasedByPrim :: PrimProto -> AnalysisInfo -> Placed Prim
        -> Compiler AnalysisInfo
aliasedByPrim proto info prim = do
    let (aliasMap, interestingCallProperties, multiSpeczDepInfo, deadCells) =
            info
    aliasMap' <- updateAliasedByPrim aliasMap prim
    (interestingCallProperties', multiSpeczDepInfo')
        <- updateMultiSpeczInfoByPrim
            proto (aliasMap, interestingCallProperties, multiSpeczDepInfo) prim
    (interestingCallProperties'', deadCells')
        <- updateDeadCellsByPrim
            proto (aliasMap, interestingCallProperties', deadCells) prim
    return
        (aliasMap', interestingCallProperties'', multiSpeczDepInfo', deadCells')


-- merge a list of "AnalysisInfo" after fork.
mergeAnalysisInfo :: [AnalysisInfo] -> AnalysisInfo
mergeAnalysisInfo infos =
    let (aliasMapList, interestingCallPropertiesList,
            multiSpeczDepInfoList, deadCellsList) = List.unzip4 infos
        aliasMap = List.foldl joinPTG emptyPTG aliasMapList
        interestingCallProperties =
            List.foldl Set.union Set.empty interestingCallPropertiesList
        -- XXX there could be something better than "Map.unions"
        multiSpeczDepInfo = Map.unions multiSpeczDepInfoList
        -- We don't need "deadCells" after fork for now.
        deadCells = Map.empty
    in (aliasMap, interestingCallProperties, multiSpeczDepInfo, deadCells)


-- |Log a message, if we are logging optimisation activity.
logAlias :: String -> Compiler ()
logAlias = logMsg Analysis

----------------------------------------------------------------
--                 Proc Level Aliasing Analysis
----------------------------------------------------------------
-- Compute aliasMap on parameters for each procedure


-- | The transfer function (points_to_graph.md §4): fold the effect of one prim
-- onto the points-to graph, then drop dead (final) variables so they stop
-- acting as aliasing roots (matching the old @removeDeadVar@).  Pointer-ness
-- gates every edge -- a non-pointer argument contributes no aliasing.
updateAliasedByPrim :: AliasMapLocal -> Placed Prim -> Compiler AliasMapLocal
updateAliasedByPrim ptg placed = do
    let prim = content placed
    logAlias $ "--- transfer prim: " ++ show prim
    ptg' <- transferPrim ptg prim
    return $ dropFinalArgs ptg' (fst (primArgs prim))


-- | Apply one prim's points-to effect (before dead-var cleanup).
transferPrim :: PointsToGraph -> Prim -> Compiler PointsToGraph
transferPrim ptg prim = case prim of
    PrimCall _ spec _ args _ -> transferCall ptg spec args
    PrimForeign "lpvm" "alloc" _ [_, ArgVar{argVarName=out}] ->
        -- A fresh, unescaped local cell.
        return $ snd $ freshLocalNode out ptg
    PrimForeign "lpvm" "access" _ [struct, offset, _, _, member] ->
        transferAccess ptg struct offset member
    PrimForeign "lpvm" "mutate" flags args ->
        transferMutate ptg flags args
    PrimForeign "lpvm" "cast" _ [inp, outp] ->
        transferCopy False ptg inp outp
    PrimForeign "llvm" "move" _ [inp, outp] ->
        transferCopy True ptg inp outp
    PrimForeign "lpvm" "load" _ [ArgGlobal glob _, ArgVar{argVarName=out}] ->
        -- Anything read from a global is treated as the (escaping) global node.
        return $ addVarNodes out (Set.singleton (Node (GlobalNode glob))) ptg
    PrimForeign "lpvm" "store" _ [val, ArgGlobal glob _] ->
        transferStore ptg val glob
    -- Interior-pointer / tag-masking ops (TODO 2, TODO 11): `add`/`sub` compute
    -- an interior pointer into a base object; `and`/`or`/`xor` mask/unmask a
    -- boxed-constructor tag.  All are value-preserving w.r.t. the base address,
    -- so the result points into whatever the pointer operand(s) point to.
    PrimForeign "llvm" op _ args
        | op `elem` ["add", "sub", "and", "or", "xor"] ->
            transferInterior ptg args
    _ -> return ptg


-- | Wybe call: instantiate the callee's stored 'ProcPTGSummary' onto the
-- caller's graph (see 'instantiateSummary').  The rich summary carries field
-- edges (embedding), pass-through aliases, and escape, so the caller learns the
-- precise shape of what the callee did to its arguments and returned structures
-- -- far more than the old field-insensitive param-alias classes.
transferCall :: PointsToGraph -> ProcSpec -> [PrimArg] -> Compiler PointsToGraph
transferCall ptg spec args = do
    calleeDef <- getProcDef spec
    let ProcDefPrim _ calleeProto _ analysis _ = procImpln calleeDef
    instantiateSummary calleeProto args (procArgPTGSummary analysis) ptg


-- | The variable name of an 'ArgVar', if the arg is one.
argVarNameMaybe :: PrimArg -> Maybe PrimVarName
argVarNameMaybe ArgVar{argVarName=v} = Just v
argVarNameMaybe _                    = Nothing


----------------------------------------------------------------
--        Rich interprocedural summary (ProcPTGSummary)
----------------------------------------------------------------
-- The summary is the projection of a proc's final PointsToGraph onto the nodes
-- visible across the call boundary (points_to_graph.md §5).  It carries field
-- edges (embedding), direct pass-through aliases, and per-node escape -- far
-- more than the old field-insensitive param-alias classes.  Node identity is
-- made portable (ParameterID-keyed 'ExtNode') so the summary serializes into
-- object files and instantiates at any call site.


-- | Cap phantom nesting at depth 1 (K-limiting): a phantom successor of a
-- phantom folds back to the inner phantom, so a self-recursive proc cannot
-- accrete an unbounded phantom chain across the SCC fixpoint (points_to_graph.md
-- TODO 8).  This is the summary analogue of the recursive-type node collapse.
kLimitPhantom :: ExtNode -> ExtNode
kLimitPhantom (ExtPhantom inner@ExtPhantom{} _) = inner
kLimitPhantom e                                 = e


-- | Project the final local PointsToGraph onto the serialized 'ProcPTGSummary'.
-- Roots are the params' external nodes plus whatever their variables point to at
-- exit (so a freshly-built returned structure -- a 'LocalNode' bound to an
-- output param -- is folded into its 'ExtReturn', preserving the returned
-- shape; TODO 9).  A forward walk over the field edges records embeddings in
-- 'psEdges', materializing k-limited 'ExtPhantom's for local cells that have no
-- portable identity.  Pass-through identity (a var directly bound to another
-- param's memory) is lifted into 'psEdges' as a 'FieldIdent' edge from the output
-- to its source roots, and 'psEscape' records the per-node escape class.
projectSummary :: PrimProto -> PointsToGraph -> ProcPTGSummary
projectSummary proto ptg =
    let indexed  = List.zip [0..] (primProtoParams proto)
        -- name -> the external identity of that param's own node
        paramExt = Map.fromList
            [ (primParamName p
              , if isInputFlow (primParamFlow p) then ExtParam i else ExtReturn i)
            | (i, p) <- indexed ]
        -- The external identity of a node origin, if it has a portable one.  A
        -- LocalNode has none (it is folded into a root's ext / a phantom).
        extOfOrigin :: NodeOrigin -> Maybe ExtNode
        extOfOrigin o = case o of
            ParamNode nm       -> Map.lookup nm paramExt
            ReturnNode nm      -> Map.lookup nm paramExt
            GlobalNode g       -> Just (ExtGlobal g)
            ConstNode s        -> Just (ExtConst s)
            PhantomNode base f ->
                kLimitPhantom . (`ExtPhantom` f) <$> extOfOrigin base
            LocalNode _        -> Nothing
        -- Roots: (ext identity, node set) for every param.
        roots =
            [ (ext, Set.insert (Node (ParamNode nm)) (varNodes ptg nm))
            | (_, p) <- indexed
            , let nm = primParamName p
            , Just ext <- [Map.lookup nm paramExt] ]
        -- Seed the node -> ext map: an external-origin node keeps its own
        -- identity; a local node folds into the root's ext (a returned/param
        -- structure).
        seedXlate = List.foldl'
            (\m (ext, ns) -> List.foldl'
                (\m' n -> case extOfOrigin (nodeOrigin n) of
                            Just self -> Map.insert n self m'
                            Nothing   -> Map.insertWith (\_ old -> old) n ext m')
                m (Set.toList ns))
            Map.empty roots
        -- Forward walk: assign identities and collect field edges.
        (xlate, edges) = bfs seedXlate Map.empty (Map.keys seedXlate)
        bfs xl acc []        = (xl, acc)
        bfs xl acc (n:queue) =
            let e       = xl Map.! n
                flds    = Map.findWithDefault Map.empty n (ptgEdges ptg)
                pairs   = [ (f, t) | (f, ts) <- Map.toList flds, t <- Set.toList ts ]
                (xl', acc', new) = List.foldl' (step e) (xl, acc, []) pairs
            in bfs xl' acc' (new ++ queue)
        step e (xl, acc, new) (f, t) =
            case extOfOrigin (nodeOrigin t) of
                Just x  ->
                    let (xl', new') = if Map.member t xl
                                        then (xl, new)
                                        else (Map.insert t x xl, t : new)
                    in (xl', addEdge acc e f x, new')
                Nothing -> case Map.lookup t xl of
                    Just x  -> (xl, addEdge acc e f x, new)
                    Nothing ->
                        let ph = kLimitPhantom (ExtPhantom e f)
                        in (Map.insert t ph xl, addEdge acc e f ph, t : new)
        addEdge acc e f x =
            Map.insertWith (Map.unionWith Set.union) e
                (Map.singleton f (Set.singleton x)) acc
        -- Pass-through returns folded into node identity.  Two params whose root
        -- node sets directly overlap (e.g. `?out = in` binds out to in's node)
        -- share memory with no field indirection -- not expressible as an edge.
        -- Rather than a general alias-pair relation, this is recorded per *output*
        -- param as the set of other roots it shares memory with (its
        -- overlap-connected component minus itself): the input(s) it returns (a
        -- merge `if c then ?out=a else ?out=b` yields several), and/or sibling
        -- outputs returning the same memory.  An output that overlaps nothing is a
        -- genuinely fresh return and is omitted.  (Two *inputs* never overlap by
        -- identity -- their distinct 'ParamNode's meet only through an edge,
        -- already in 'psEdges' -- so every entry is anchored at an output; input
        -- args are not forced to alias each other, dropping the extra conservatism
        -- of the old pair relation.)
        overlapAdj = Map.fromListWith Set.union $ concat
            [ [(extA, Set.singleton extB), (extB, Set.singleton extA)]
            | ((extA, nsA) : rest) <- List.tails roots
            , (extB, nsB) <- rest
            , extA /= extB
            , not (Set.null (Set.intersection nsA nsB)) ]
        componentOf start = go Set.empty (Set.singleton start)
          where
            go seen frontier
                | Set.null frontier = seen
                | otherwise =
                    let seen' = Set.union seen frontier
                        nbrs  = Set.unions
                                  [ Map.findWithDefault Set.empty e overlapAdj
                                  | e <- Set.toList frontier ]
                    in go seen' (Set.difference nbrs seen')
        identEdges =
            [ (ExtReturn i, srcs)
            | (i, p) <- indexed
            , not (isInputFlow (primParamFlow p))
            , let srcs = Set.delete (ExtReturn i) (componentOf (ExtReturn i))
            , not (Set.null srcs) ]
        -- Lift the pass-through identity into the edge graph: each such output
        -- gets a 'FieldIdent' edge to its source roots, so 'psEdges' alone carries
        -- both containment (real field offsets) and identity aliasing.
        edgesWithIdent = List.foldl'
            (\acc (rj, srcs) ->
                Set.foldr (\s a -> addEdge a rj FieldIdent s) acc srcs)
            edges identEdges
        -- Escape class per external node (only the non-trivial entries).
        escapes = Map.fromListWith joinEscape
            [ (e, esc)
            | (n, e) <- Map.toList xlate
            , let esc = escapeOf ptg n
            , esc /= NoEscape ]
    in ProcPTGSummary { psEdges  = edgesWithIdent
                      , psEscape = escapes }


-- | Instantiate a callee's 'ProcPTGSummary' onto the caller's graph at a call
-- site (points_to_graph.md §5.2).  Build a substitution σ mapping each callee
-- 'ExtNode' to the caller nodes it stands for -- input params to the actual
-- argument's nodes (minting a fresh node when the caller arg is nodeless, so
-- the union-find variable-identity is preserved), output params to the caller's
-- out-argument (minting a fresh returned cell when absent), globals/consts to
-- their sinks, and phantoms by reading the corresponding field of their base in
-- the caller (materializing caller phantoms only when the base is external).
-- Then replay the summary: containment edges become 'writeField's (embedding); a
-- pass-through output's 'FieldIdent' edge is consumed during σ resolution, binding
-- the caller out-arg variable to its source nodes (identity, not a fresh cell);
-- and escape classes are raised on the caller nodes.  Because σ(input param) is
-- the caller arg's own nodes, two actual arguments that already alias share σ
-- automatically, so the soundness-critical alias merge (TODO 5) falls out for
-- free.
instantiateSummary :: PrimProto -> [PrimArg] -> ProcPTGSummary
        -> PointsToGraph -> Compiler PointsToGraph
instantiateSummary calleeProto args summary ptg0 = do
    -- Every external node mentioned in the summary needs a σ image.  A
    -- pass-through output and its sources are 'FieldIdent' edge endpoints, so they
    -- are already covered by the edge keys/targets below.
    let extNodes = Set.toList $ Set.unions
            [ Map.keysSet (psEdges summary)
            , Set.unions [ Set.unions (Map.elems fm)
                         | fm <- Map.elems (psEdges summary) ]
            , Map.keysSet (psEscape summary) ]
    -- Resolve σ for every needed ext node, threading the graph (minting /
    -- materializing may extend it) and memoizing.
    (sigma, ptg1) <- foldM
        (\(memo, g) e -> do
            (_, memo', g') <- resolveExt e (memo, g)
            return (memo', g'))
        (Map.empty, ptg0) extNodes
    let lookupSig e = Map.findWithDefault Set.empty e sigma
    -- (1) Replay field edges: for base.f -> tgt, embed σ(tgt) in σ(base).f.  A
    -- 'FieldIdent' edge is identity, not containment: it is consumed during σ
    -- resolution (see 'resolveExt' for 'ExtReturn', which binds the out-arg var to
    -- the source nodes), so it is skipped here rather than written as a field.
    let ptg2 = List.foldl'
            (\g (base, fm) ->
                let bases = lookupSig base
                in List.foldl'
                    (\g' (f, tgts) ->
                        if f == FieldIdent then g' else
                        let tgtNs = Set.unions (List.map lookupSig (Set.toList tgts))
                        in Set.foldr (\n -> writeField n f tgtNs) g' bases)
                    g (Map.toList fm))
            ptg1 (Map.toList (psEdges summary))
    -- Pass-through binding of the actual out-arg variables is done during σ
    -- resolution (see 'resolveExt' for 'ExtReturn'): a pass-through output shares
    -- its canonical source's caller nodes, so the out-arg variable is bound there
    -- and no separate alias-replay pass is needed.
    --
    -- (2) Raise escape classes on the caller nodes (and everything reachable).
    let ptg3 = Map.foldrWithKey
            (\e st g -> if st >= ArgEscape
                            then raiseEscapeReachable st (lookupSig e) g
                            else g)
            ptg2 (psEscape summary)
    return ptg3
  where
    argAt i = if i >= 0 && i < List.length args then Just (args !! i) else Nothing
    isExtReturn ExtReturn{} = True
    isExtReturn _           = False
    notExtReturn = not . isExtReturn
    -- The identity ('FieldIdent') sources of an ext node: the nodes it IS (shares
    -- memory with), as recorded in 'psEdges'.  Empty for a fresh/non-aliased node.
    identSourcesOf e = Map.findWithDefault Set.empty FieldIdent
                           (Map.findWithDefault Map.empty e (psEdges summary))

    -- Resolve one 'ExtNode' to the set of caller nodes it stands for, threading
    -- the (possibly extended) graph and a memo.
    resolveExt :: ExtNode -> (Map ExtNode (Set Node), PointsToGraph)
            -> Compiler (Set Node, Map ExtNode (Set Node), PointsToGraph)
    resolveExt ext (memo, g) =
        case Map.lookup ext memo of
            Just ns -> return (ns, memo, g)
            Nothing -> do
                (ns, memo', g') <- compute ext memo g
                return (ns, Map.insert ext ns memo', g')

    compute ext memo g = case ext of
        ExtParam i  -> resolveArg (argAt i) memo g
        ExtReturn i ->
            -- A pass-through return SHARES its sources' nodes (the input(s) it
            -- returns, or a sibling output -- carried by the output's 'FieldIdent'
            -- edge) rather than minting a fresh cell: the callee threaded the same
            -- structure through (an in-place update), so the returned var must have
            -- the sources' identity, not a spurious fresh local that would leak
            -- into their field edges and defeat the unaliased query (the nbody
            -- regression).  Only a genuinely fresh return (no 'FieldIdent' edge, or
            -- one whose sources are nodeless) mints.
            case identSourcesOf (ExtReturn i) of
                srcs | Set.null srcs -> resolveOut (argAt i) memo g
                srcs -> do
                    -- Non-return sources are concrete (input args / const / global
                    -- sinks); resolve and union them.  Resolving sibling *returns*
                    -- would only chase back to these same sources (or cycle), so a
                    -- pure sibling-return merge is handled by the min-return mint.
                    let nonRet = [ s | s <- Set.toList srcs, notExtReturn s ]
                    (inNs, memoA, gA) <- foldM
                        (\(acc, m, gg) s -> do
                            (ns, m', gg') <- resolveExt s (m, gg)
                            return (Set.union acc ns, m', gg'))
                        (Set.empty, memo, g) nonRet
                    (ns, memoB, gB) <-
                        if not (Set.null inNs)
                            then return (inNs, memoA, gA)
                            else
                                -- Pure sibling-return merge (or nodeless inputs):
                                -- the lowest-indexed return of the class mints the
                                -- single shared cell; the rest resolve to it.
                                let comp   = Set.insert (ExtReturn i) srcs
                                    minRet = Set.findMin
                                                 (Set.filter isExtReturn comp)
                                in if minRet == ExtReturn i
                                    then resolveOut (argAt i) memoA gA
                                    else resolveExt minRet (memoA, gA)
                    let gC = case argAt i >>= argVarNameMaybe of
                                Just v  -> addVarNodes v ns gB
                                Nothing -> gB
                    return (ns, memoB, gC)
        ExtGlobal gl -> return (Set.singleton (Node (GlobalNode gl)), memo, g)
        ExtConst s   -> return (Set.singleton (Node (ConstNode s)), memo, g)
        ExtPhantom base f -> do
            (baseNs, memo', g') <- resolveExt base (memo, g)
            let (collected, g'') = Set.foldr
                    (\n (acc, gg) -> let (rs, gg') = readFieldMat n f gg
                                     in (Set.union acc rs, gg'))
                    (Set.empty, g') baseNs
            return (collected, memo', g'')

    -- An input param resolves to the actual argument's VARIABLE nodes only.
    -- Const/global args are dropped at the boundary (mirroring the old var-only
    -- @_zipParamToArgVar@): propagating a shared constant into the caller would
    -- spuriously tie a returned value to a dead constant and block its reuse
    -- (the nbody regression).  A nodeless pointer *variable* is minted a fresh
    -- node (keyed by the var, stable across fixpoint iterations) so it still
    -- shares identity with the other members of its summary class -- the
    -- union-find variable-identity that protects a freshly-returned value from
    -- an unsound destructive reuse (the string corruption case).
    resolveArg (Just arg) memo gg = do
        ptr <- argIsPointer arg
        case (ptr, argVarNameMaybe arg) of
            (True, Just v) ->
                let ns = varNodes gg v
                in if Set.null ns
                    then let (n, gg') = freshLocalNode v gg
                         in return (Set.singleton n, memo, gg')
                    else return (ns, memo, gg)
            _ -> return (Set.empty, memo, gg)
    resolveArg Nothing memo gg = return (Set.empty, memo, gg)
    -- A genuinely fresh returned structure: whatever the caller's out-arg
    -- variable already points to, or a fresh cell bound to it when absent.
    resolveOut (Just ArgVar{argVarName=v}) memo gg =
        let existing = varNodes gg v
        in if Set.null existing
            then let (n, gg') = freshLocalNode v gg
                 in return (Set.singleton n, memo, gg')
            else return (existing, memo, gg)
    resolveOut _ memo gg = return (Set.empty, memo, gg)


-- | Field read: @pts(member) ⊇ ⋃_{n ∈ pts(struct)} readFieldMat(n, key)@.
-- Skipped when the member is not a pointer.  'readFieldMat' materializes a
-- phantom (external base) or falls back to the base node (local base with an
-- unknown field), keeping an embedded/interior read conservatively aliased.
transferAccess :: PointsToGraph -> PrimArg -> PrimArg -> PrimArg
        -> Compiler PointsToGraph
transferAccess ptg struct offset member = case member of
    ArgVar{argVarName=mv} -> do
        ptrMember <- argIsPointer member
        if not ptrMember
            then return ptg
            else do
                let key = keyOfOffset (fromIntegral <$> argIntVal offset)
                let structNodes = rawSourceNodes ptg struct
                let (collected, ptg') = Set.foldr
                        (\n (acc, g) -> let (ns, g') = readFieldMat n key g
                                        in (Set.union acc ns, g'))
                        (Set.empty, ptg) structNodes
                return $ addVarNodes mv collected ptg'
    _ -> return ptg


-- | Field write.  (1) Struct edge: @pts(fOut) ⊇ pts(fIn)@, honouring `noalias`
-- (a genuinely fresh copy) by giving fOut a fresh local node instead.  (2) Field
-- store: for every node of the struct being written, @writeField(n, key) ⊇
-- pts(member)@ (skipped when member is not a pointer).
transferMutate :: PointsToGraph -> [Ident] -> [PrimArg] -> Compiler PointsToGraph
transferMutate ptg flags [fIn, fOut, offset, _, _, _, member] = do
    let noalias = "noalias" `elem` flags
    let key     = keyOfOffset (fromIntegral <$> argIntVal offset)
    let fInNodes = rawSourceNodes ptg fIn
    let (ptg1, storeInto) = case fOut of
            ArgVar{argVarName=fo}
                | noalias   -> let (n, g) = freshLocalNode fo ptg
                               in (g, Set.singleton n)
                | otherwise -> let g = addVarNodes fo fInNodes ptg
                               in (g, Set.union fInNodes (varNodes g fo))
            _ -> (ptg, fInNodes)
    ptrMember <- argIsPointer member
    let memberNodes = if ptrMember then rawSourceNodes ptg1 member else Set.empty
    return $ Set.foldr (\n g -> writeField n key memberNodes g) ptg1 storeInto
transferMutate ptg _ _ = return ptg


-- | Value-preserving copy: @pts(out) ⊇ pts(in)@.  When @gated@ is set (an
-- `llvm move`), the copy only carries points-to information if the source is
-- pointer-represented: copying a non-pointer scalar (e.g. an int) must not
-- create an alias between two values that merely share a numeric value, matching
-- the old analysis's `aliasedRep` filter.  When @gated@ is unset (an `lpvm
-- cast`), the copy is ungated because a cast may move an address through an
-- int-typed intermediate and must still carry the points-to set (TODO 12).
transferCopy :: Bool -> PointsToGraph -> PrimArg -> PrimArg
        -> Compiler PointsToGraph
transferCopy gated ptg inp outp = do
    carry <- if gated then argIsPointer inp else return True
    return $ case outp of
        ArgVar{argVarName=out} | carry ->
            addVarNodes out (rawSourceNodes ptg inp) ptg
        _ -> ptg


-- | Global store: @writeField(GlobalNode, FieldAny) ⊇ pts(val)@ and taint the
-- stored value (and everything reachable) as escaping.  The edge from the
-- (external) global node is what makes the stored value read as aliased.
transferStore :: PointsToGraph -> PrimArg -> GlobalInfo -> Compiler PointsToGraph
transferStore ptg val glob = do
    ptrVal <- argIsPointer val
    let valNodes = if ptrVal then rawSourceNodes ptg val else Set.empty
    let gNode    = Node (GlobalNode glob)
    return $ raiseEscapeReachable GlobalEscape valNodes
                (writeField gNode FieldAny valNodes ptg)


-- | Interior-pointer / tag ops: every output points into whatever the pointer
-- inputs point to (@pts(out) ⊇ ⋃ pts(pointer inputs)@).
transferInterior :: PointsToGraph -> [PrimArg] -> Compiler PointsToGraph
transferInterior ptg args = do
    let ins  = [ a | a <- args, argFlowDirection a /= FlowOut ]
    let outs = [ v | a@ArgVar{argVarName=v} <- args, argFlowDirection a == FlowOut ]
    inNodeSets <- mapM (\a -> do ptr <- argIsPointer a
                                 return $ if ptr then rawSourceNodes ptg a
                                                 else Set.empty) ins
    let inNodes = Set.unions inNodeSets
    return $ List.foldl' (\g v -> addVarNodes v inNodes g) ptg outs


-- | Nodes contributed by a source argument (pointer variables, global sinks,
-- and constant memory blocks).  Constant refs introduce a 'ConstNode' (TODO 3).
rawSourceNodes :: PointsToGraph -> PrimArg -> Set Node
rawSourceNodes ptg arg = case arg of
    ArgVar{argVarName=v} -> varNodes ptg v
    ArgGlobal glob _     -> Set.singleton (Node (GlobalNode glob))
    ArgConstRef ref _    -> Set.singleton (Node (ConstNode ref))
    _                    -> Set.empty


-- | Is this argument's type represented as an address (pointer-like)?
argIsPointer :: PrimArg -> Compiler Bool
argIsPointer arg = do
    rep <- lookupTypeRepresentation (argType arg)
    return $ maybe False aliasedRep rep
  where
    aliasedRep CPointer = True
    aliasedRep Pointer  = True
    aliasedRep Func{}   = True
    aliasedRep _        = False


-- | Drop dead (final) argument variables from the environment.  Their nodes and
-- edges are retained (they are the persistent aliasing substrate); only the
-- var->node bindings go, so a dead var stops being an aliasing root.
dropFinalArgs :: PointsToGraph -> [PrimArg] -> PointsToGraph
dropFinalArgs ptg args =
    dropVars (Set.fromList
        [ v | ArgVar{argVarName=v, argVarFinal=True} <- args ]) ptg


----------------------------------------------------------------
--                 Global Level Aliasing Analysis
----------------------------------------------------------------
-- The local one above considers all parameters as aliased, and this global
-- one is to extend that by generating specialized procedures where
-- some parameters aren't aliased.
-- The code here is to analysis each procedure and list parameters
-- that are interesting for further use (in "Transform.hs").
-- We consider a parameter is interesting when the alias
-- information of that parameter can help us generate a
-- better version of that procedure.
-- More detail about Multiple Specialization can be found in "Transform.hs"


-- we say a real param is interesting if it can be updated
-- destructively when it doesn't alias to anything from outside
updateMultiSpeczInfoByPrim :: PrimProto
        -> (AliasMapLocal, Set InterestingCallProperty, MultiSpeczDepInfo)
        -> Placed Prim
        -> Compiler (Set InterestingCallProperty, MultiSpeczDepInfo)
updateMultiSpeczInfoByPrim proto
        (aliasMap, interestingCallProperties, multiSpeczDepInfo) prim =
    case content prim of
        PrimCall callSiteID spec _ args  _ -> do
            calleeDef <- getProcDef spec
            let ProcDefPrim _ calleeProto _ analysis _ = procImpln calleeDef
            let interestingPrimCallInfo = List.zip args [0..]
                    |> List.filter (\(arg, paramID) ->
                        -- we only care parameters that are interesting,
                        -- args that aren't struct(address) are removed.
                        Set.member (InterestingUnaliased paramID)
                                (procInterestingCallProperties analysis)
                        -- if a argument is used more than once,
                        -- then it should be aliased
                        && isArgVarUsedOnceInArgs arg args calleeProto)
                    |> Maybe.mapMaybe (\(arg, paramID) ->
                        fmap (\requiredParams -> (arg, paramID, requiredParams))
                            (isArgUnaliased aliasMap arg))
            logAlias $ "interestingPrimCallInfo: "
                    ++ show interestingPrimCallInfo
            -- update interesting params
            let newInterestingParams =
                    List.concatMap (\(_, _, x) -> x) interestingPrimCallInfo
            unless (List.null newInterestingParams)
                        $ logAlias $ "Found interesting params: "
                        ++ show newInterestingParams
            let interestingCallProperties' =
                    addInterestingUnaliasedParams proto
                        interestingCallProperties newInterestingParams
            -- update dependencies
            let infoItems = List.map (\(_, calleeParamID, requiredParams) ->
                    let requiredParamIDs =
                            List.map (parameterVarNameToID proto) requiredParams
                    in
                    NonAliasedParamCond calleeParamID requiredParamIDs
                    ) interestingPrimCallInfo
            multiSpeczDepInfo' <- updateMultiSpeczDepInfo multiSpeczDepInfo
                    callSiteID spec infoItems
            return (interestingCallProperties', multiSpeczDepInfo')
        PrimForeign "lpvm" "mutate" flags args ->
            case args of
                [fIn, _, _, ArgInt des _, _, _, _] ->
                    -- Skip "mutate" that is set to be destructive by
                    -- previous optimizer
                    if des /= 1
                    then
                        -- mutate only happens on struct(address)
                        case isArgUnaliased aliasMap fIn of
                        Just requiredParams -> do
                            logAlias $ "Found interesting params: "
                                    ++ show requiredParams
                            let interestingCallProperties' =
                                    addInterestingUnaliasedParams proto
                                        interestingCallProperties requiredParams
                            return
                                (interestingCallProperties', multiSpeczDepInfo)
                        Nothing ->
                            return
                                (interestingCallProperties, multiSpeczDepInfo)
                    else return (interestingCallProperties, multiSpeczDepInfo)
                _ ->
                    shouldnt "unable to match args of lpvm mutate instruction"
        _ -> return (interestingCallProperties, multiSpeczDepInfo)


-- It returns "Just requiredParams" if the given "PrimArg" isn't aliased and
-- isn't used after this point.
-- "requiredParams" is a list of params that needs to be non-aliased to make
-- the given "PrimArg" actually interesting (Caused by "MaybeAliasByParam").
-- A special case is that it returns "Just []" for "ArgInt", because "ArgInt"
-- can be used for struct tags.
-- It returns "Nothing" in other cases.
isArgUnaliased :: AliasMapLocal -> PrimArg -> Maybe [PrimVarName]
isArgUnaliased aliasMap ArgVar{argVarName=varName, argVarFinal=final}
    | final     = queryUnaliased aliasMap varName
    | otherwise = Nothing
isArgUnaliased _ (ArgInt _ _) = Just []
isArgUnaliased _ _ = Nothing


-- | Check if the argument escapes the current procedure via alias analysis.
-- Returns True if it's aliased to something outside the local scope (a global
-- or a parameter).  This is one of two escape checks used at alloc sites; the
-- other is the mutation-chain reachability set in Transform.hs
-- (computeEscapedVars).  An alloc must be heap-allocated if either check fires.
isArgEscaped :: AliasMapLocal -> PrimArg -> Bool
isArgEscaped aliasMap ArgVar{argVarName=varName} = queryEscaped aliasMap varName
isArgEscaped _ _ = True  -- constants/globals are conservatively considered escaped


-- return True if the given arg is only used once in given list of arg.
-- Unneeded params are ignored.
-- no need to worry about output var since it's in SSA form.
isArgVarUsedOnceInArgs :: PrimArg -> [PrimArg] -> PrimProto -> Bool
isArgVarUsedOnceInArgs ArgVar{argVarName=varName} args calleeProto =
    List.zip args (primProtoParams calleeProto)
    |> List.filter (\case
            (ArgVar{argVarName=varName'}, param)
                -> varName == varName' && paramIsNeeded param
            _
                -> False)
    |> List.length |> (== 1)
isArgVarUsedOnceInArgs _ _ _ = True -- we don't care about constant value


-- adding interesting unaliased params
addInterestingUnaliasedParams :: PrimProto -> Set InterestingCallProperty
        -> [PrimVarName] -> Set InterestingCallProperty
addInterestingUnaliasedParams proto properties params =
    List.map (InterestingUnaliased . (parameterVarNameToID proto)) params
    |> (List.foldr Set.insert) properties


-- adding new specz version dependency
updateMultiSpeczDepInfo :: MultiSpeczDepInfo -> CallSiteID -> ProcSpec
        -> [CallSiteProperty] -> Compiler MultiSpeczDepInfo
updateMultiSpeczDepInfo multiSpeczDepInfo callSiteID pSpec items =
    if List.null items
    then
        return multiSpeczDepInfo
    else do
        logAlias $ "Update MultiSpeczDepInfo, CallSiteID: " ++ show callSiteID
                ++ " ProcSpec: " ++ show pSpec ++ " items:" ++ show items
        return $ Map.alter (\x ->
            fromMaybe (pSpec, Set.empty) x
            |> second (Set.union (Set.fromList items))
            |> Just) callSiteID multiSpeczDepInfo


----------------------------------------------------------------
--                 Dead Memory Cell Analysis
----------------------------------------------------------------
-- This analyser finds dead memory cells so we can reuse them to
-- avoid some alloc instructions.
-- The currently alias map is undirectional, so we have to identify
-- dead cells using access instruction.
-- if there is an access instruction that reads some value from x,
-- then we consider x is dead if x is unaliased and final.
--
-- The transform part can be found in "Transform.hs".

-- XXX currently it relies on the size arg of the access instruction. Another
--       way (much more flexible) to do it is introducing some lpvm instructions
--       that do nothing and only provide information for the compiler.
-- TODO call "GC_free" on large unused dead cells.
--       (according to https://github.com/ivmai/bdwgc, > 8 bytes)
-- TODO we'd like this analysis to detect structures that are dead aside from
--       later access instructions, which could be moved earlier to allow the
--       structure to be reused.
-- TODO consider re-run the optimiser after this or even run this before the
--       optimiser.


-- Update dead cells info based on the given prim. If a dead cell comes from a
-- parameter, then we mark that parameter as interesting.
updateDeadCellsByPrim :: PrimProto
        -> (AliasMapLocal, Set InterestingCallProperty, DeadCells)
        -> Placed Prim -> Compiler (Set InterestingCallProperty, DeadCells)
updateDeadCellsByPrim proto (aliasMap, interestingCallProperties, deadCells)
        prim =
    case content prim of
        PrimForeign "lpvm" "access" _ args -> do
            deadCells'
                <- updateDeadCellsByAccessArgs (aliasMap, deadCells) args
            return (interestingCallProperties, deadCells')
        PrimForeign "lpvm" "alloc" _ args  -> do
            let (result, deadCells') = assignDeadCellsByAllocArgs deadCells args
            interestingCallProperties' <- case result of
                    Nothing -> return interestingCallProperties
                    Just (selectedCell, requiredParams) ->
                        if requiredParams /= []
                        then do
                            logAlias $ "Found interesting parameters in dead "
                                    ++ "cell analysis. " ++ show requiredParams
                            return $ addInterestingUnaliasedParams proto
                                        interestingCallProperties requiredParams
                        else return interestingCallProperties
            return (interestingCallProperties', deadCells')
        _ ->
            return (interestingCallProperties, deadCells)


-- Find new dead cell from the given "primArgs" of "access" instruction.
updateDeadCellsByAccessArgs :: (AliasMapLocal, DeadCells) -> [PrimArg]
        -> Compiler DeadCells
updateDeadCellsByAccessArgs (aliasMap, deadCells) primArgs = do
    case primArgs of
        -- [struct:type, offset:int, size:int, startOffset:int, ?member:type2]
        [struct@ArgVar{argVarName=varName}, _, ArgInt size _, startOffset, _] ->
            let size' = fromInteger size in
            case isArgUnaliased aliasMap struct of
                Just requiredParams -> do
                    logAlias $ "Found new dead cell: " ++ show varName
                            ++ " size:" ++ show size' ++ " requiredParams:"
                            ++ show requiredParams
                    let newCell = ((struct, startOffset), requiredParams)
                    return $ Map.alter (\x ->
                        (case x of
                            Nothing -> [newCell]
                            Just cells -> newCell:cells) |> Just)
                                    size' deadCells
                Nothing ->
                    return deadCells
        _ -> return deadCells


-- Try to assign a dead cell to reuse for the given "alloc" instruction.
-- It returns "(result, deadCells)". "result" is "Nothing" when there isn't a
-- suitable dead cell to reuse. Otherwise, result is
-- "Just ((selectedCell, startOffset), requiredParams)". "requiredParams"
-- contains parameters that need to be non-aliased before reusing the
-- "selectedCell" (Caused by "MaybeAliasByParam"). Note that this always tries
-- to assigned a cell with empty "requiredParams" first.
assignDeadCellsByAllocArgs :: DeadCells -> [PrimArg]
        -> (Maybe ((PrimArg, PrimArg), [PrimVarName]), DeadCells)
assignDeadCellsByAllocArgs deadCells primArgs =
    case primArgs of
        -- [size:int, ?struct:type]
        [ArgInt size _, struct] ->
            let size' = fromInteger size in
            case Map.lookup size' deadCells of
                Just cells ->
                    let assigned =
                            -- try to select one without "requiredParams".
                            case List.find (List.null . snd) cells of
                                Just x  -> Just x
                                Nothing -> case cells of
                                    []    -> Nothing
                                    (x:_) -> Just x
                    in
                    case assigned of
                        Nothing -> (Nothing, deadCells)
                        Just x  ->
                            -- XXX we need something better than this. In order to
                            -- have better optimization, we combine "requiredParams"
                            -- from all possible cells. However, it may create some
                            -- specialized versions that are identical.
                            let requiredParams =
                                    if List.null $ snd x
                                    then []
                                    else
                                        List.concatMap snd cells
                                        |> Set.fromList |> Set.toList
                            in
                            let cells' = List.delete x cells in
                            let deadCells' = Map.insert size' cells' deadCells in
                            (Just (fst x, requiredParams), deadCells')
                Nothing    -> (Nothing, deadCells)
        _ -> (Nothing, deadCells)
