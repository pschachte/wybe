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


-- The intraprocedural working state is now a field- and direction-sensitive
-- "PointsToGraph" (see "PointsToGraph.hs"), replacing the old Steensgaard-style
-- union-find ("DisjointSet AliasMapLocalItem").  At proc exit it is projected
-- back to the serialized "AliasMap" (defined in "AST.hs"), a "DisjointSet
-- PrimVarName" recording which formal parameters may alias each other -- the
-- callee-summary interface is unchanged, so callers are unaffected.  See
-- "points_to_graph.md" (Phase A).
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
        -> Compiler [(AliasMap, Set InterestingCallProperty)]
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


-- extract "AliasMap" and "Set InterestingCallProperty" from
-- the given "ProcAnalysis"
extractAliasInfoFromAnalysis :: ProcAnalysis
        -> (AliasMap, Set InterestingCallProperty)
extractAliasInfoFromAnalysis analysis =
    (procArgAliasMap analysis, procInterestingCallProperties analysis)

-- This comparison is CRUCIAL. The underlying data struct should
-- handle equal CORRECTLY.
isAliasInfoChanged :: (AliasMap, Set InterestingCallProperty)
                    -> (AliasMap, Set InterestingCallProperty) -> Bool
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

        aliasMap' <- completeAliasMap caller aliasMap
        -- Update proc analysis with new aliasPairs
        let newAnalysis =
                oldAnalysis {
                    procArgAliasMap = aliasMap',
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


completeAliasMap :: PrimProto -> AliasMapLocal -> Compiler AliasMap
completeAliasMap caller aliasMap = do
    -- Project the final graph onto parameter aliasing: pairs of maybe-aliased
    -- params whose reachable node sets intersect (see 'paramAliasPairs').  Fold
    -- the pairs into a DisjointSet and drop singletons, reproducing the old
    -- union-find summary shape ("DisjointSet PrimVarName" of aliased params).
    let pairs = paramAliasPairs aliasMap
    let aliasMap' = Set.foldr (\(p, q) -> unionTwoInDS p q) emptyDS pairs
                        |> removeSingletonFromDS
    logAlias $ "^^^  param alias pairs: " ++ show pairs
    logAlias $ "^^^  alias of formal params: " ++ show aliasMap'
    return aliasMap'


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
        transferCopy ptg inp outp
    PrimForeign "llvm" "move" _ [inp, outp] ->
        transferCopy ptg inp outp
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


-- | Wybe call: instantiate the callee's stored summary (still the coarse
-- name-based 'AliasMap') onto the caller's graph.  For every pair of callee
-- parameters that may alias, alias the corresponding actual arguments so they
-- share memory (§5.2.4 alias merge, field-insensitive as the coarse summary
-- requires).  Crucially this must handle *non-variable* args (constant refs and
-- globals): if a returned/output arg aliases a constant argument (e.g. a slice
-- result embedding a constant range), the var arg must learn it references that
-- constant -- otherwise a later destructive spec could clobber the shared
-- constant (silent corruption).
transferCall :: PointsToGraph -> ProcSpec -> [PrimArg] -> Compiler PointsToGraph
transferCall ptg spec args = do
    calleeDef <- getProcDef spec
    let ProcDefPrim _ calleeProto _ analysis _ = procImpln calleeDef
    let calleeSummary = procArgAliasMap analysis
    -- map each callee param name to the caller arg's (source nodes, maybe var).
    -- Gate on pointer-ness: a non-pointer arg (e.g. a constant int/float, or a
    -- non-address global) carries no aliasing, matching the old analysis's
    -- aliasedRep filter.  Without this, a non-pointer constant/global argument
    -- would spuriously alias the output and block destructive reuse.
    paramInfo <- Map.fromList <$> mapM
            (\(pn, arg) -> do
                ptr <- argIsPointer arg
                let ns = if ptr then rawSourceNodes ptg arg else Set.empty
                return (pn, (ns, argVarNameMaybe arg)))
            (List.zip (primProtoParamNames calleeProto) args)
    let pairs = Set.toList (dsToTransitivePairs calleeSummary)
    return $ List.foldl' (\g (p, q) ->
        case (Map.lookup p paramInfo, Map.lookup q paramInfo) of
            (Just (na, va), Just (nb, vb)) ->
                let both = Set.union na nb
                    bind v = maybe id (`addVarNodes` both) v
                in bind va (bind vb g)
            _ -> g) ptg pairs


-- | The variable name of an 'ArgVar', if the arg is one.
argVarNameMaybe :: PrimArg -> Maybe PrimVarName
argVarNameMaybe ArgVar{argVarName=v} = Just v
argVarNameMaybe _                    = Nothing


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


-- | Value-preserving copy (`lpvm cast` / `llvm move`): @pts(out) ⊇ pts(in)@.
-- Ungated by representation: a cast may move an address through an int-typed
-- intermediate and must still carry the points-to set (TODO 12).
transferCopy :: PointsToGraph -> PrimArg -> PrimArg -> Compiler PointsToGraph
transferCopy ptg inp outp = return $ case outp of
    ArgVar{argVarName=out} -> addVarNodes out (rawSourceNodes ptg inp) ptg
    _                      -> ptg


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


-- Helper: map arguments in callee proc to its formal parameters so we can get
-- alias info of the arguments
mapParamToArg :: PrimProto -> [PrimArg] -> Map PrimVarName PrimArg
mapParamToArg proto args =
    let formalParamNames = primProtoParamNames proto
        paramArgPairs = _zipParamToArg formalParamNames args
    in Map.fromList paramArgPairs


-- Helper: zip formal param to PrimArg with PrimArg that could be aliased
_zipParamToArg :: [PrimVarName] -> [PrimArg] -> [(PrimVarName, PrimArg)]
_zipParamToArg (p:params) (c@ArgConstRef{}:args) =
    (p, c):_zipParamToArg params args
_zipParamToArg (p:params) (g@ArgGlobal{}:args) =
    (p, g):_zipParamToArg params args
_zipParamToArg (p:params) (v@ArgVar{argVarName=nm}:args) =
    (p, v):_zipParamToArg params args
_zipParamToArg (_:params) (_:args) = _zipParamToArg params args
_zipParamToArg [] _ = []
_zipParamToArg _ [] = []


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
