--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 19:02:05 EST 2014
--  Purpose  : Framework to optimise a single module
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.

module Optimise (optimiseMod) where

import           AST
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.Graph
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Set                  as Set
import           Expansion
import           Options                   (LogSelection (Optimise))
import           Types

optimiseMod :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
optimiseMod mods thisMod = do
    reenterModule thisMod
    -- checkFullyTyped -- Sanity check: be sure everything is fully typed
    procs <- getModuleImplementationField (Map.toList . modProcs)
    let ordered =
            stronglyConnComp
            [(pspec,pspec,
              nub $ concatMap (localBodyCallees thisMod . procBody) procDefs)
             | (name,procDefs) <- procs,
               (n,def) <- zip [0..] procDefs,
               let pspec = ProcSpec thisMod name n
             ]
    logOptimise $ "Optimise SCCs:\n" ++
        unlines (List.map (show . sccElts) ordered)
    -- XXX this is wrong:  it does not do a proper top-down
    -- traversal, as it is not guaranteed to vist all callers before
    -- visiting the called proc.  Need to construct inverse graph instead.
    mapM_ (mapM_ optimiseProcTopDown .  sccElts) $ reverse ordered

    mapM_ optimiseSccBottomUp ordered

    mapM_ aliasSccBottomUp ordered

    finishModule
    return (False,[])


-- | Do bottom-up optimisation on one SCC.  If optimising any but the first
--   in the SCC determines it should be inlined, we may have already missed
--   inlining a call to it, so go through the whole SCC and optimise it
--   again.
--
--   XXX  This is a bit heavy-handed, but it will only do extra work for
--   mutually recursive procs, and it's simpler than keeping track of all
--   proc calls we've seen and not inlined so we avoid repeating work when
--   it won't do anything.  It's also possible that this may need to be
--   repeated to a fixed point, but I'm not confident that optimisation
--   is monotone and I don't want an infinite loop.
optimiseSccBottomUp procs = do
    inlines <- mapM optimiseProcBottomUp $ sccElts procs
    when (or $ tail inlines) $ do
        mapM_ optimiseProcBottomUp $ sccElts procs
        return ()


procBody :: ProcDef -> ProcBody
procBody def =
    case procImpln def of
        ProcDefSrc _       -> shouldnt "Optimising un-compiled code"
        ProcDefPrim _ body _ -> body


sccElts (AcyclicSCC single) = [single]
sccElts (CyclicSCC multi)   = multi


optimiseProcTopDown :: ProcSpec -> Compiler ()
optimiseProcTopDown pspec = do
    logOptimise $ ">>> Optimise (Top-down) " ++ show pspec
    updateProcDefM (optimiseProcDefTD pspec) pspec
    return ()


optimiseProcDefTD :: ProcSpec -> ProcDef -> Compiler ProcDef
optimiseProcDefTD pspec def = do
    return def


-- | Do bottom-up optimisations of a Proc, returning whether to inline it
optimiseProcBottomUp :: ProcSpec -> Compiler Bool
optimiseProcBottomUp pspec = do
    logOptimise $ "\n>>> Optimise (Bottom-up) " ++ show pspec
    updateProcDefM (optimiseProcDefBU pspec) pspec
    newDef <- getProcDef pspec
    return $ procInline newDef


optimiseProcDefBU :: ProcSpec -> ProcDef -> Compiler ProcDef
optimiseProcDefBU pspec def = do
    logOptimise $ "*** " ++ show pspec ++
      " before optimisation:" ++ showProcDef 4 def
    def' <- procExpansion pspec def >>= decideInlining >>= updateFreshness
    logOptimise $ "*** " ++ show pspec ++
      " after optimisation:" ++ showProcDef 4 def' ++ "\n"
    return def'


----------------------------------------------------------------
--                       Deciding what to inline
----------------------------------------------------------------

-- |Decide whether to inline the proc and mark it if so.  If it's already
--  marked to be inlined, don't second guess that.
decideInlining :: ProcDef -> Compiler ProcDef
decideInlining def
    |  NoFork == bodyFork body && not (procInline def) = do
    logOptimise $ "Considering inline of " ++ procName def
    let benefit = 4 + procCost proto -- add 4 for time saving
    logOptimise $ "  benefit = " ++ show benefit
    let cost = bodyCost $ bodyPrims body
    logOptimise $ "  cost = " ++ show cost
    -- Inline procs where benefit >= cost and private procs with only one use
    if benefit >= cost
       || procCallCount def <= 1 && procVis def == Private
    then return $ def { procInline = True }
    else return def
    where ProcDefPrim proto body _ = procImpln def
decideInlining def = return def


procCost :: PrimProto -> Int
procCost proto =
    1 + (length $ List.filter (not . phantomParam) $ primProtoParams proto)

bodyCost :: [Placed Prim] -> Int
bodyCost pprims = sum $ List.map (primCost . content) pprims

primCost :: Prim -> Int
primCost (PrimCall _ args)          = 1 + (sum $ List.map argCost args)
primCost (PrimForeign "llvm" _ _ _) = 1 -- single instuction, so cost = 1
primCost (PrimForeign "$" _ _ _)    = 1    -- single instuction, so cost = 1
primCost (PrimForeign _ _ _ args)   = 1 + (sum $ List.map argCost args)
primCost (PrimTest _)               = 0

argCost :: PrimArg -> Int
argCost arg = if phantomArg arg then 0 else 1

----------------------------------------------------------------
--                     Handling the call graph
----------------------------------------------------------------


-- |Finding all procs called by a given proc body
localBodyCallees :: ModSpec -> ProcBody -> [ProcSpec]
localBodyCallees modspec body =
    foldBodyDistrib (\_ prim callees -> localCallees modspec prim ++ callees)
    [] (++) (++) body


localCallees :: ModSpec -> Prim -> [ProcSpec]
localCallees modspec (PrimCall pspec _) = [pspec]
localCallees _ _                        = []


-- |Log a message, if we are logging optimisation activity.
logOptimise :: String -> Compiler ()
logOptimise s = logMsg Optimise s


----------------------------------------------------------------
--                     Freshness Analysis
----------------------------------------------------------------
-- Build a set of fresh vars and update destructive flag in lpvm mutate
-- instruction
updateFreshness :: ProcDef -> Compiler ProcDef
updateFreshness procDef = do
    let (ProcDefPrim proto body _) = procImpln procDef
    let prims = bodyPrims body
    let (freshset, prims') = List.foldl freshInPrim (Set.empty, []) prims
    logOptimise $ "\n*** Freshness analysis:" ++ show freshset ++ "\n"
    let body' = body { bodyPrims = prims' }
    return procDef { procImpln = ProcDefPrim proto body' (ProcAnalysis []) }


-- Update args in a signle (alloc/mutate) prim
freshInPrim :: (Set PrimVarName, [Placed Prim]) -> Placed Prim
                -> (Set PrimVarName, [Placed Prim])
freshInPrim (freshVars, prims)
    (Placed (PrimForeign lang "mutate" flags args) pos) =
        (freshVars', prims ++ [Placed (PrimForeign lang "mutate" flags args') pos])
            where (freshVars', args') = freshInMutate freshVars args
freshInPrim (freshVars, prims)
    (Unplaced (PrimForeign lang "mutate" flags args)) =
        (freshVars', prims ++ [Unplaced (PrimForeign lang "mutate" flags args')])
            where (freshVars', args') = freshInMutate freshVars args
freshInPrim (freshVars, prims) prim =
    case content prim of
        (PrimForeign _ "alloc" _ args) ->
            (freshVars', prims ++ [prim])
                where freshVars' = List.foldl freshInAlloc freshVars args
        _ ->
            (freshVars, prims ++ [prim])

-- newly allocated space is fresh
freshInAlloc :: Set PrimVarName -> PrimArg -> Set PrimVarName
freshInAlloc freshVars (ArgVar nm _ FlowOut _ _) = Set.insert nm freshVars
freshInAlloc freshVars _ = freshVars

-- variable after mutation is also fresh
freshInMutate :: Set PrimVarName -> [PrimArg] -> (Set PrimVarName, [PrimArg])
freshInMutate freshVars
    [fIn@(ArgVar inName _ _ _ final), fOut@(ArgVar outName _ _ _ _), size,
    offset, ArgInt des typ, mem] =
        let
            freshVars' = Set.insert outName freshVars
        in
            if Set.member inName freshVars' && final
            then (freshVars', [fIn, fOut, size, offset, ArgInt 1 typ, mem])
            else (freshVars', [fIn, fOut, size, offset, ArgInt 0 typ, mem])
freshInMutate freshVars args = (freshVars, args)


----------------------------------------------------------------
--                     Escape Analysis
----------------------------------------------------------------
aliasSccBottomUp :: SCC ProcSpec -> Compiler ()
aliasSccBottomUp procs = do
    -- First pass (only process alias pairs incurred by move and mutate)
    mapM_ aliasProcBottomUp $ sccElts procs
    -- Second pass (handle alias pairs incurred by proc calls within procs)
    -- mapM_ aliasProcBottomUp $ sccElts procs

aliasProcBottomUp :: ProcSpec -> Compiler ()
aliasProcBottomUp pspec = do
    logOptimise ">>> Alias analysis (Bottom-up):"
    updateProcDefM (checkEscape pspec) pspec
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

-- Helper: Cartesian product of escaped FlowIn vars to proc output
_cartProd :: [a] -> [a] -> [(a, a)]
_cartProd ins outs = [(i, o) | i <- ins, o <- outs]


-- Check any argument become stale after this proc call if this
-- proc is not inlined
checkEscape :: ProcSpec -> ProcDef -> Compiler ProcDef
checkEscape spec def
    | not (procInline def) = do
        let (ProcDefPrim entryProto body analysis) = procImpln def
        let prims = bodyPrims body
        -- First pass (only process alias pairs incurred by move and mutate)
        let aliasPairs = List.foldr
                            (\prim alias ->
                                let args = escapablePrimArgs $ content prim
                                in aliasPairsFromArgs entryProto args alias) [] prims
        let aliasPairs' = removeDupTuples aliasPairs

        -- Second pass (handle alias pairs incurred by proc calls within
        -- entryProto)
        (prims', aliasNames) <- foldM (\(ps, as) prim ->
                            escapeByProcCalls (ps, as) prim) ([], []) prims
        let aliasByProcCalls = _aliasNamesToPairs entryProto aliasNames
        let allPairs = aliasPairs' ++ aliasByProcCalls
        let allPairs' = removeDupTuples allPairs

        -- Update body prims with correct destructive flag
        let body' = body { bodyPrims = prims' }

        -- Update proc analysis with new aliasPairs
        let analysis' = analysis { procArgAliases = allPairs' }
        logOptimise $ show entryProto ++ ":\n" ++ show allPairs'

        return def { procImpln = ProcDefPrim entryProto body' analysis'}
checkEscape _ def = return def


-- For first pass:
-- Build up alias pairs triggerred by move and mutate instructions
escapablePrimArgs :: Prim -> [PrimArg]
escapablePrimArgs (PrimForeign _ "move" _ args) = args
escapablePrimArgs (PrimForeign _ "mutate" _ args) = args
escapablePrimArgs _ = []

-- Only append to list if the arg is passed in by the enclosing entry proc or is
-- the return arg of the proc
-- paramNames: a list of PrimVarName of arguments of the enclosing proc
-- args: the list of PrimArg, the arguments of the prim enclosed in entryProto
argsOfProcProto :: [PrimVarName] -> (PrimArg -> PrimVarName) -> [PrimArg]
                    -> [Int]
argsOfProcProto paramNames varNameGetter =
    List.foldl (\es arg ->
        if isProcProtoArg paramNames arg
            then
                let vnm = varNameGetter arg
                    vidx = List.elemIndex vnm paramNames
                in case vidx of
                    Just vidx -> vidx : es
                    Nothing -> es
            else es) []


-- Check Arg escape in one prim of prims of the a ProcBody
aliasPairsFromArgs :: PrimProto -> [PrimArg] -> [AliasPair] -> [AliasPair]
aliasPairsFromArgs _ [] aliasPairs = aliasPairs
aliasPairsFromArgs entryProto args aliasPairs =
    let inputArgs = List.filter ((FlowIn ==) . argFlowDirection) args
        outputArgs = List.filter ((FlowOut ==) . argFlowDirection) args
        paramNames = procProtoParamNames entryProto
        escapedInputs = argsOfProcProto paramNames inArgVar inputArgs
        escapedVia = argsOfProcProto paramNames outArgVar outputArgs
    in _cartProd escapedInputs escapedVia ++ aliasPairs


-- For second pass:
-- Build up alias pairs triggerred by proc calls
-- Also update destructive flag in mutate prims following proc calls
escapeByProcCalls :: ([Placed Prim], [(PrimVarName, PrimVarName)])
                    -> Placed Prim
                    -> Compiler ([Placed Prim], [(PrimVarName, PrimVarName)])
escapeByProcCalls (prims, aliasNames)
    (Placed (PrimForeign lang "mutate" flags args) pos) =
        return (prims ++ [Placed (PrimForeign lang "mutate" flags args') pos], aliasNames)
            where args' = _updateMutateForAlias aliasNames args
escapeByProcCalls (prims, aliasNames)
    (Unplaced (PrimForeign lang "mutate" flags args)) =
        return (prims ++ [Unplaced (PrimForeign lang "mutate" flags args')], aliasNames)
            where args' = _updateMutateForAlias aliasNames args
escapeByProcCalls (prims, aliasNames) prim =
    case content prim of
        PrimCall spec args -> do
            def <- getProcDef spec
            let (ProcDefPrim thisProto body analysis) = procImpln def
            let pairs = procArgAliases analysis
            logOptimise $ show thisProto
            logOptimise $ "PrimCall args: " ++ show args
            logOptimise $ "pairs: " ++ show pairs
            let aliasNames' = _aliasPairsToNames args pairs
            logOptimise $ "names: " ++ show aliasNames'
            return (prims ++ [prim], aliasNames ++ aliasNames')
        _ ->
            return (prims ++ [prim], aliasNames)

-- Helper: convert alias index pairs to var name pairs
_aliasPairsToNames :: [PrimArg] -> [AliasPair] -> [(PrimVarName, PrimVarName)]
_aliasPairsToNames primCallArgs =
    List.foldr (\(p1,p2) aliasNames ->
        let ArgVar n1 _ _ _ _ = primCallArgs !! p1
            ArgVar n2 _ _ _ _ = primCallArgs !! p2
        in (n1, n2) : aliasNames
        ) []

-- Helper: convert aliased var names pair to arg index pair
_aliasNamesToPairs :: PrimProto -> [(PrimVarName, PrimVarName)] -> [AliasPair]
_aliasNamesToPairs entryProto aliasNames =
    let paramNames = procProtoParamNames entryProto
    in List.foldr (\(n1, n2) pairs ->
        let idexes = (List.elemIndex n1 paramNames, List.elemIndex n2 paramNames)
            -- idx2 = (List.elemIndex n1 paramNames, List.elemIndex n2 paramNames)
        in case idexes of
            (Just idx1, Just idx2) -> (idx1, idx2):pairs
            _ -> pairs
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
