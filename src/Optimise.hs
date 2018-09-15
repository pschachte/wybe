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

    -- mapM_ (mapM_ aliasSccTopDown . sccElts) ordered

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
    logOptimise "\n\nvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"
    logOptimise $ ">>> Optimise (Bottom-up) " ++ show pspec
    updateProcDefM (optimiseProcDefBU pspec) pspec
    newDef <- getProcDef pspec
    return $ procInline newDef


optimiseProcDefBU :: ProcSpec -> ProcDef -> Compiler ProcDef
optimiseProcDefBU pspec def = do
    logOptimise $ "*** " ++ show pspec ++
      " before optimisation:" ++ showProcDef 4 def
    def' <- procExpansion pspec def >>= decideInlining >>= updateFreshness >>= checkEscape
    logOptimise $ "*** " ++ show pspec ++
      " after optimisation:" ++ showProcDef 4 def'
    logOptimise "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
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
    logOptimise "\n***********************"
    logOptimise "*** Freshness analysis:"
    logOptimise $ show freshset
    logOptimise "***********************\n\n"
    let body' = body { bodyPrims = prims' }
    return procDef { procImpln = ProcDefPrim proto body' (ProcAnalysis []) }


-- Update args in a signle (alloc/mutate) prim
freshInPrim :: (Set PrimVarName, [Placed Prim]) -> Placed Prim
                -> (Set PrimVarName, [Placed Prim])
freshInPrim (freshVars, prims) (Placed (PrimForeign lang "mutate" flags args) pos) =
    (freshVars', prims ++ [Placed (PrimForeign lang "mutate" flags args') pos])
        where (freshVars', args') = freshInMutate freshVars args
freshInPrim (freshVars, prims) (Unplaced (PrimForeign lang "mutate" flags args)) =
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

-- aliasSccTopDown :: ProcSpec -> Compiler ()
-- aliasSccTopDown pspec = do
--     logOptimise $ ">>> Alias analysis (Top-down) " ++ show pspec
--     pdef <- getProcDef pspec
--     checkEscape pdef
--     return ()

-- Help function to normalise alias pairs in order
normalise :: Ord a => (a,a) -> (a,a)
normalise t@(x,y)
    | y < x    = (y,x)
    | otherwise = t

-- Then remove duplicated alias pairs
removeDupTuples :: Ord a => [(a,a)] -> [(a,a)]
removeDupTuples =
    List.map List.head . List.group . List.sort . List.map normalise


-- Check any argument become stale after this proc call if this
-- proc is not inlined
checkEscape :: ProcDef -> Compiler ProcDef
checkEscape def
    | not (procInline def) = do
        logOptimise "\n....................."
        logOptimise "*** Escape analysis:"
        logOptimise $ "*** " ++ procName def
        let (ProcDefPrim entryProto body analysis) = procImpln def
        let prims = bodyPrims body
        let aliasPairs = List.foldr
                            (\prim alias ->
                                let args = escapablePrimArgs $ content prim
                                in aliasProcVars entryProto args alias) [] prims
        let aliasPairs' = removeDupTuples aliasPairs
        let analysis' = analysis { procArgAliases = aliasPairs' }
        logOptimise $ "Alias pairs: " ++ show aliasPairs'
        logOptimise ".....................\n\n"
        return def { procImpln = ProcDefPrim entryProto body analysis'}
checkEscape def = return def


escapablePrimArgs :: Prim -> [PrimArg]
escapablePrimArgs (PrimForeign _ "move" _ args) = args
escapablePrimArgs (PrimForeign _ "mutate" _ args) = args
escapablePrimArgs _ = []


-- Only append to list if the arg is passed in by the enclosing entry proc or is
-- the return arg of the proc
-- entryProto: the enclosing proc
-- args: the list of PrimArg, the arguments of the prim enclosed in entryProto
argsOfProcProto :: PrimProto -> (PrimArg -> PrimVarName) -> [PrimArg]
                    -> [Int]
argsOfProcProto entryProto varNameGetter args =
    -- paramNames is a list of PrimVarName of arguments of the enclosing proc
    let paramNames = procProtoParamNames entryProto
    in List.foldl (\es arg ->
        if isProcProtoArg paramNames arg
            then
                let vnm = varNameGetter arg
                    vidx = List.elemIndex vnm paramNames
                in case vidx of
                    Just vidx -> vidx : es
                    Nothing -> es
            else es) [] args


-- Cartesian product of escaped FlowIn vars to proc output
cartProd :: [a] -> [a] -> [(a, a)]
cartProd ins outs = [(i, o) | i <- ins, o <- outs]


-- Check Arg escape in one prim of prims of the a ProcBody
aliasProcVars :: PrimProto -> [PrimArg] -> [(Int, Int)]
                     -> [(Int, Int)]
aliasProcVars entryProto [] aliasPairs = aliasPairs
aliasProcVars entryProto args aliasPairs =
    let inputArgs = List.filter ((FlowIn ==) . argFlowDirection) args
        outputArgs = List.filter ((FlowOut ==) . argFlowDirection) args
        escapedInputs = argsOfProcProto entryProto inArgVar inputArgs
        escapedVia = argsOfProcProto entryProto outArgVar outputArgs
    in cartProd escapedInputs escapedVia ++ aliasPairs
