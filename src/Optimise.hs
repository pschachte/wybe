--  File     : Normalise.hs
--  Author   : Peter Schachte
--  Purpose  : Framework to optimise a single module
--  Copyright: (c) 2014-2019 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Optimise (optimiseMod) where

import           AST
import           Callers                   (getSccProcs)
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Set                  as Set
import           UnivSet                   as USet
import           Data.Graph
import           Expansion
import           Options                   (LogSelection (Optimise))
import           Types
import           Util
import           Debug.Trace


-- optimiseMod :: ModSpec -> Compiler (Bool,[(String,OptPos)])
optimiseMod :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
optimiseMod _ thisMod = do
    reenterModule thisMod
    -- checkFullyTyped -- Sanity check: be sure everything is fully typed
    orderedProcs <- getSccProcs thisMod
    logOptimise $ "Optimise SCCs:\n" ++
        unlines (List.map (show . sccElts) orderedProcs)
    -- XXX this is wrong:  it does not do a proper top-down
    -- traversal, as it is not guaranteed to vist all callers before
    -- visiting the called proc.  Need to construct inverse graph instead.
    -- mapM_ (mapM_ optimiseProcTopDown .  sccElts) $ reverse orderedProcs

    mapM_ optimiseSccBottomUp orderedProcs

    reexitModule
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
optimiseSccBottomUp :: SCC ProcSpec -> Compiler ()
optimiseSccBottomUp (AcyclicSCC single) = optimiseSccBottomUp' [single]
optimiseSccBottomUp (CyclicSCC procs) = optimiseSccBottomUp' procs


-- | As with optimiseSccBottomUp, but operates on a list of procs
optimiseSccBottomUp' :: [ProcSpec] -> Compiler ()
optimiseSccBottomUp' procs = do
    -- We perform an extra inference here because it is possible
    -- that the current global flow interface is not strict
    inferGlobalFlows procs
    repeat <- optimiseProcsBottomUp procs
    -- If any but first in SCC were marked for inlining, repeat to inline
    -- in earlier procs in the SCC.
    when repeat
        $ void $ optimiseProcsBottomUp procs


-- | Do bottom-up optimisations of Procs, returning which to inline
optimiseProcsBottomUp :: [ProcSpec] -> Compiler Bool
optimiseProcsBottomUp procs = do
    inlines <- mapM optimiseProcBottomUp procs
    -- Optimise may have removed some global flows, so we try to restrict the
    -- interface
    globals <- inferGlobalFlows procs
    return $ or $ tail inlines ++ tail globals


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
    def' <- procExpansion pspec def >>= decideInlining
    logOptimise $ "*** " ++ show pspec ++
      " after optimisation:" ++ showProcDef 4 def' ++ "\n"
    return def'


optimiseProcTopDown :: ProcSpec -> Compiler ()
optimiseProcTopDown pspec = do
    logOptimise $ ">>> Optimise (Top-down) " ++ show pspec
    updateProcDefM (optimiseProcDefTD pspec) pspec


optimiseProcDefTD :: ProcSpec -> ProcDef -> Compiler ProcDef
optimiseProcDefTD pspec def = do
    return def


----------------------------------------------------------------
--                       Deciding what to inline
----------------------------------------------------------------

-- |Decide whether to inline the proc and mark it if so.  If it's already
--  marked to be inlined, don't second guess that.  If it's impure, don't
--  mark it for inlining, but don't override if the user declared it inline.
decideInlining :: ProcDef -> Compiler ProcDef
decideInlining def | procImpurity def > Semipure  = return def
decideInlining def
    |  NoFork == bodyFork body && procInlining def == MayInline = do
    logOptimise $ "Considering inline of " ++ procName def
    benefit <- (4 +) <$> procCost proto globalFlows -- add 4 for time saving
    logOptimise $ "  benefit = " ++ show benefit
    cost <- bodyCost $ bodyPrims body
    logOptimise $ "  cost = " ++ show cost
    -- Inline procs where benefit >= cost and private procs with only one use
    if benefit >= cost
       || procCallCount def <= 1 && procVis def == Private
    then return $ def { procInlining = Inline }
    else return def
    where impln = procImpln def
          proto = procImplnProto impln
          body = procImplnBody impln
          globalFlows = primProtoGlobalFlows proto
decideInlining def = return def


-- |Estimate the "cost" of a call to a proc; ie, how much space the call will
--  occupy.
procCost :: PrimProto -> GlobalFlows -> Compiler Int
procCost proto GlobalFlows{globalFlowsIn=ins, globalFlowsOut=outs} = do
    nonPhantoms <- filterM ((not <$>) . paramIsPhantom) $ primProtoParams proto
    let globalCost = Set.size . USet.toSet Set.empty
    return $ 1 + length nonPhantoms + globalCost ins + globalCost outs


-- |Estimate the "cost" of a proc body; ie, how much space the code occupies.
bodyCost :: [Placed Prim] -> Compiler Int
bodyCost pprims = sum <$> mapM (primCost . content) pprims


-- |Estimate the "cost" of an individual instruction, in terms of code size. We
--  approximate the cost of a LLVM instruction as 1, a Wybe or C call as 1 + the
--  cost of the arguments, and a test instruction as free.
primCost :: Prim -> Compiler Int
primCost (PrimForeign "llvm" _ _ _) = return 1
primCost (PrimCall _ _ _ args _)      = (1+) . sum <$> mapM argCost args
primCost (PrimHigher _ fn args)     = (1+) . sum <$> mapM argCost (fn:args)
primCost (PrimForeign _ _ _ args)   = (1+) . sum <$> mapM argCost args


-- |Estimate the "cost" of an argument to a C or Wybe call.  This is 0 for
--  phantoms and unneeded arguments, which generate no code, and 1 otherwise.
argCost :: PrimArg -> Compiler Int
argCost ArgUnneeded{} = return 0
argCost arg = do
    isPhantom <- argIsPhantom arg
    return $ if isPhantom then 0 else 1


----------------------------------------------------------------
--                       Infering Global Flows
----------------------------------------------------------------


-- | Infer all global flows across the given procedures,
-- updating their associated GlobalFlows to (possibly) smaller sets, and
-- ensuring the global flows of all prims are correct
inferGlobalFlows :: [ProcSpec] -> Compiler [Bool]
inferGlobalFlows procs = do
    let procSet = Set.fromList procs
    implns <- (procImpln <$>) <$> mapM getProcDef procs
    let oldFlows = primProtoGlobalFlows . procImplnProto <$> implns 
    let newFlows = inferGlobalFlows' <$> implns
    let sccFlows = Map.fromList $ zipWith ((,) . procImplnProcSpec) implns newFlows
    mapM_ (updateProcDefM $ updateProcDefGlobalFlows sccFlows) procs
    return $ zipWith (/=) newFlows oldFlows


-- | Helper for inferGlobalFlows, applied to a single ProcBody
inferGlobalFlows' :: ProcImpln -> GlobalFlows
inferGlobalFlows' ProcDefSrc{} = shouldnt "inferGlobalFlows'"
inferGlobalFlows' (ProcDefPrim pspec 
                    (PrimProto _ _ oldFlows@(GlobalFlows ins outs) ) body _ _) = 
    bodyGlobalFlows (ins `USet.intersection` outs) body
                `globalFlowsIntersection` oldFlows



-- | Get the global flows that occur across a ProcBody, given the procs that appear
-- in the SCC and the Globals that occur in/out
bodyGlobalFlows :: UnivSet GlobalInfo -> ProcBody -> GlobalFlows 
bodyGlobalFlows oldFlows (ProcBody prims fork) 
    = List.foldr (globalFlowsUnion' . (snd . primArgs) . content) 
                 (forkGlobalFlows oldFlows fork) prims
  where 
    -- kill in-flows from second that have only an outwards flow in first
    globalFlowsUnion' (GlobalFlows i1 o1) (GlobalFlows i2 o2)
        = GlobalFlows 
            (i1 `USet.union` whenFinite (`Set.difference` USet.toSet Set.empty o1) i2) 
            (o1 `USet.union` o2)

-- | Global flows that occur across forks, accounting for the old in/out flows.
-- If a flow out does not occur in all branches, but at least 1, and occurs in
-- the old in/out, then this also occurs in/out 
forkGlobalFlows :: UnivSet GlobalInfo -> PrimFork -> GlobalFlows
forkGlobalFlows _ NoFork = emptyGlobalFlows
forkGlobalFlows oldFlows (PrimFork _ _ _ bodies) =
    let gFlows = bodyGlobalFlows oldFlows <$> bodies
        gOuts = globalFlowsOut <$> gFlows
        someOuts = List.foldr USet.union emptyUnivSet gOuts 
        allOuts = List.foldr USet.intersection UniversalSet gOuts
        oldFlows' = oldFlows `USet.intersection` 
                        whenFinite (`USet.subtractUnivSet` allOuts) someOuts
    in List.foldr globalFlowsUnion (GlobalFlows oldFlows' emptyUnivSet) gFlows


-- | Update the GlobalFlows of Prims of a ProcDef and the prototype with
-- the given GlobalFlows
updateProcDefGlobalFlows :: Map ProcSpec GlobalFlows -> ProcDef -> Compiler ProcDef
updateProcDefGlobalFlows _ ProcDef{procImpln=ProcDefSrc{}} =
    shouldnt "updateProcDefGlobalFlows on un-compiled code"
updateProcDefGlobalFlows sccFlows def@ProcDef{procImpln=impln@ProcDefPrim{
                                                procImplnProcSpec=pspec,
                                                procImplnBody=body,
                                                procImplnProto=proto}} = do
    body' <- updateBodyGlobalFlows sccFlows body
    let newFlows = trustFromJust "updateProcDefGlobalFlows" 
                 $ Map.lookup pspec sccFlows
    return def{procImpln=impln{
        procImplnBody=body',
        procImplnProto=proto{primProtoGlobalFlows=newFlows}}}


-- | Update the GlobalFlows of Prims of a ProcBody
updateBodyGlobalFlows :: Map ProcSpec GlobalFlows -> ProcBody -> Compiler ProcBody
updateBodyGlobalFlows sccFlows (ProcBody body fork) = do
    body' <- mapM (updatePlacedM $ updatePrimGlobalFlows sccFlows) body
    ProcBody body' <$> updateForkGlobalFlows sccFlows fork
    

-- | Update the GlobalFlows of Prims across a PrimFork
updateForkGlobalFlows :: Map ProcSpec GlobalFlows -> PrimFork -> Compiler PrimFork
updateForkGlobalFlows _ NoFork = return NoFork
updateForkGlobalFlows sccFlows (PrimFork var ty final bodies) =
    PrimFork var ty final <$> mapM (updateBodyGlobalFlows sccFlows) bodies


-- | Update the GlobalFlows of a Prim
-- If the prim is a call to a proc in the Set of ProcSpecs, we update the
-- GlobalFlows to the intersection of the given GlobalFlows and the current
updatePrimGlobalFlows :: Map ProcSpec GlobalFlows -> Prim -> Compiler Prim
updatePrimGlobalFlows sccFlows (PrimCall cID pspec impurity args gFlows) = 
    case Map.lookup pspec sccFlows of
        Just newFlows -> return $ PrimCall cID pspec impurity args newFlows
        Nothing -> do
            flows <- getProcGlobalFlows pspec
            return $ PrimCall cID pspec impurity args flows
updatePrimGlobalFlows _ prim = return prim


-- | Get the leading outwards flows of a proc body, 
-- i.e., outwards flows that occur before a corresponding inwards flow
bodyLeadingOutFlows :: ProcBody -> Set GlobalInfo
bodyLeadingOutFlows (ProcBody prims fork) = 
    List.foldr (killFlows . content) (forkLeadingOutFlows fork) prims


-- | Get the leading outwards flows of a PrimFork, 
-- i.e., outwards flows that occur before a corresponding inwards flow
forkLeadingOutFlows :: PrimFork -> Set GlobalInfo 
forkLeadingOutFlows NoFork = Set.empty
forkLeadingOutFlows (PrimFork _ _ _ bodies) = 
    List.foldr1 Set.intersection $ bodyLeadingOutFlows <$> bodies


-- | Get the leading outwards flows of a proc body, 
-- i.e., outwards flows that occur before a corresponding inwards flow
killFlows :: Prim -> Set GlobalInfo -> Set GlobalInfo
killFlows prim oldKilled = 
    (oldKilled `Set.union` USet.toSet Set.empty outs) `USet.subtractUnivSet` ins
  where GlobalFlows ins outs = snd $ primArgs prim

-- |Log a message, if we are logging optimisation activity.
logOptimise :: String -> Compiler ()
logOptimise = logMsg Optimise
