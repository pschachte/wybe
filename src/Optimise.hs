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
    inlines <- optimiseProcsBottomUp procs
    -- If any but first in SCC were marked for inlining, repeat to inline
    -- in earlier procs in the SCC.
    when (or $ tail inlines)
        $ void $ optimiseProcsBottomUp procs


-- | Do bottom-up optimisations of Procs, returning which to inline
optimiseProcsBottomUp :: [ProcSpec] -> Compiler [Bool]
optimiseProcsBottomUp procs = do
    inlines <- mapM optimiseProcBottomUp procs
    -- Optimise may have removed some global flows, so we try to restrict the
    -- interface
    inferGlobalFlows procs
    return inlines


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
--  marked to be inlined, don't second guess that.
decideInlining :: ProcDef -> Compiler ProcDef
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
primCost (PrimCall _ _ args _ _)      = (1+) . sum <$> mapM argCost args
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
inferGlobalFlows :: [ProcSpec] -> Compiler ()
inferGlobalFlows procs = do
    let procSet = Set.fromList procs
    gFlows <- foldM (addGlobalFlows procSet) emptyGlobalFlows procs
    mapM_ (updateProcDefM $ updateProcDefGlobalFlows procSet gFlows) procs


-- | Add all Global Flows from a given procedure to a set of GlobalFlows,
-- ingoring calls to those that are in the Set of ProcSpecs
addGlobalFlows :: Set ProcSpec -> GlobalFlows -> ProcSpec -> Compiler GlobalFlows
addGlobalFlows procs gFlows pspec =
    foldBodyPrims (const $ globalFlowsUnion . primGlobalFlows' procs)
                  gFlows globalFlowsUnion
        . procImplnBody . procImpln <$> getProcDef pspec


-- | Add all Global Flows from a given Prim to a set of GlobalFlows.
-- If the call is to a proc in the given Set of ProcSpecs, we do not add the
-- GlobalFlows, else we add the global flows associated with the proc
primGlobalFlows' :: Set ProcSpec -> Prim -> GlobalFlows
primGlobalFlows' procs (PrimCall _ pspec _ _ _)
    | pspec `Set.member` procs = emptyGlobalFlows
primGlobalFlows' _ prim = snd $ primArgs prim


-- | Update the GlobalFlows of Prims of a ProcDef and the prototype with
-- the given GlobalFlows
updateProcDefGlobalFlows :: Set ProcSpec -> GlobalFlows -> ProcDef -> Compiler ProcDef
updateProcDefGlobalFlows _ _ ProcDef{procImpln=ProcDefSrc{}} =
    shouldnt "updateProcDefGlobalFlows on un-compiled code"
updateProcDefGlobalFlows procs newFlows
        def@ProcDef{procImpln=impln@ProcDefPrim{
            procImplnBody=body,
            procImplnProto=proto@PrimProto{primProtoGlobalFlows=oldFlows}}} = do
    body' <- updateBodyGlobalFlows procs newFlows body
    return def{procImpln=impln{
        procImplnBody=body',
        procImplnProto=proto{
            primProtoGlobalFlows=globalFlowsIntersection newFlows oldFlows}}}


-- | Update the GlobalFlows of Prims of a ProcBody
updateBodyGlobalFlows :: Set ProcSpec -> GlobalFlows -> ProcBody -> Compiler ProcBody
updateBodyGlobalFlows procs newFlows (ProcBody body fork) = do
    body' <- mapM (updatePlacedM $ updatePrimGlobalFlows procs newFlows) body
    ProcBody body' <$> case fork of
        NoFork -> return NoFork
        PrimFork{forkBodies=forks} -> do
            forks' <- mapM (updateBodyGlobalFlows procs newFlows) forks
            return fork{forkBodies=forks'}


-- | Update the GlobalFlows of a Prim
-- If the prim is a call to a proc in the Set of ProcSpecs, we update the
-- GlobalFlows to the intersection of the given GlobalFlows and the current
updatePrimGlobalFlows :: Set ProcSpec -> GlobalFlows -> Prim -> Compiler Prim
updatePrimGlobalFlows procs newFlows (PrimCall cID pspec args gFlows attrs)
    | pspec `Set.member` procs
    = return $ PrimCall cID pspec args (globalFlowsIntersection newFlows gFlows) attrs
    | otherwise = do
        flows <- getProcGlobalFlows pspec
        return $ PrimCall cID pspec args flows attrs
updatePrimGlobalFlows _ _ prim = return prim


-- |Log a message, if we are logging optimisation activity.
logOptimise :: String -> Compiler ()
logOptimise = logMsg Optimise
