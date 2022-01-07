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
optimiseSccBottomUp (AcyclicSCC single) = do
    void $ optimiseProcBottomUp single
    inferGlobalFlows [single]
optimiseSccBottomUp (CyclicSCC procs) = do
    inlines <- mapM optimiseProcBottomUp procs
    inferGlobalFlows procs
    -- If any but first in SCC were marked for inlining, repeat to inline
    -- in earlier procs in the SCC.
    when (or $ tail inlines)
        $ do 
            mapM_ optimiseProcBottomUp procs
            inferGlobalFlows procs


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
    def' <- procExpansion pspec def >>= decideInlining
    logOptimise $ "*** " ++ show pspec ++
      " after optimisation:" ++ showProcDef 4 def' ++ "\n"
    return def'

----------------------------------------------------------------
--                       Infering how global flow in procs
----------------------------------------------------------------


-- | Update the given ProcDef to the given GlobalFlows
updateGlobalFlows :: GlobalFlows -> ProcDef -> ProcDef
updateGlobalFlows _ ProcDef{procImpln=ProcDefSrc{}}
    = shouldnt "updateGlobalFlows on uncompiled proc"
updateGlobalFlows toSave
        pDef@ProcDef{procImpln=impln@ProcDefPrim{procImplnGlobalFlows=gFlows}}
    = pDef{procImpln=impln{procImplnGlobalFlows=updateGlobalFlows' toSave gFlows}}


updateGlobalFlows' :: GlobalFlows -> GlobalFlows -> GlobalFlows
updateGlobalFlows' toSave = 
    maybe toSave (Just . Map.filter (not . Set.null) 
                       . Map.mapWithKey (Set.filter . flip (hasGlobalFlow toSave)))


-- | Infer all global flows across the given procedures, 
-- updating their associated GlobalFlows
inferGlobalFlows :: [ProcSpec] -> Compiler ()
inferGlobalFlows procs = do
    gFlows <- foldM (collectGlobalFlows $ Set.fromList procs) emptyGlobalFlows procs
    mapM_ (updateProcDef $ updateGlobalFlows gFlows) procs


-- | Add all Global Flows from a given procedure to a set of GlobalFlows
collectGlobalFlows :: Set ProcSpec -> GlobalFlows -> ProcSpec -> Compiler GlobalFlows
collectGlobalFlows procs gFlows pspec = do
    body <- procImplnBody . procImpln <$> getProcDef pspec
    foldBodyPrims
        (const $ addPrimGlobalFlows procs)
        (return gFlows)
        (liftM2 globalFlowsUnion)
        body


-- | Add all Global Flows from a given Prim to a set of GlobalFlows.
-- If the call is to a proc in the given set of proc specs, we do not add the
-- GLobalFlows, else
-- * LPVM load instructions add a FlowIn for the respective Global
-- * LPVM store instructions add a FlowOut for the respective Global
-- * First order calls add their respective GlobalFlows into the set
-- * Resourceful higher order calls set the GlobalFlows to the universal set
addPrimGlobalFlows :: Set ProcSpec -> Prim 
                   -> Compiler GlobalFlows -> Compiler GlobalFlows
addPrimGlobalFlows procs (PrimCall _ pspec _) gFlows
    | pspec `Set.member` procs = gFlows 
addPrimGlobalFlows _ prim gFlows 
    = liftM2 globalFlowsUnion (primGlobalFlows prim) gFlows


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
          globalFlows = procImplnGlobalFlows impln
decideInlining def = return def


-- |Estimate the "cost" of a call to a proc; ie, how much space the call will
--  occupy.
procCost :: PrimProto -> GlobalFlows -> Compiler Int
procCost proto globalFlows = do
    nonPhantoms <- filterM ((not <$>) . paramIsPhantom) $ primProtoParams proto
    let globalCost = maybe 0 (Map.foldl ((. Set.size) . (+)) 0) globalFlows
    return $ 1 + length nonPhantoms + globalCost


-- |Estimate the "cost" of a proc body; ie, how much space the code occupies.
bodyCost :: [Placed Prim] -> Compiler Int
bodyCost pprims = sum <$> mapM (primCost . content) pprims


-- |Estimate the "cost" of an individual instruction, in terms of code size. We
--  approximate the cost of a LLVM instruction as 1, a Wybe or C call as 1 + the
--  cost of the arguments, and a test instruction as free.
primCost :: Prim -> Compiler Int
primCost (PrimForeign "llvm" _ _ _) = return 1
primCost (PrimCall _ _ args)        = (1+) . sum <$> mapM argCost args
primCost (PrimHigher _ fn args)     = (1+) . sum <$> mapM argCost (fn:args)
primCost (PrimForeign _ _ _ args)   = (1+) . sum <$> mapM argCost args


-- |Estimate the "cost" of an argument to a C or Wybe call.  This is 0 for
--  phantoms and unneeded arguments, which generate no code, and 1 otherwise.
argCost :: PrimArg -> Compiler Int
argCost ArgUnneeded{} = return 0
argCost arg = do
    isPhantom <- argIsPhantom arg
    return $ if isPhantom then 0 else 1


-- |Log a message, if we are logging optimisation activity.
logOptimise :: String -> Compiler ()
logOptimise = logMsg Optimise
