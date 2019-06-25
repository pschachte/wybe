--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 19:02:05 EST 2014
--  Purpose  : Framework to optimise a single module
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.

module Optimise (optimiseMod) where

import           AST
import           Callers                   (getSccProcs)
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Set                  as Set
import           Expansion
import           Options                   (LogSelection (Optimise))
import           Types
import           Util


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
    mapM_ (mapM_ optimiseProcTopDown .  sccElts) $ reverse orderedProcs

    mapM_ optimiseSccBottomUp orderedProcs

    _ <- reexitModule
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
    1 + (length $ List.filter (not . paramIsPhantom) $ primProtoParams proto)

bodyCost :: [Placed Prim] -> Int
bodyCost pprims = sum $ List.map (primCost . content) pprims

primCost :: Prim -> Int
primCost (PrimCall _ args)          = 1 + (sum $ List.map argCost args)
primCost (PrimForeign "llvm" _ _ _) = 1 -- single instuction, so cost = 1
primCost (PrimForeign "$" _ _ _)    = 1    -- single instuction, so cost = 1
primCost (PrimForeign _ _ _ args)   = 1 + (sum $ List.map argCost args)
primCost (PrimTest _)               = 0

argCost :: PrimArg -> Int
argCost arg = if argIsPhantom arg then 0 else 1


-- |Log a message, if we are logging optimisation activity.
logOptimise :: String -> Compiler ()
logOptimise = logMsg Optimise
