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
optimiseSccBottomUp procs = do
    inlines <- mapM optimiseProcBottomUp $ sccElts procs
    -- XXX Don't bother to repeat optimisation to a fixed point.  That doesn't
    --     seem to hurt us.
    -- when (or $ tail inlines) $ do
    --     mapM_ optimiseProcBottomUp $ sccElts procs
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
    benefit <- (4 +) <$> procCost proto -- add 4 for time saving
    logOptimise $ "  benefit = " ++ show benefit
    cost <- bodyCost $ bodyPrims body
    logOptimise $ "  cost = " ++ show cost
    -- Inline procs where benefit >= cost and private procs with only one use
    if benefit >= cost
       || procCallCount def <= 1 && procVis def == Private
    then return $ def { procInline = True }
    else return def
    where ProcDefPrim proto body _ _ = procImpln def
decideInlining def = return def


-- |Estimate the "cost" of a call to a proc; ie, how much space the call will
--  occupy.
procCost :: PrimProto -> Compiler Int
procCost proto = do
    nonPhantoms <- filterM ((not <$>) . paramIsPhantom) $ primProtoParams proto
    return $ 1 + length nonPhantoms


-- |Estimate the "cost" of a proc body; ie, how much space the code occupies.
bodyCost :: [Placed Prim] -> Compiler Int
bodyCost pprims = sum <$> mapM (primCost . content) pprims


-- |Estimate the "cost" of an individual instruction, in terms of code size. We
--  approximate the cost of a LLVM instruction as 1, a Wybe or C call as 1 + the
--  cost of the arguments, and a test instruction as free.
primCost :: Prim -> Compiler Int
primCost (PrimForeign "llvm" _ _ _) = return 1
primCost (PrimCall _ args)          = (1+) . sum <$> mapM argCost args
primCost (PrimForeign _ _ _ args)   = (1+) . sum <$> mapM argCost args
primCost (PrimTest _)               = return 0


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
