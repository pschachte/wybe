--  File     : BodyBuilder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri 22 May 2015 10:59:56 AEST
--  Purpose  : A monad to build up a procedure Body
--  Copyright: © 2015 Peter Schachte.  All rights reserved.
--

module BodyBuilder (
  -- BodyBuilder, buildBody, instr, beginFork, nextBranch, finishFork
  BodyBuilder, buildBody, instr, buildFork
  ) where

import AST
import Options (LogSelection(BodyBuilder))
import Data.Map as Map
import Data.List as List
import Data.Set as Set
import Data.Maybe
import Control.Monad
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.Trans.State

import Debug.Trace

----------------------------------------------------------------
--                       The BodyBuilder Monad
--
-- This monad keeps track of variable renaming needed to keep inlining
-- hygenic.  To do this, we rename all the input parameters of the proc to 
-- be inlined, and when expanding the body, we rename any variables when 
-- first assigned.  The exception to this is the proc's output parameters.  
-- These are kept as a set.  We also maintain a counter for temporary 
-- variable names.
----------------------------------------------------------------

-- type BodyBuilder = StateT BodyState Compiler
type BodyBuilder = StateT ProcBody Compiler

-- data BodyState = BodyState {
--     currBody     :: Maybe [Placed Prim], -- ^The body we're building, reversed
--                                       -- If nothing, history holds current node
--     history      :: [ProcBody]        -- ^Tree nodes back to the root
--     } deriving Show


----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body
buildBody :: BodyBuilder a -> Compiler (a,ProcBody)
buildBody builder = do
    logMsg BodyBuilder "<<<< Beginning to build a proc body"
    -- (a,final) <- runStateT builder $ BodyState (Just []) []
    (a,ProcBody revPrims fork) <- runStateT builder $ ProcBody [] NoFork
    logMsg BodyBuilder ">>>> Finished  building a proc body"
    -- return (a,astateBody final)
    return (a,ProcBody (reverse revPrims) fork)


buildFork :: PrimVarName -> Bool -> [BodyBuilder ()] -> BodyBuilder ()
buildFork var last branchBuilders = do
    logBuild $ "<<<< beginning to build a new fork on " ++ show var 
      ++ " (last=" ++ show last ++ ")"
    ProcBody revPrims fork <- get
    case fork of
      PrimFork _ _ _ -> shouldnt "Building a fork while building a fork"
      NoFork -> put $ ProcBody revPrims $ PrimFork var last []
    mapM buildBranch branchBuilders
    ProcBody revPrims' fork' <- get
    case fork' of
      NoFork -> shouldnt "Building a fork produced and empty fork"
      PrimFork v l revBranches ->
        put $ ProcBody revPrims' $ PrimFork v l $ reverse revBranches
    logBuild $ ">>>> Finished building a fork"


buildBranch :: BodyBuilder () -> BodyBuilder ()
buildBranch builder = do
    logBuild "<<<< <<<< Beginning to build a branch"
    branch <- buildPrims builder
    logBuild ">>>> >>>> Finished  building a branch"
    ProcBody revPrims fork <- get
    case fork of
      NoFork -> shouldnt "Building a branch outside of buildFork"
      PrimFork v l branches ->
        put $ ProcBody revPrims $ PrimFork v l $ branch : branches

buildPrims :: BodyBuilder () -> BodyBuilder ProcBody
buildPrims builder = do
    ((),ProcBody revPrims fork) <- lift $ runStateT builder $ ProcBody [] NoFork
    return $ ProcBody (reverse revPrims) fork

-- |Add an instruction to the current body
instr :: Placed Prim -> BodyBuilder ()
instr x = do
    logBuild $ "---- adding instruction " ++ show x
    ProcBody instrs fork <- get
    case fork of
      PrimFork _ _ _ -> shouldnt "adding an instr after a fork"
      NoFork -> put $ ProcBody (x : instrs) fork
    -- (BodyState curr hist) <- get
    -- case curr of
    --   Nothing -> shouldnt "adding an instr after a fork"
    --   Just l  -> do
    --     logBuild $ "---- adding instruction " ++ show x
    --     put $ BodyState (Just (x : l)) hist


-- -- |Start a new fork at the end of a body
-- beginFork :: PrimVarName -> Bool -> BodyBuilder ()
-- beginFork var last = do
--     logBuild $ "---- <<<< beginning to build a new fork"
--     bodies <- gets stateCurrBodies
--     case bodies of
--       (ProcBody prims NoFork : history) ->
--         put $ BodyState (Just []) 
--               (ProcBody prims (PrimFork var last []) : history)
--       _ -> shouldnt "Inconsistent BodyState"


-- -- |Finish one branch of a fork and prepare to start the next
-- nextBranch :: BodyBuilder ()
-- nextBranch = do
--     logBuild $ "==== starting new branch of the fork (ending previous one)"
--     bodies <- gets stateCurrBodies
--     case bodies of
--       (curr : (ProcBody prims (PrimFork var last branches)) : history) ->
--         put $ BodyState (Just []) 
--               (ProcBody prims (PrimFork var last (branches++[curr])) : history)
--       _ -> shouldnt "nextBranch without beginFork"


-- -- |Finish the whole fork
-- finishFork :: BodyBuilder ()
-- finishFork = do
--     logBuild $ "---- <<<< finished building a new fork"
--     bodies <- gets stateCurrBodies
--     case bodies of
--       (curr : (ProcBody prims (PrimFork var last branches)) : history) ->
--         put $ BodyState Nothing
--               (ProcBody prims (PrimFork var last (branches++[curr])) : history)
--       _ -> shouldnt "nextBranch without beginFork"


----------------------------------------------------------------
--                          Extracting the Actual Body
----------------------------------------------------------------

-- stateCurrBodies :: BodyState -> [ProcBody]
-- stateCurrBodies (BodyState Nothing bodies) = bodies
-- stateCurrBodies (BodyState (Just prims) bodies) =
--     ProcBody (reverse prims) NoFork : bodies


-- stateBody :: BodyState -> ProcBody
-- stateBody state =
--     case stateCurrBodies state of
--       [] -> shouldnt "Inconsistent BodyState"
--       [body] -> body
--       _ -> shouldnt "BodyBuilder with unfinished fork"


----------------------------------------------------------------
--                                  Logging
----------------------------------------------------------------

-- |Log a message, if we are logging unbrancher activity.
logBuild :: String -> BodyBuilder ()
logBuild s = lift $ logMsg BodyBuilder s
