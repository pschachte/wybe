--  File     : BodyBuilder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri 22 May 2015 10:59:56 AEST
--  Purpose  : A monad to build up a procedure Body
--  Copyright: © 2015 Peter Schachte.  All rights reserved.
--

module BodyBuilder (
  BodyBuilder, buildBody, instr, beginFork, nextBranch, finishFork
  ) where

import AST
import Options (LogSelection(Expansion))
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

type BodyBuilder = StateT BodyState Compiler

data BodyState = BodyState {
    currBody     :: Maybe [Placed Prim], -- ^The body we're building, reversed
                                      -- If nothing, history holds current node
    history      :: [ProcBody]        -- ^Tree nodes back to the root
    } deriving Show


----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body
buildBody :: BodyBuilder a -> Compiler (a,ProcBody)
buildBody builder = do
    (a,final) <- runStateT builder $ BodyState (Just []) []
    return (a,stateBody final)


-- |Add an instruction to the current body
instr :: Placed Prim -> BodyBuilder ()
instr x = do
    (BodyState curr hist) <- get
    case curr of
      Nothing -> shouldnt "adding an instr after a fork"
      Just l  -> put $ BodyState (Just (x : l)) hist


-- |Start a new fork at the end of a body
beginFork :: PrimVarName -> Bool -> BodyBuilder ()
beginFork var last = do
    bodies <- gets stateCurrBodies
    case bodies of
      (ProcBody prims NoFork : history) ->
        put $ BodyState (Just []) 
              (ProcBody prims (PrimFork var last []) : history)
      _ -> shouldnt "Inconsistent BodyState"


-- |Finish one branch of a fork and prepare to start the next
nextBranch :: BodyBuilder ()
nextBranch = do
    bodies <- gets stateCurrBodies
    case bodies of
      (curr : (ProcBody prims (PrimFork var last branches)) : history) ->
        put $ BodyState (Just []) 
              (ProcBody prims (PrimFork var last (branches++[curr])) : history)
      _ -> shouldnt "nextBranch without beginFork"


-- |Finish the whole fork
finishFork :: BodyBuilder ()
finishFork = do
    bodies <- gets stateCurrBodies
    case bodies of
      (curr : (ProcBody prims (PrimFork var last branches)) : history) ->
        put $ BodyState Nothing
              (ProcBody prims (PrimFork var last (branches++[curr])) : history)
      _ -> shouldnt "nextBranch without beginFork"


----------------------------------------------------------------
--                          Extracting the Actual Body
----------------------------------------------------------------

stateCurrBodies :: BodyState -> [ProcBody]
stateCurrBodies (BodyState Nothing bodies) = bodies
stateCurrBodies (BodyState (Just prims) bodies) =
    ProcBody (reverse prims) NoFork : bodies


stateBody :: BodyState -> ProcBody
stateBody state =
    case stateCurrBodies state of
      [] -> shouldnt "Inconsistent BodyState"
      [body] -> body
      _ -> shouldnt "BodyBuilder with unfinished fork"
