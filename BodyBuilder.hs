--  File     : BodyBuilder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri 22 May 2015 10:59:56 AEST
--  Purpose  : A monad to build up a procedure Body, with copy propagation
--  Copyright: © 2015 Peter Schachte.  All rights reserved.
--

module BodyBuilder (
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

type BodyBuilder = StateT BodyState Compiler

data BodyState = BodyState {
    currBody     :: ProcBody,         -- ^The body we're building, lists reversed
    currSubst    :: Substitution,     -- ^variable substitutions to propagate
    protected    :: Set PrimVarName   -- ^Variables that cannot be renamed
    } deriving Show

type Substitution = Map PrimVarName PrimArg


initState :: Set PrimVarName -> BodyState
initState protected = BodyState (ProcBody [] NoFork) Map.empty protected


continueState :: Substitution -> Set PrimVarName -> BodyState
continueState subst protected = BodyState (ProcBody [] NoFork) subst protected


----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body
buildBody :: Set PrimVarName -> BodyBuilder a -> Compiler (a,ProcBody)
buildBody prot builder = do
    logMsg BodyBuilder "<<<< Beginning to build a proc body"
    -- (a,final) <- runStateT builder $ BodyState (Just []) []
    (a,BodyState (ProcBody revPrims fork) _ _) <- runStateT builder $ 
                                                  initState prot
    logMsg BodyBuilder ">>>> Finished  building a proc body"
    -- return (a,astateBody final)
    return (a,ProcBody (reverse revPrims) fork)


-- XXX Ensure forks with only one branch are turned into straight-line code.
buildFork :: PrimVarName -> Bool -> [BodyBuilder ()] -> BodyBuilder ()
buildFork var last branchBuilders = do
    logBuild $ "<<<< beginning to build a new fork on " ++ show var 
      ++ " (last=" ++ show last ++ ")"
    ProcBody revPrims fork <- gets currBody
    case fork of
      PrimFork _ _ _ -> shouldnt "Building a fork while building a fork"
      NoFork -> modify (\s -> s {currBody = ProcBody revPrims $ PrimFork var last [] })
    mapM buildBranch branchBuilders
    ProcBody revPrims' fork' <- gets currBody
    case fork' of
      NoFork -> shouldnt "Building a fork produced and empty fork"
      PrimFork v l revBranches ->
        modify (\s -> s { currBody = ProcBody revPrims' $ 
                                     PrimFork v l $ reverse revBranches })
    logBuild $ ">>>> Finished building a fork"


buildBranch :: BodyBuilder () -> BodyBuilder ()
buildBranch builder = do
    logBuild "<<<< <<<< Beginning to build a branch"
    branch <- buildPrims builder
    logBuild ">>>> >>>> Finished  building a branch"
    ProcBody revPrims fork <- gets currBody
    case fork of
      NoFork -> shouldnt "Building a branch outside of buildFork"
      PrimFork v l branches ->
        modify (\s -> s { currBody = ProcBody revPrims $ 
                                     PrimFork v l $ branch : branches })

buildPrims :: BodyBuilder () -> BodyBuilder ProcBody
buildPrims builder = do
    subst <- gets currSubst
    prot <- gets protected
    ((),BodyState (ProcBody revPrims fork) _ _) <- 
      lift $ runStateT builder $ continueState subst prot
    return $ ProcBody (reverse revPrims) fork


-- |Add an instruction to the current body, after applying the current substitution.
--  If it's a move instruction, add it to the current substitution, and only add it
--  if it assigns a protected variable.
instr :: Prim -> OptPos -> BodyBuilder ()
instr (PrimCall pspec args) pos = do
    args' <- mapM expandArg args
    rawInstr (PrimCall pspec args') pos
instr (PrimForeign "llvm" "move" [] [val, argvar@(ArgVar var _ flow _ _)]) pos = do
    val' <- expandArg val
    logBuild $ "  Expanding move(" ++ show val' ++ ", " ++ show argvar ++ ")"
    unless (flow == FlowOut && argFlowDirection val' == FlowIn) $ 
      shouldnt "move instruction with wrong flow"
    addSubst var val'
    noSubst <- gets (Set.member var . protected)
    -- keep this assignment if we need to
    when noSubst $ rawInstr (PrimForeign "llvm" "move" [] [val', argvar]) pos
instr (PrimForeign  lang nm flags args) pos = do
    args' <- mapM expandArg args
    rawInstr (PrimForeign  lang nm flags args') pos
instr PrimNop _ = do
    -- Filter out NOPs
    return ()


-- |Add a binding for a variable.  If that variable is an output for the proc being
--  defined, also add an explicit assignment to that variable.
addSubst :: PrimVarName -> PrimArg -> BodyBuilder ()
addSubst var val = do
    logBuild $ "      adding subst " ++ show var ++ " -> " ++ show val
    modify (\s -> s { currSubst = Map.insert var val $ currSubst s })
    subst <- gets currSubst
    logBuild $ "      new subst = " ++ show subst

-- |Unconditionally add an instr to the current body
rawInstr :: Prim -> OptPos -> BodyBuilder ()
rawInstr prim pos = do
    logBuild $ "---- adding instruction " ++ show prim
    ProcBody prims fork <- gets currBody
    case fork of
      PrimFork _ _ _ -> shouldnt "adding an instr after a fork"
      NoFork ->     
        modify (\s -> s { currBody = ProcBody (maybePlace prim pos : prims) fork })

-- |Return the current ultimate value of the input argument.
expandArg :: PrimArg -> BodyBuilder PrimArg
expandArg arg@(ArgVar var typ FlowIn ftype _) = do
    var' <- gets (Map.lookup var . currSubst)
    maybe (return arg) expandArg var'
expandArg arg = return arg


setPrimArgFlow :: PrimFlow -> ArgFlowType -> PrimArg -> PrimArg
setPrimArgFlow flow ftype (ArgVar n t _ _ lst) = (ArgVar n t flow ftype lst)
setPrimArgFlow FlowIn _ arg = arg
setPrimArgFlow FlowOut _ arg =
    -- XXX eventually want this to generate a comparison, once we allow failure
    shouldnt $ "trying to make " ++ show arg ++ " an output argument"


----------------------------------------------------------------
--                          Extracting the Actual Body
----------------------------------------------------------------

----------------------------------------------------------------
--                                  Logging
----------------------------------------------------------------

-- |Log a message, if we are logging unbrancher activity.
logBuild :: String -> BodyBuilder ()
logBuild s = lift $ logMsg BodyBuilder s
