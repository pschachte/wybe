--  File     : BodyBuilder.hs
--  Author   : Peter Schachte
--  Purpose  : A monad to build up a procedure Body, with copy propagation
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module BodyBuilder (
  BodyBuilder, buildBody, freshVarName, instr, buildFork, completeFork,
  beginBranch, endBranch, definiteVariableValue
  ) where

import AST
import Snippets
import Util
import Options (LogSelection(BodyBuilder))
import Data.Map as Map
import Data.List as List
import Data.Set as Set
import Data.Maybe
import Data.Bits
import Control.Applicative
import Control.Monad
import Control.Monad.Extra (whenJust)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State


----------------------------------------------------------------
--                       The BodyBuilder Monad
--
-- This monad is used to build up a ProcBody one instruction at a time.
--
-- buildBody runs the monad, producing a ProcBody.
-- instr adds a single instruction to then end of the procBody being built.
-- Forks are produced by the following functions:
--    buildFork     initiates a fork on a specified variable
--    beginBranch   starts a new branch of the current fork
--    endBranch     ends the current branch
--    completeFork  completes the current fork
--
-- A ProcBody is considered to have a unique continuation if it either
-- does not end in a branch, or if all but at most one of the branches
-- it ends with ends with a definite failure (a PrimTest (ArgInt 0 _)).
--
-- No instructions can be added between buildFork and beginBranch, or
-- between endBranch and beginBranch, or if the current state does not have
-- a unique continuation. A new fork can be built within a branch, but must
-- be completed before the branch is ended.
--
-- The ProcBody type does not support having anything follow a fork. Once a
-- ProcBody forks, the branches do not join again. Instead, each branch of
-- a fork should end with a call to another proc, which does whatever
-- should come after the fork. To handle this, once a fork is completed,
-- the BodyBuilder starts a new Unforked instruction sequence, and records
-- the completed fork as the predecessor of the Unforked sequence. This
-- also permits a fork to follow the Unforked sequence which follows a
-- fork. When producing the final ProcBody, if the current Unforked
-- sequence is short (or empty) and there is a predecessor fork, we simply
-- add the sequence to the end of each of branch of the fork and remove the
-- Unforked sequence. If it is not short and there is a predecessor, we
-- create a fresh proc whose input arguments are all the live variables,
-- whose outputs are the current proc's outputs, and whose body is built
-- from Unforked sequence, add a call to this fresh proc to each branch of
-- the previous Forked sequence, and remove the Unforked.
--
-- We handle a Forked sequence by generating a ProcBody for each branch,
-- collecting these as the branches of a ProcBody, and taking the
-- instructions from the preceding Unforked as the instruction sequence of
-- the ProcBody.
--
-- Note that for convenience/efficiency, we collect the instructions in a
-- sequence and the branches in a fork in reverse order, so these are
-- reversed when converting to a ProcBody.
--
-- Some transformation is performed by the BodyBuilder monad; in
-- particular, we keep track of variable=variable assignments, and replace
-- references to the destination (left) variable with the source (right)
-- variable.  This usually leaves the assignment dead, to be removed in
-- a later pass.  We also keep track of previous instructions, and later
-- calls to the same instructions with the same inputs are replaced by
-- assignments to the outputs with the old outputs.  We also handle some
-- arithmetic equivalences, entailments, and tautologies (eg, on a branch
-- where we know x==y, a call to x<=y will always return true; for
-- unsigned x, x<0 is always false, and x>0 is replaced with x!=0).
-- We also maintain a counter for temporary variable names.
--
-- The BodyState has two constructors:  Unforked is used before the first
-- fork, and after each new branch is created. Instructions can just be
-- added to this. Forked is used after a new fork is begun and before its
-- first branch is created, between ending a branch and starting a new one,
-- and after the fork is completed. New instructions can be added and new
-- forks built only when in the Unforked state. In the Forked state, we can
-- only create a new branch.
--
-- These constructors are used in a zipper-like structure, where the top of the
-- structure is the part we're building, and below that is the parent, ie,
-- the fork structure of which it's a part. This is implemented as follows:
--
--     buildFork is called when the state is Unforked.  It creates a new
--     Forked state, with the old state as its origin and an empty list
--     of bodies.  The new parent is the same as the old one.
--
--     beginBranch is called when the state is Forked.  It creates a new
--     Unforked state with the old state as parent.
--
--     endBranch is called with either a Forked or Unforked state.  It
--     adds the current state to the parent state's list of bodies and
--     makes that the new state.
--
--     completeFork is called when the state is Forked.  It doesn't
--     change the state.
----------------------------------------------------------------

type BodyBuilder = StateT BodyState Compiler

-- Holds the content of a ProcBody while we're building it.
data BodyState = BodyState {
      currBuild   :: [Placed Prim],   -- ^The body we're building, reversed
      currSubst   :: Substitution,    -- ^variable substitutions to propagate
      blockDefs   :: Set PrimVarName, -- ^All variables defined in this block
      forkConsts  :: Set PrimVarName, -- ^Consts in some branches of prev fork
      outSubst    :: VarSubstitution, -- ^Substitutions for var assignments
      subExprs    :: ComputedCalls,   -- ^Previously computed calls to reuse
      failed      :: Bool,            -- ^True if this body always fails
      tmpCount    :: Int,             -- ^The next temp variable number to use
      buildState  :: BuildState,      -- ^What state this node is in
      parent      :: Maybe BodyState  -- ^What comes before/above this
      } deriving (Eq,Show)


data BuildState
    = Unforked           -- ^Still building; ready for more instrs
    | Forked {           -- ^Building a new fork
        forkingVar   :: PrimVarName,   -- ^Variable that selects branch to take
        forkingVarTy :: TypeSpec,      -- ^Type of forkingVar
        knownVal     :: Maybe Integer, -- ^Definite value of forkingVar if known
        fused        :: Bool,          -- ^forkingVar is a constant in every
                                       -- branch in the parent fork, so this
                                       -- fork will be fused with parent fork
        bodies       :: [BodyState],   -- ^Rev'd BodyStates of branches so far
        complete     :: Bool           -- ^Whether the fork has been completed
        }
    deriving (Eq,Show)


-- | A fresh BodyState with specified temp counter and output var substitution
initState :: Int -> VarSubstitution -> BodyState
initState tmp oSubst =
    BodyState [] Map.empty Set.empty Set.empty oSubst Map.empty False tmp
              Unforked Nothing


-- | Set up a BodyState as a new child of the specified BodyState
childState :: BodyState -> BuildState -> BodyState
childState st@BodyState{currSubst=iSubst,outSubst=oSubst,subExprs=subs,
                        tmpCount=tmp, forkConsts=consts} bld =
    BodyState [] iSubst Set.empty consts oSubst subs False tmp bld $ Just st


-- | A mapping from variables to definite values, in service to constant
-- propagation.
type Substitution = Map PrimVarName PrimArg


-- | A mapping from variables to their renamings.  This is in service to
-- variable elimination.
type VarSubstitution = Map PrimVarName PrimVarName


-- To handle common subexpression elimination, we keep a map from previous
-- calls with their outputs removed.  This type encapsulates
-- that.  In the Prim keys, all PrimArgs are inputs.
type ComputedCalls = Map Prim [PrimArg]


-- |Allocate the next temp variable name and ensure it's not allocated again
freshVarName :: BodyBuilder PrimVarName
freshVarName = do
    tmp <- gets tmpCount
    modify (\st -> st {tmpCount = tmp + 1})
    return $ PrimVarName (mkTempName tmp) 0



----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body, along with the
-- final temp variable count and the set of variables used in the body.
buildBody :: Int -> VarSubstitution -> BodyBuilder a
          -> Compiler (Int,Set PrimVarName,ProcBody)
buildBody tmp oSubst builder = do
    logMsg BodyBuilder "<<<< Beginning to build a proc body"
    st <- execStateT builder $ initState tmp oSubst
    logMsg BodyBuilder ">>>> Finished building a proc body"
    logMsg BodyBuilder "     Current state:"
    logMsg BodyBuilder $ fst $ showState 8 st
    currBody (ProcBody [] NoFork) st


-- |Start a new fork on var of type ty
buildFork :: PrimVarName -> TypeSpec -> BodyBuilder ()
buildFork var ty = do
    st <- get
    var' <- expandVar var boolType
    logBuild $ "<<<< beginning to build a new fork on " ++ show var
               ++ " (-> " ++ show var' ++ ")"
    case buildState st of
      Forked{complete=True} ->
        shouldnt "Building a fork in Forked state"
      Forked{complete=False} ->
        shouldnt "Building a fork in Forking state"
      Unforked -> do
        arg' <- expandVar var ty
        logBuild $ "     (expands to " ++ show arg' ++ ")"
        case arg' of
          ArgInt n _ -> -- fork variable value known at compile-time
            put $ childState st $ Forked var ty (Just n) False [] False
          ArgVar{argVarName=var',argVarType=varType} -> do
            -- statically unknown result
            consts <- gets forkConsts
            logBuild $ "Consts from parent fork = " ++ show consts
            let fused = Set.member var' consts
            logBuild $ "This fork "
                       ++ (if fused then "WILL " else "will NOT ")
                       ++ "be fused with parent"
            put $ childState st $ Forked var' ty Nothing fused [] False
          _ -> shouldnt "switch on non-integer variable"
        logState


-- |Complete a fork previously initiated by buildFork.
completeFork :: BodyBuilder ()
completeFork = do
    st <- get
    case buildState st of
      Forked{complete=True} ->
        shouldnt "Completing an already-completed fork"
      Unforked ->
        shouldnt "Completing an un-built fork"
      Forked var ty val fused bods False -> do
        logBuild $ ">>>> ending fork on " ++ show var
        -- let branchMap = List.foldr1 (Map.intersectionWith Set.union)
        --                 (Map.map Set.singleton
        --                  . Map.filter argIsConst . currSubst <$> bods)
        let branchMaps = Map.filter argIsConst . currSubst <$> bods
        -- Variables set to the same constant in every branch
        let extraSubsts = List.foldr1 intersectMapIdentity branchMaps
        logBuild $ "     extraSubsts = " ++ show extraSubsts
        -- Variables with a constant value in each branch.  These can be
        -- used later to fuse branches of subsequent forks on those variables
        -- with this fork.
        let consts = List.foldr1 Set.union
                     $ List.map Map.keysSet branchMaps
        logBuild $ "     definite variables in all branches: " ++ show consts
        -- Prepare for any instructions coming after the fork
        let parent = st {buildState = Forked var ty val fused bods True,
                         tmpCount = maximum $ tmpCount <$> bods}
        let child = childState parent Unforked
        put $ child { forkConsts = consts,
                      currSubst = Map.union extraSubsts $ currSubst child}
        logState


-- |Start a new branch for the next integer value of the switch variable.
beginBranch :: BodyBuilder ()
beginBranch = do
    st <- get
    case buildState st of
      Forked{complete=True} ->
        shouldnt "Beginning a branch in an already-completed fork"
      Unforked ->
        shouldnt "Beginning a branch in an un-built fork"
      Forked var ty val fused bods False -> do
        let branchNum = length bods
        logBuild $ "<<<< <<<< Beginning to build "
                   ++ (if fused then "fused " else "") ++ "branch "
                   ++ show branchNum ++ " on " ++ show var
        when fused $ do
          par <- gets $ trustFromJust "forkConst with no grandparent branch"
                      . (>>= parent) . parent
          case buildState par of
            Forked{bodies=bods} -> do
              let matchingSubsts =
                    List.map currSubst
                    $ List.filter (matchingSubst var branchNum) bods
              let extraSubsts =
                    if List.null matchingSubsts
                    then Map.empty
                    else List.foldr1 intersectMapIdentity matchingSubsts
              logBuild $ "          Adding substs " ++ show extraSubsts
              -- XXX shouldn't need to do this sanity check
              -- lostSubsts <- (Map.\\ extraSubsts) <$> gets currSubst
              -- unless (Map.null lostSubsts )
              --   $ shouldnt $ "Fusion loses substs " ++ show lostSubsts
              modify $ \st -> st { currSubst =
                                   Map.union extraSubsts (currSubst st) }
            Unforked -> shouldnt "forkConst predicted parent branch"
        put $ childState st Unforked
        -- XXX also add consequences of this, eg if var is result of X==Y
        --     comparison and var == 1, then record that X==Y.
        when (isNothing val && not fused)
          $ addSubst var $ ArgInt (fromIntegral branchNum) intType
        logState


-- |End the current branch.
endBranch :: BodyBuilder ()
endBranch = do
    st <- get
    (par,st,var,ty,val,fused,bodies) <- gets popParent
    logBuild $ ">>>> >>>> Ending branch "
               ++ show (length bodies) ++ " on " ++ show var
    put $ par { buildState=Forked var ty val fused (st:bodies) False }
    logState


-- |Return the closest Forking ancestor of a state, and fix its immediate
--  child to no longer list it as parent
popParent :: BodyState -> (BodyState,BodyState,PrimVarName,TypeSpec,
                           Maybe Integer,Bool,[BodyState])
popParent st@BodyState{parent=Nothing} =
    shouldnt "endBranch with no open branch to end"
popParent st@BodyState{parent=(Just
             par@BodyState{buildState=(Forked var ty val fused
                                       branches False)})} =
    (par, st {parent = Nothing}, var, ty, val, fused, branches)
popParent st@BodyState{parent=Just par} =
    let (ancestor, fixedPar, var, ty, val, fused, branches) = popParent par
    in  (ancestor,st {parent=Just fixedPar}, var, ty, val, fused, branches)


-- | Test if the specified variable is bound to the specified constant in the
-- specified BodyState.
matchingSubst :: PrimVarName -> Int -> BodyState -> Bool
matchingSubst var branchNum bod =
  maybe False ((== branchNum) . fromIntegral)
  ((Map.lookup var $ currSubst bod) >>= argIntegerValue)


-- |Return Just the known value of the specified variable, or Nothing
definiteVariableValue :: PrimVarName -> BodyBuilder (Maybe PrimArg)
definiteVariableValue var = do
    arg <- expandVar var AnyType
    case arg of
        ArgVar{} -> return Nothing -- variable (unknown) result
        _ -> return $ Just arg

buildPrims :: BodyState -> BodyBuilder a -> Compiler (a,BodyState)
buildPrims st builder = runStateT builder st


-- |Add an instruction to the current body, after applying the current
--  substitution. If it's a move instruction, add it to the current
--  substitution.
instr :: Prim -> OptPos -> BodyBuilder ()
instr prim pos = do
    st <- get
    case st of
      BodyState{failed=True}  -> do -- ignore if we've already failed
        logBuild $ "  Failing branch:  ignoring instruction " ++ show prim
        return ()
      BodyState{failed=False,buildState=Unforked} -> do
        prim' <- argExpandedPrim prim
        logBuild $ "Generating instr " ++ show prim ++ " -> " ++ show prim'
        instr' prim' pos
      _ ->
        shouldnt "instr in Forked context"


instr' :: Prim -> OptPos -> BodyBuilder ()
instr' prim@(PrimForeign "llvm" "move" []
           [val, argvar@ArgVar{argVarName=var, argVarFlow=flow}]) pos
  = do
    logBuild $ "  Expanding move(" ++ show val ++ ", " ++ show argvar ++ ")"
    unless (flow == FlowOut && argFlowDirection val == FlowIn) $
      shouldnt "move instruction with wrong flow"
    outVar <- gets (Map.findWithDefault var var . outSubst)
    addSubst outVar val
    rawInstr prim pos
    recordVarSet argvar
--     this is a bit of a hack to work around not threading a heap
--     through the code, which causes the compiler to try to reuse
--     the results of calls to alloc.  Since the mutate primitives
--     already have an output value, that should stop us from trying
--     to reuse modified structures or the results of calls to
--     access after a structure is modified, so alloc should be
--     the only problem that needs fixing.  We don't want to fix this
--     by threading a heap through, because it's fine to reorder calls
--     to alloc.
instr' prim@(PrimForeign "lpvm" "alloc" [] [_,argvar]) pos = do
    logBuild "  Leaving alloc alone"
    rawInstr prim pos
    recordVarSet argvar
instr' prim@(PrimForeign "lpvm" "cast" []
             [from, to@ArgVar{argVarName=var, argVarFlow=flow}]) pos
  = do
    logBuild $ "  Expanding cast(" ++ show from ++ ", " ++ show to ++ ")"
    unless (argFlowDirection from == FlowIn && flow == FlowOut) $
        shouldnt "cast instruction with wrong flow"
    if argType from == argType to
      then instr' (PrimForeign "llvm" "move" [] [from, to]) pos
      else ordinaryInstr prim pos
instr' prim@(PrimTest (ArgInt 0 _)) pos = do
    rawInstr prim pos
    logBuild "  Found fail instruction; noting failing branch"
    -- note guaranteed failure
    modify (\s -> s { failed=True })
instr' prim pos = ordinaryInstr prim pos


ordinaryInstr :: Prim -> OptPos -> BodyBuilder ()
ordinaryInstr prim pos = do
    let (prim',newOuts) = splitPrimOutputs prim
    logBuild $ "Looking for computed instr " ++ show prim' ++ " ..."
    currSubExprs <- gets subExprs
    logBuild $ "  with subExprs = " ++ show currSubExprs
    match <- gets (Map.lookup prim' . subExprs)
    case match of
        Nothing -> do
            -- record prim executed (and other modes), and generate instr
            logBuild "not found"
            recordEntailedPrims prim
            rawInstr prim pos
            mapM_ recordVarSet $ primOutputs prim
        Just oldOuts -> do
            -- common subexpr: just need to record substitutions
            logBuild $ "found it; substituting "
                       ++ show oldOuts ++ " for " ++ show newOuts
            mapM_ (\(newOut,oldOut) ->
                     instr' (PrimForeign "llvm" "move" []
                              [mkInput oldOut, newOut])
                     Nothing)
                  $ zip newOuts oldOuts



-- | Invert an output arg to be an input arg.
mkInput :: PrimArg -> PrimArg
mkInput (ArgVar name ty coerce _ ftype lst) =
    ArgVar name ty coerce FlowIn Ordinary False
mkInput arg@ArgInt{} = arg
mkInput arg@ArgFloat{} = arg
mkInput arg@ArgString{} = arg
mkInput arg@ArgChar{} = arg
mkInput (ArgUnneeded FlowOut ty) = ArgUnneeded FlowIn ty
mkInput arg@ArgUnneeded{} = arg


argExpandedPrim :: Prim -> BodyBuilder Prim
argExpandedPrim call@(PrimCall id pspec args) = do
    args' <- mapM expandArg args
    params <- lift $ primProtoParams <$> getProcPrimProto pspec
    unless (sameLength args' params) $
        shouldnt $ "arguments don't match params in call " ++ show call
    args'' <- zipWithM (transformUnneededArg $ zip params args) params args'
    return $ PrimCall id pspec args''
argExpandedPrim (PrimForeign lang nm flags args) = do
    args' <- mapM expandArg args
    return $ simplifyForeign lang nm flags args'
argExpandedPrim (PrimTest arg) = do
    arg' <- expandArg arg
    return $ PrimTest arg'


-- |Replace any arguments corresponding to unneeded parameters with
--  ArgUnneeded.  For unneeded *output* parameters, there must be an
--  input with the same name.  We must set the output argument variable
--  to the corresponding input argument, so the value is defined.
transformUnneededArg :: [(PrimParam,PrimArg)] -> PrimParam -> PrimArg
                     -> BodyBuilder PrimArg
transformUnneededArg pairs
    PrimParam{primParamInfo=ParamInfo{paramInfoUnneeded=True},
               primParamFlow=flow, primParamType=typ, primParamName=name}
    arg = do
        logBuild $ "Marking unneeded argument " ++ show arg
        when (flow == FlowOut) $ do
            case List.filter
                 (\(p,a)-> primParamName p == name && primParamFlow p == FlowIn)
                 pairs of
              []      -> shouldnt $ "No input param matching output "
                                    ++ show name
              [(_,a)] -> do
                logBuild $ "Adding move instruction for unneeded output "
                           ++ show arg
                instr' (PrimForeign "llvm" "move" [] [a, arg]) Nothing
              _       -> shouldnt $ "Multiple input params match output "
                                    ++ show name
        return $ ArgUnneeded flow typ
transformUnneededArg _ _ arg = return arg


-- |Construct a fake version of a Prim instruction containing only its
-- inputs, and with inessential parts canonicalised away.  Also return the
-- outputs of the instruction.
splitPrimOutputs :: Prim -> (Prim, [PrimArg])
splitPrimOutputs prim =
    let (inArgs,outArgs) = splitArgsByMode $ primArgs prim
    in  (replacePrimArgs prim $ canonicaliseArg <$> inArgs, outArgs)


-- |Returns a list of all output arguments of the input Prim
primOutputs :: Prim -> [PrimArg]
primOutputs prim =
    List.filter ((==FlowOut) . argFlowDirection) $ primArgs prim


-- |Add a binding for a variable. If that variable is an output for the
--  proc being defined, also add an explicit assignment to that variable.
addSubst :: PrimVarName -> PrimArg -> BodyBuilder ()
addSubst var val = do
    logBuild $ "      adding subst " ++ show var ++ " -> " ++ show val
    modify (\s -> s { currSubst = Map.insert var val $ currSubst s })
    subst <- gets currSubst
    logBuild $ "      new subst = " ++ show subst


-- |Record that the specified arg (which must be a variable) has been set.
recordVarSet :: PrimArg -> BodyBuilder ()
recordVarSet ArgVar{argVarName=nm, argVarFlow=FlowOut} =
    modify (\s -> s { blockDefs = Set.insert nm $ blockDefs s })
recordVarSet (ArgUnneeded FlowOut _) = return ()
recordVarSet arg =
    shouldnt $ "recordVarSet of non-output argument " ++ show arg

-- |Record all instructions equivalent to the input prim in the lookup table,
--  so if we later see an equivalent instruction we don't repeat it but
--  reuse the already-computed outputs.  This implements common subexpression
--  elimination.  It can also handle optimisations like recognizing the
--  reconstruction of a deconstructed value, and accounts for commutative
--  operations and inverse operations.
recordEntailedPrims :: Prim -> BodyBuilder ()
recordEntailedPrims prim = do
    let pair1 = splitPrimOutputs prim
    instrPairs <- (pair1:) <$> lift (instrConsequences prim)
    logBuild $ "Recording computed instrs"
               ++ List.concatMap
                  (\(p,o)-> "\n        " ++ show p ++ " -> " ++ show o)
                  instrPairs
    modify (\s -> s {subExprs = List.foldr (uncurry Map.insert) (subExprs s)
                                instrPairs})


-- |Return a list of instructions that have effectively already been
--  computed, mostly because they are inverses of instructions already
--  computed, or because of commutativity.
--  XXX Doesn't yet handle multiple modes for PrimCalls
instrConsequences :: Prim -> Compiler [(Prim,[PrimArg])]
instrConsequences prim =
   List.map (\(p,os) -> (canonicalisePrim p, os)) <$> instrConsequences' prim

instrConsequences' :: Prim -> Compiler [(Prim,[PrimArg])]
instrConsequences' (PrimForeign "lpvm" "cast" flags [a1,a2]) =
    return [(PrimForeign "lpvm" "cast" flags [a2], [a1])]
-- XXX this doesn't handle mutate to other fields leaving value unchanged
instrConsequences' (PrimForeign "lpvm" "mutate" [] [_,addr,offset,_,_,_,val]) =
    return [(PrimForeign "lpvm" "access" [] [addr,offset], [val])]
instrConsequences' (PrimForeign "llvm" "add" flags [a1,a2,a3]) =
    return [(PrimForeign "llvm" "sub" flags [a3,a2], [a1]),
            (PrimForeign "llvm" "sub" flags [a3,a1], [a2]),
            (PrimForeign "llvm" "add" flags [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "sub" flags [a1,a2,a3]) =
    return [(PrimForeign "llvm" "add" flags [a3,a2], [a1]),
            (PrimForeign "llvm" "add" flags [a2,a3], [a1]),
            (PrimForeign "llvm" "sub" flags [a1,a3], [a2])]
instrConsequences' (PrimForeign "llvm" "mul" flags [a1,a2,a3]) =
    return [(PrimForeign "llvm" "mul" flags [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "fadd" flags [a1,a2,a3]) =
    return [(PrimForeign "llvm" "fadd" flags [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "fmul" flags [a1,a2,a3]) =
    return [(PrimForeign "llvm" "fmul" flags [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "and" flags [a1,a2,a3]) =
    return [(PrimForeign "llvm" "and" flags [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "or" flags [a1,a2,a3]) =
    return [(PrimForeign "llvm" "or" flags [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["eq"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["eq"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["ne"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["ne"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["slt"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["sgt"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["sgt"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["slt"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["ult"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["ugt"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["ugt"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["ult"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["sle"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["sge"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["sge"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["sle"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["ule"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["uge"] [a2,a1], [a3])]
instrConsequences' (PrimForeign "llvm" "icmp" ["uge"] [a1,a2,a3]) =
    return [(PrimForeign "llvm" "icmp" ["ule"] [a2,a1], [a3])]
instrConsequences' _ = return []



-- |Unconditionally add an instr to the current body
rawInstr :: Prim -> OptPos -> BodyBuilder ()
rawInstr prim pos = do
    logBuild $ "---- adding instruction " ++ show prim
    validateInstr prim
    modify $ addInstrToState (maybePlace prim pos)



splitArgsByMode :: [PrimArg] -> ([PrimArg], [PrimArg])
splitArgsByMode = List.partition ((==FlowIn) . argFlowDirection)


canonicalisePrim :: Prim -> Prim
canonicalisePrim (PrimCall id nm args) =
    PrimCall id nm $ List.map (canonicaliseArg . mkInput) args
canonicalisePrim (PrimForeign lang op flags args) =
    PrimForeign lang op flags $ List.map (canonicaliseArg . mkInput) args
canonicalisePrim (PrimTest arg) =
    PrimTest $ (canonicaliseArg . mkInput) arg


-- |Standardise unimportant info in an arg, so that it is equal to any
--  other arg with the same content.
canonicaliseArg :: PrimArg -> PrimArg
canonicaliseArg ArgVar{argVarName=nm, argVarFlow=fl} =
    ArgVar nm AnyType False fl Ordinary False
canonicaliseArg (ArgInt v _)         = ArgInt v AnyType
canonicaliseArg (ArgFloat v _)       = ArgFloat v AnyType
canonicaliseArg (ArgString v _)      = ArgString v AnyType
canonicaliseArg (ArgChar v _)        = ArgChar v AnyType
canonicaliseArg (ArgUnneeded dir _)  = ArgUnneeded dir AnyType


validateInstr :: Prim -> BodyBuilder ()
validateInstr i@(PrimCall _ _ args)        = mapM_ (validateArg i) args
validateInstr i@(PrimForeign _ _ _ args) = mapM_ (validateArg i) args
validateInstr (PrimTest _)               = return ()


validateArg :: Prim -> PrimArg -> BodyBuilder ()
validateArg instr ArgVar{argVarType=ty} = validateType ty instr
validateArg instr (ArgInt    _ ty)    = validateType ty instr
validateArg instr (ArgFloat  _ ty)    = validateType ty instr
validateArg instr (ArgString _ ty)    = validateType ty instr
validateArg instr (ArgChar   _ ty)    = validateType ty instr
validateArg instr (ArgUnneeded _ ty)  = validateType ty instr


validateType :: TypeSpec -> Prim -> BodyBuilder ()
validateType InvalidType instr =
    shouldnt $ "InvalidType in argument of " ++ show instr
-- XXX AnyType is now a valid type treated as a word type
-- validateType AnyType instr =
--     shouldnt $ "AnyType in argument of " ++ show instr
validateType _ instr = return ()


addInstrToState :: Placed Prim -> BodyState -> BodyState
addInstrToState ins st@BodyState{buildState=Unforked} =
    st { currBuild = ins:currBuild st}
-- XXX merge these two equations
addInstrToState ins st@BodyState{buildState=bld@Forked{complete=False,
                                                       bodies=bods}} =
    st { buildState = bld {bodies=List.map (addInstrToState ins) bods} }
addInstrToState ins st@BodyState{buildState=bld@Forked{complete=True,
                                                       bodies=bods}} =
    st { buildState = bld {bodies=List.map (addInstrToState ins) bods} }


-- |Return the current ultimate value of the specified variable name and type
expandVar :: PrimVarName -> TypeSpec -> BodyBuilder PrimArg
expandVar var ty = expandArg $ ArgVar var ty False FlowIn Ordinary False


-- |Return the current ultimate value of the input argument.
expandArg :: PrimArg -> BodyBuilder PrimArg
expandArg arg@ArgVar{argVarName=var, argVarFlow=FlowIn} = do
    var' <- gets (Map.lookup var . currSubst)
    logBuild $ "Expanded " ++ show var ++ " to variable " ++ show var'
    maybe (return arg) expandArg var'
expandArg (ArgVar var typ coerce FlowOut ftype lst) = do
    var' <- gets (Map.findWithDefault var var . outSubst)
    return $ ArgVar var' typ coerce FlowOut ftype lst
expandArg arg = return arg



----------------------------------------------------------------
--                              Constant Folding
----------------------------------------------------------------

-- |Transform primitives with all inputs known into a move instruction by
--  performing the operation at compile-time.
simplifyForeign ::  String -> ProcName -> [Ident] -> [PrimArg] -> Prim
simplifyForeign "llvm" op flags args = simplifyOp op flags args
simplifyForeign lang op flags args = PrimForeign lang op flags args


-- | Simplify and canonicalise llvm instructions where possible. This
--   handles constant folding and simple (single-operation) algebraic
--   simplifications (left and right identities and annihilators).
--   Commutative ops are canonicalised by putting the smaller argument
--   first, but only for integer ops.  Integer inequalities are
--   canonicalised by putting smaller argument first and flipping
--   comparison if necessary.
simplifyOp :: ProcName -> [Ident] -> [PrimArg] -> Prim
-- Integer ops
simplifyOp "add" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (n1+n2) ty) output
simplifyOp "add" _ [ArgInt 0 ty, arg, output] =
  primMove arg output
simplifyOp "add" _ [arg, ArgInt 0 ty, output] =
  primMove arg output
simplifyOp "add" flags [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "add" flags [arg2, arg1, output]
simplifyOp "sub" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (n1-n2) ty) output
simplifyOp "sub" _ [arg, ArgInt 0 _, output] =
  primMove arg output
simplifyOp "mul" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (n1*n2) ty) output
simplifyOp "mul" _ [ArgInt 1 ty, arg, output] =
  primMove arg output
simplifyOp "mul" _ [arg, ArgInt 1 ty, output] =
  primMove arg output
simplifyOp "mul" _ [ArgInt 0 ty, _, output] =
  primMove (ArgInt 0 ty) output
simplifyOp "mul" _ [_, ArgInt 0 ty, output] =
  primMove (ArgInt 0 ty) output
simplifyOp "mul" flags [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "mul" flags [arg2, arg1, output]
simplifyOp "div" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (n1 `div` n2) ty) output
simplifyOp "div" _ [arg, ArgInt 1 _, output] =
  primMove arg output
-- Bitstring ops
simplifyOp "and" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (fromIntegral n1 .&. fromIntegral n2) ty) output
simplifyOp "and" _ [ArgInt 0 ty, _, output] =
  primMove (ArgInt 0 ty) output
simplifyOp "and" _ [_, ArgInt 0 ty, output] =
  primMove (ArgInt 0 ty) output
simplifyOp "and" _ [ArgInt (-1) _, arg, output] =
  primMove arg output
simplifyOp "and" _ [arg, ArgInt (-1) _, output] =
  primMove arg output
simplifyOp "and" flags [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "and" flags [arg2, arg1, output]
simplifyOp "or" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (fromIntegral n1 .|. fromIntegral n2) ty) output
simplifyOp "or" _ [ArgInt (-1) ty, _, output] =
  primMove (ArgInt (-1) ty) output
simplifyOp "or" _ [_, ArgInt (-1) ty, output] =
  primMove (ArgInt (-1) ty) output
simplifyOp "or" _ [ArgInt 0 _, arg, output] =
  primMove arg output
simplifyOp "or" _ [arg, ArgInt 0 _, output] =
  primMove arg output
simplifyOp "or" flags [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "or" flags [arg2, arg1, output]
simplifyOp "xor" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (fromIntegral n1 `xor` fromIntegral n2) ty) output
simplifyOp "xor" _ [ArgInt 0 _, arg, output] =
  primMove arg output
simplifyOp "xor" _ [arg, ArgInt 0 _, output] =
  primMove arg output
simplifyOp "xor" flags [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "xor" flags [arg2, arg1, output]
simplifyOp "shl" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (n1 `shiftL` fromIntegral n2) ty) output
simplifyOp "shl" _ [arg, ArgInt 0 _, output] =
  primMove arg output
simplifyOp "shl" _ [arg@(ArgInt 0 _), _, output] =
  primMove arg output
simplifyOp "ashr" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  primMove (ArgInt (n1 `shiftR` fromIntegral n2) ty) output
simplifyOp "ashr" _ [arg, ArgInt 0 _, output] =
  primMove arg output
-- XXX Need to convert both to unsigned before shifting
-- simplifyOp "lshr" _ [ArgInt n1 ty, ArgInt n2 _, output] =
--   primMove (ArgInt (n1 `shiftR` fromIntegral n2) ty) output
simplifyOp "lshr" _ [arg, ArgInt 0 _, output] =
  primMove arg output
-- Integer comparisons, including special handling of unsigned comparison to 0
simplifyOp "icmp" ["eq"] [ArgInt n1 _, ArgInt n2 _, output] =
  primMove (boolConstant $ n1==n2) output
simplifyOp "icmp" ["eq"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["eq"] [arg2, arg1, output]
simplifyOp "icmp" ["ne"] [ArgInt n1 _, ArgInt n2 _, output] =
  primMove (boolConstant $ n1/=n2) output
simplifyOp "icmp" ["ne"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["ne"] [arg2, arg1, output]
simplifyOp "icmp" ["slt"] [ArgInt n1 _, ArgInt n2 _, output] =
  primMove (boolConstant $ n1<n2) output
simplifyOp "icmp" ["slt"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["sgt"] [arg2, arg1, output]
simplifyOp "icmp" ["sle"] [ArgInt n1 _, ArgInt n2 _, output] =
  primMove (boolConstant $ n1<=n2) output
simplifyOp "icmp" ["sle"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["sge"] [arg2, arg1, output]
simplifyOp "icmp" ["sgt"] [ArgInt n1 _, ArgInt n2 _, output] =
  primMove (boolConstant $ n1>n2) output
simplifyOp "icmp" ["sgt"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["slt"] [arg2, arg1, output]
simplifyOp "icmp" ["sge"] [ArgInt n1 _, ArgInt n2 _, output] =
  primMove (boolConstant $ n1>=n2) output
simplifyOp "icmp" ["sge"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["sle"] [arg2, arg1, output]
simplifyOp "icmp" ["ult"] [ArgInt n1 _, ArgInt n2 _, output] =
  let n1' = fromIntegral n1 :: Word
      n2' = fromIntegral n2 :: Word
  in primMove (boolConstant $ n1'<n2') output
simplifyOp "icmp" ["ult"] [_, ArgInt 0 _, output] = -- nothing is < 0
  primMove (ArgInt 0 boolType) output
simplifyOp "icmp" ["ult"] [a1, ArgInt 1 ty, output] = -- only 0 is < 1
  PrimForeign "llvm" "icmp" ["eq"] [a1,ArgInt 0 ty,output]
simplifyOp "icmp" ["ult"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["ugt"] [arg2, arg1, output]
simplifyOp "icmp" ["ule"] [ArgInt n1 _, ArgInt n2 _, output] =
  let n1' = fromIntegral n1 :: Word
      n2' = fromIntegral n2 :: Word
  in primMove (boolConstant $ n1'<=n2') output
simplifyOp "icmp" ["ule"] [ArgInt 0 _, _, output] = -- 0 is <= everything
  primMove (ArgInt 1 boolType) output
simplifyOp "icmp" ["ule"] [ArgInt 1 ty, a2, output] = -- 1 is <= all but 0
  PrimForeign "llvm" "icmp" ["ne"] [ArgInt 0 ty,a2,output]
simplifyOp "icmp" ["ule"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["uge"] [arg2, arg1, output]
simplifyOp "icmp" ["ugt"] [ArgInt n1 _, ArgInt n2 _, output] =
  let n1' = fromIntegral n1 :: Word
      n2' = fromIntegral n2 :: Word
  in primMove (boolConstant $ n1'>n2') output
simplifyOp "icmp" ["ugt"] [ArgInt 0 _, _, output] = -- 0 is > nothing
  primMove (ArgInt 0 boolType) output
simplifyOp "icmp" ["ugt"] [ArgInt 1 ty, a2, output] = -- 1 is > only 0
  PrimForeign "llvm" "icmp" ["eq"] [ArgInt 0 ty,a2,output]
simplifyOp "icmp" ["ugt"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["ult"] [arg2, arg1, output]
simplifyOp "icmp" ["uge"] [ArgInt n1 _, ArgInt n2 _, output] =
  let n1' = fromIntegral n1 :: Word
      n2' = fromIntegral n2 :: Word
  in primMove (boolConstant $ n1'>=n2') output
simplifyOp "icmp" ["uge"] [_, ArgInt 0 _, output] = -- everything is >= 0
  primMove (ArgInt 1 boolType) output
simplifyOp "icmp" ["uge"] [a1, ArgInt 1 ty, output] = -- all but 0 is >= 1
  PrimForeign "llvm" "icmp" ["ne"] [a1,ArgInt 0 ty,output]
simplifyOp "icmp" ["uge"] [arg1, arg2, output]
    | arg2 < arg1 = PrimForeign "llvm" "icmp" ["ule"] [arg2, arg1, output]
-- Float ops
simplifyOp "fadd" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  primMove (ArgFloat (n1+n2) ty) output
simplifyOp "fadd" _ [ArgFloat 0 _, arg, output] =
  primMove arg output
simplifyOp "fadd" _ [arg, ArgFloat 0 _, output] =
  primMove arg output
simplifyOp "fsub" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  primMove (ArgFloat (n1-n2) ty) output
simplifyOp "fsub" _ [arg, ArgFloat 0 _, output] =
  primMove arg output
simplifyOp "fmul" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  primMove (ArgFloat (n1*n2) ty) output
simplifyOp "fmul" _ [arg, ArgFloat 1 _, output] =
  primMove arg output
simplifyOp "fmul" _ [ArgFloat 1 _, arg, output] =
  primMove arg output
-- We don't handle float * 0.0 because of the semantics of IEEE floating mult.
simplifyOp "fdiv" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  primMove (ArgFloat (n1/n2) ty) output
simplifyOp "fdiv" _ [arg, ArgFloat 1 _, output] =
  primMove arg output
-- Float comparisons
simplifyOp "fcmp" ["eq"] [ArgFloat n1 _, ArgFloat n2 _, output] =
  primMove (boolConstant $ n1==n2) output
simplifyOp "fcmp" ["ne"] [ArgFloat n1 _, ArgFloat n2 _, output] =
  primMove (boolConstant $ n1/=n2) output
simplifyOp "fcmp" ["slt"] [ArgFloat n1 _, ArgFloat n2 _, output] =
  primMove (boolConstant $ n1<n2) output
simplifyOp "fcmp" ["sle"] [ArgFloat n1 _, ArgFloat n2 _, output] =
  primMove (boolConstant $ n1<=n2) output
simplifyOp "fcmp" ["sgt"] [ArgFloat n1 _, ArgFloat n2 _, output] =
  primMove (boolConstant $ n1>n2) output
simplifyOp "fcmp" ["sge"] [ArgFloat n1 _, ArgFloat n2 _, output] =
  primMove (boolConstant $ n1>=n2) output
simplifyOp name flags args = PrimForeign "llvm" name flags args


boolConstant :: Bool -> PrimArg
boolConstant bool = ArgInt (fromIntegral $ fromEnum bool) boolType

----------------------------------------------------------------
--                  Reassembling the ProcBody
--
-- Once we've built up a BodyState, this code assembles it into a new ProcBody.
-- While we're at it, we also mark the last use of each variable, eliminate
-- calls that don't produce any output needed later in the body, and eliminate
-- any move instructions that moves a variable defined in the same block as the
-- move and not used after the move.  Most other move instructions were removed
-- while building BodyState, but that approach cannot eliminate moves to output
-- parameters.
----------------------------------------------------------------

currBody :: ProcBody -> BodyState -> Compiler (Int,Set PrimVarName,ProcBody)
currBody body st = do
    logMsg BodyBuilder $ "Now reconstructing body with usedLater = "
      ++ intercalate ", " (show <$> Map.keys (outSubst st))
    st' <- execStateT (rebuildBody st)
           $ BkwdBuilderState (Map.keysSet $ outSubst st) Nothing Map.empty
                              0 body
    logMsg BodyBuilder ">>>> Finished rebuilding a proc body"
    logMsg BodyBuilder "     Final state:"
    logMsg BodyBuilder $ showBlock 5 $ bkwdFollowing st'
    return (tmpCount st, bkwdUsedLater st', bkwdFollowing st')


type BkwdBuilder = StateT BkwdBuilderState Compiler

-- |BkwdBuilderState is used to store context info while building a ProcBody
-- backwards from a BodyState, itself the result of rebuilding a ProcBody
-- forwards.  Because construction runs backwards, the state mostly holds
-- information about the following code.
data BkwdBuilderState = BkwdBuilderState {
      bkwdUsedLater :: Set PrimVarName,  -- ^Variables used later in computation
      bkwdBranchesUsedLater :: Maybe [Set PrimVarName],
                                         -- ^The usedLater set for each
                                         -- following branch, used for fused
                                         -- branches.
      bkwdRenaming  :: VarSubstitution,  -- ^Variable substitution to apply
      bkwdTmpCount  :: Int,              -- ^Highest temporary variable number
      bkwdFollowing :: ProcBody          -- ^Code to come later
      } deriving (Eq,Show)



rebuildBody :: BodyState -> BkwdBuilder ()
rebuildBody st@BodyState{currBuild=prims, currSubst=subst, blockDefs=defs,
                         buildState=bldst, parent=par} = do
    usedLater <- gets bkwdUsedLater
    following <- gets bkwdFollowing
    logBkwd $ "Rebuilding body:" ++ fst (showState 8 st)
              ++ "\nwith currSubst = " ++ show subst
              ++ "\n     usedLater = " ++ show usedLater
    -- First see if we can prune away a later fork based on
    pruneBody subst
    case bldst of
      Unforked -> nop
      Forked{complete=False} ->
        shouldnt "Building proc body for bodystate with incomplete fork"
      Forked var ty fixedval fused bods True ->
        case fixedval of
          Just val ->
            rebuildBody $ selectElt val bods
          Nothing -> do
            -- XXX Perhaps we should generate a new proc for the parent par in
            -- cases where it's more than a few prims.  Currently UnBranch
            -- ensures that's not needed, but maybe it shouldn't.
            sts <- mapM (rebuildBranch subst) $ reverse bods
            usedLater' <- gets bkwdUsedLater
            let usedLaters = bkwdUsedLater <$> sts
            let usedLater'' = List.foldr Set.union usedLater' usedLaters
            let branchesUsedLater =
                  if fused
                  then Just usedLaters
                  else Nothing
            logBkwd $ "Switch on " ++ show var
                      ++ " with usedLater " ++ show usedLater''
            logBkwd $ "branchesUsedLater = "
                      ++ show branchesUsedLater
            let lastUse = Set.notMember var usedLater''
            let usedLater''' = Set.insert var usedLater''
            let tmp = maximum $ List.map bkwdTmpCount sts
            let followingBranches = List.map bkwdFollowing sts
            put $ BkwdBuilderState usedLater''' branchesUsedLater
                  Map.empty tmp
                  $ ProcBody [] $ PrimFork var ty lastUse followingBranches
    mapM_ (placedApply (bkwdBuildStmt defs)) prims
    finalUsedLater <- gets bkwdUsedLater
    logBkwd $ "Finished rebuild with usedLater = " ++ show finalUsedLater
    maybe nop rebuildBody par


-- |Select the element of bods specified by num
selectElt :: Integral a => a -> [b] -> b
selectElt num bods =
    if num' >= 0 && num' < length bods
    then bods !! num'
    else shouldnt $ "Out-of-bounds fixed value in fork " ++ show num'
  where num' = fromIntegral num


rebuildBranch :: Substitution -> BodyState -> BkwdBuilder BkwdBuilderState
rebuildBranch subst bod = do
    bkwdSt <- get
    lift $ execStateT (rebuildBody bod) bkwdSt


-- |Prune the specified ProcBody according to the variable bindings of
-- subst, eliminating any forks whose selection is forced by the bindings.
-- XXX This is weak.  First, it should prune forks recursively, and second,
-- the returned used var set should only include the bodies that are not
-- pruned.  But to do that, ProcBody needs to track used variables, or else
-- we have to recompute it from scratch.
pruneBody :: Substitution -> BkwdBuilder ()
pruneBody subst = do
    logBkwd "Trying to prune body"
    body <- gets bkwdFollowing
    case bodyFork body of
      PrimFork{forkVar=var, forkBodies=bods} ->
        case Map.lookup var subst of
          Just (ArgInt num _) -> do
            used0 <- gets bkwdUsedLater
            used <- maybe used0 (selectElt num) <$> gets bkwdBranchesUsedLater
            logBkwd $ "pruneBody successful:  selecting branch " ++ show num
            logBkwd $ "usedLater set to " ++ show used
            let prevBody = selectElt num bods
            let prims = bodyPrims body
            let newBody = prevBody { bodyPrims = prims ++ bodyPrims prevBody }
            modify $ \st -> st { bkwdUsedLater = used, bkwdFollowing = newBody }
          _ -> do
            logBkwd "Can't prune body"
            return ()
      _ -> do
        logBkwd "Can't prune body"
        return ()


bkwdBuildStmt :: Set PrimVarName -> Prim -> OptPos -> BkwdBuilder ()
bkwdBuildStmt defs prim pos = do
    usedLater <- gets bkwdUsedLater
    logBkwd $ "  Rebuilding prim:" ++ show prim
              ++ "\n    with usedLater = " ++ show usedLater
    let args = primArgs prim
    args' <- mapM renameArg args
    logBkwd $ "    renamed args = " ++ show args'
    case (prim,args') of
      (PrimForeign "llvm" "move" [] _, [ArgVar{argVarName=fromVar},
                                        ArgVar{argVarName=toVar}])
        | Set.notMember fromVar usedLater && Set.member fromVar defs ->
            modify (\s -> s { bkwdRenaming = Map.insert fromVar toVar
                                            $ bkwdRenaming s })
      _ -> do
        let (ins, outs) = splitArgsByMode $ List.filter argIsVar args'
        -- Filter out instructions that produce no needed outputs
        when (any (`Set.member` usedLater)
              $ argVarName <$> outs) $ do
          let prim' = replacePrimArgs prim $ markIfLastUse usedLater <$> args'
          logBkwd $ "    updated prim = " ++ show prim'
          let inVars = argVarName <$> ins
          let usedLater' = List.foldr Set.insert usedLater inVars
          st@BkwdBuilderState{bkwdFollowing=bd@ProcBody{bodyPrims=prims}} <- get
          put $ st { bkwdFollowing =
                       bd { bodyPrims = maybePlace prim' pos:prims },
                     bkwdUsedLater = usedLater' }


renameArg :: PrimArg -> BkwdBuilder PrimArg
renameArg arg@ArgVar{argVarName=name} = do
    name' <- gets (Map.findWithDefault name name . bkwdRenaming)
    return $ arg {argVarName=name'}
renameArg arg = return arg


markIfLastUse :: Set PrimVarName -> PrimArg -> PrimArg
markIfLastUse usedLater arg@ArgVar{argVarName=nm,argVarFlow=FlowIn} =
  arg {argVarFinal=Set.notMember nm usedLater}
markIfLastUse _ arg = arg


----------------------------------------------------------------
--                                  Logging
----------------------------------------------------------------

-- |Log a message, if we are logging body building activity.
logBuild :: String -> BodyBuilder ()
logBuild s = lift $ logMsg BodyBuilder s


-- |Log a message, if we are logging body building activity.
logBkwd :: String -> BkwdBuilder ()
logBkwd s = lift $ logMsg BodyBuilder s


-- | Log the current builder state
logState :: BodyBuilder ()
logState = do
    st <- get
    logBuild $ "     Current state:" ++ fst (showState 8 st)
    return ()


-- | Show the current builder state.  Since the builder builds upside down, we
-- start by showing the parent, then we show the current state.
showState :: Int -> BodyState -> (String,Int)
showState indent BodyState{parent=par, currBuild=revPrims, buildState=bld,
                           blockDefs=defed, forkConsts=consts} =
    let (str  ,indent')   = maybe ("",indent) (showState indent) par
        str'              = showPlacedPrims indent' (reverse revPrims)
        sets              = if List.null revPrims
                            then ""
                            else startLine indent
                                 ++ "# retargetable assignments: {"
                                 ++ intercalate ", " (List.map show $
                                                      Set.toList defed)
                                 ++ "}"
        suffix            = case bld of
                              Forked{} ->
                                startLine indent
                                ++ "Fusion consts: " ++ show consts
                              _ -> ""
        (str'',indent'') = showBuildState indent' bld
    in  (str ++ str' ++ sets ++ str'' ++ suffix, indent'')


-- | Show the current part of a build state.
showBuildState :: Int -> BuildState -> (String,Int)
showBuildState indent Unforked = ("", indent)
showBuildState indent (Forked var ty val fused bodies False) =
    let intro = showSwitch indent var ty val fused
        content = showBranches indent 0 True $ reverse bodies
        indent' = indent + 4
    in  (intro++content,indent')
showBuildState indent (Forked var ty val fused bodies True) =
    let intro = showSwitch indent var ty val fused
        content = showBranches indent 0 False $ reverse bodies
    in  (intro++content,indent)


-- | Show a list of branches of a build state.
showBranches :: Int -> Int -> Bool -> [BodyState] -> String
showBranches indent bodyNum True [] = showCase indent bodyNum
showBranches indent bodyNum False [] = ""
showBranches indent bodyNum open (body:bodies) =
    showCase indent bodyNum
    ++ fst (showState (indent+4) body)
    ++ showBranches indent (bodyNum+1) open bodies


-- | Show a single branch of a build state
showCase indent bodyNum = startLine indent ++ show bodyNum ++ "::"


-- | Show the fork part of a build state
showSwitch indent var ty val fused =
    startLine indent ++ "case " ++ show var ++ ":" ++ show ty
    ++ (if fused then " (fused)" else " (not fused)")
    ++ maybe "" (\v-> " (=" ++ show v ++ ")") val
    ++ " of"


-- | Start a new line with the specified indent.
startLine :: Int -> String
startLine tab = '\n' : replicate tab ' '
