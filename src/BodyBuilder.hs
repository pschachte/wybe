--  File     : BodyBuilder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri 22 May 2015 10:59:56 AEST
--  Purpose  : A monad to build up a procedure Body, with copy propagation
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--

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
import Data.Maybe
import Data.Bits
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
data BodyState
    = Unforked {
      currBuild   :: [Placed Prim],   -- ^The body we're building, reversed
      currSubst   :: Substitution,    -- ^variable substitutions to propagate
      outSubst    :: VarSubstitution, -- ^Substitutions for var assignments
      subExprs    :: ComputedCalls,   -- ^Previously computed calls to reuse
      definers    :: VarDefiner,      -- ^The call that defined each var
      failed      :: Bool,            -- ^True if this body always fails
      predecessor :: Maybe BodyState, -- ^The preceding Forked body state
      uParent     :: Maybe BodyState, -- ^The Forked of which this is a part
      uTmpCnt     :: Int              -- ^The next temp variable number to use
      }
    | Forked {
      origin      :: BodyState,       -- ^The Unforked state before the fork
      stForkVar   :: PrimVarName,     -- ^Variable that selects branch to take
      stKnownVal  :: Maybe Integer,   -- ^Definite value of stForkVar if known
      stForkVarTy :: TypeSpec,        -- ^Type of stForkVar
      stForkBods  :: [BodyState]      -- ^BodyStates of all branches so far
      }
    deriving (Eq,Show)


logState :: BodyBuilder ()
logState = do
    st <- get
    logBuild $ "     Current state:" ++ fst (showState 8 st)


predSep = "\n    ---- ^ Predecessor ^ ----"

mapFst :: (a->b) -> (a,c) -> (b,c)
mapFst f (x,y) = (f x,y)


showState :: Int -> BodyState -> (String,Int)
showState indent Unforked{predecessor=pred, uParent=par, currBuild=revPrims} =
    let (str',indent')   = maybe ("",indent) (showState indent) par
        (str'',_)        = maybe ("",indent)
                                 (mapFst (++predSep) . showState indent') pred
    in  (str' ++ str'' ++ showPlacedPrims indent' (reverse revPrims), indent')
showState indent Forked{origin=orig, stForkVar=var, stForkVarTy=ty,
                        stKnownVal=val, stForkBods=bods} =
    let (str',indent')   = showState indent orig
        (str'',indent'') = showBranches indent' 0 $ reverse bods
    in  (str' ++ "\n"
         ++ replicate indent' ' ' ++ "case " ++ show var ++ ":" ++ show ty
         ++ maybe "" (\v-> " (=" ++ show v ++ ")") val
         ++ " of"
         ++ str''
        , indent''
        )


showBranches :: Int -> Int -> [BodyState] -> (String,Int)
showBranches indent bodyNum [] = (showCase indent bodyNum, indent)
showBranches indent bodyNum (body:bodies) =
    let (str',indent') = showState (indent+4) body
        (str'',indent'') = showBranches indent (bodyNum+1) bodies
    in  (showCase indent bodyNum ++ str' ++ str''
        , indent')


showCase indent bodyNum = "\n" ++ replicate indent ' ' ++ show bodyNum ++ "::"


type Substitution = Map PrimVarName PrimArg
type VarSubstitution = Map PrimVarName PrimVarName


-- To handle common subexpression elimination, we keep a map from previous
-- calls with their outputs removed to the outputs.  This type encapsulates
-- that.  In the Prim keys, all PrimArgs are inputs.
type ComputedCalls = Map Prim [PrimArg]


-- To handle branch conditions, we keep track of the statement that bound
-- each variable.  For each arm of a branch, this lets us work out what
-- must be true and what must be false for that arm, so we can avoid
-- redundant tests.
type VarDefiner = Map PrimVarName Prim


-- |Get the current temp variable count
tmpCount :: BodyState -> Int
tmpCount Unforked{uTmpCnt=tmp}   = tmp
tmpCount Forked{stForkBods=bods} = maximum $ tmpCount <$> bods


-- |Get the current temp variable count
setTmpCount :: Int -> BodyState -> BodyState
setTmpCount tmp st@Unforked{} = st {uTmpCnt=tmp}
setTmpCount tmp st@Forked{stForkBods=bods} =
    st {stForkBods = setTmpCount tmp <$> bods}


-- |Allocate the next temp variable name and ensure it's not allocated again
freshVarName :: BodyBuilder PrimVarName
freshVarName = do
    tmp <- gets tmpCount
    modify $ setTmpCount (tmp+1)
    return $ PrimVarName (mkTempName tmp) 0


-- |Extract a ProcBody from a BodyState.
-- XXX This seems to miss the unforked part besides at the top level
currBody :: BodyState -> Compiler (Int,ProcBody)
currBody st@Unforked{uParent=Just _} =
    shouldnt $ "currBody of non-root unforked state " ++ show st
currBody st@Unforked{currBuild=[], predecessor=Just pred} =
    currBody pred
currBody st@Unforked{predecessor=Just _} =
    shouldnt $ "Non-empty body after a fork" ++ show st
currBody Unforked{currBuild=prims, uTmpCnt=tmp, predecessor=Nothing} = do
    let result = ProcBody (reverse prims) NoFork
    logMsg BodyBuilder $ "Unforked result = "
                         ++ showPlacedPrims 4 (bodyPrims result)
    return (tmp,result)
currBody st@(Forked Unforked{currBuild=prims} var (Just val) ty bods) =
    case maybeNth val $ reverse bods of
        Nothing -> do
          message Error
            ("Completing forked body with out-of-range decision value "
             ++ show val) Nothing
          return (tmpCount st,ProcBody (reverse prims) NoFork)
        Just bod -> do
          logMsg BodyBuilder
                 $ "Completing forked body with decision value " ++ show val
          (ProcBody prims' fork) <- snd <$> currBody bod
          logMsg BodyBuilder "Completing forked body with known decision var"
          let result = ProcBody (reverse prims ++ prims') fork
          logMsg BodyBuilder $ "Predetermined forked result = " ++ show result
          return (tmpCount st,result)
currBody st@(Forked Unforked{currBuild=prims} var val ty bods) = do
    logMsg BodyBuilder "Completing forked body with unforked origin"
    bods' <- reverse . (snd <$>) <$> mapM currBody bods
    let result = ProcBody (reverse prims) $ PrimFork var ty False bods'
    logMsg BodyBuilder $ "Forked result = " ++ show result
    return (tmpCount st,result)
currBody body@(Forked Forked{} var val ty bods) =
    shouldnt $ "currBody of Forked Forked state " ++ show body


initState :: Int -> VarSubstitution -> BodyState
initState tmp oSubst =
    Unforked [] Map.empty oSubst Map.empty Map.empty False Nothing Nothing tmp


----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body
buildBody :: Int -> VarSubstitution -> BodyBuilder a -> Compiler (Int,ProcBody)
buildBody tmp oSubst builder = do
    logMsg BodyBuilder "<<<< Beginning to build a proc body"
    (a,st) <- buildPrims (initState tmp oSubst) builder
    logMsg BodyBuilder ">>>> Finished building a proc body"
    logMsg BodyBuilder "     Current state:"
    logMsg BodyBuilder $ fst $ showState 8 st
    (tmp,body) <- currBody st
    return (tmp,body)


-- |Start a new fork on var of type ty
buildFork :: PrimVarName -> TypeSpec -> BodyBuilder ()
buildFork var ty = do
    st <- get
    var' <- expandVar var boolType
    logBuild $ "<<<< beginning to build a new fork on " ++ show var
               ++ " (-> " ++ show var' ++ ")"
    case st of
      Forked{} ->
        shouldnt "Building a fork outside of a body or branch"
      -- Unforked{failed=True} ->
      --   -- XXX not right: need to balance building/completing this fork
      --   logBuild "Beginning fork after failed body"
      Unforked{} -> do
        arg' <- expandVar var ty
        logBuild $ "     (expands to " ++ show arg' ++ ")"
        let (fvar,fval) =
              case arg' of
                  ArgInt n _ -> -- result known at compile-time
                    (var,Just n)
                  ArgVar var' varType _ _ _ -> -- statically unknown result
                    (var',Nothing)
                  _ -> shouldnt "switch on non-integer variable"
        put $ Forked st fvar fval ty []
        logState


-- |Complete a fork previously initiated by buildFork.
completeFork :: BodyBuilder ()
completeFork = do
    st <- get
    case st of
      -- Unforked{failed=True} ->
      --   logBuild "Completing fork after failed body"
      Unforked{} -> shouldnt "Completing an unbegun fork"
      -- Forked{stKnownVal=Just n, stForkBods=bods} -> do
      --   logBuild $ ">>>> ending fork on value " ++ show n
      --   let selectedBranch = reverse bods !! fromIntegral n
      --   logBuild $ ">>> leaving state: " ++ show selectedBranch
      --   put selectedBranch
      Forked{origin=Forked{}} -> shouldnt "Complete an unbuilt fork"
      Forked{origin=Unforked{currSubst=subst, outSubst=osubst, subExprs=se,
                             definers=defs},
             stForkBods=bods, stForkVar=var} -> do
        logBuild $ ">>>> ending fork on " ++ show var
        -- Prepare for any instructions coming after the fork
        put $ Unforked [] subst osubst se defs False (Just st) Nothing
                       $ maximum $ tmpCount <$> bods
        logState


-- |Start a new branch for the next integer value of the switch variable.
beginBranch :: BodyBuilder ()
beginBranch = do
    st <- get
    let branchNum = fromIntegral $ length $ stForkBods st
    logBuild $ "<<<< <<<< Beginning to build branch "
               ++ show branchNum ++ " on " ++ show (stForkVar st)
    case st of
        -- Unforked{failed=True} ->
        --   logBuild "Beginning branch after failed body"
        Unforked{} ->
          shouldnt "beginBranch in Unforked state"
        Forked{origin=Unforked _ subst vsubst subexp defs failed _ _ tmp,
               stForkVar=var, stKnownVal=val} -> do
          -- consider the branch failed if we know the switch variable, and
          -- this is the wrong branch.  This avoids generating unneeded code.
          let failed' = failed || maybe False (/=branchNum) val
          put $ Unforked [] subst vsubst subexp defs failed'
                    Nothing (Just st) tmp
          -- note the value of the fork variable for this branch if unknown
          -- XXX also add consequences of this, eg if var is result of X==Y
          --     comparison and var == 1, then record that X==Y.
          when (isNothing val) $ addSubst var $ ArgInt branchNum intType
          logState
          return ()
        Forked{origin=Forked{}} ->
          shouldnt "Beginning a branch outside of a fork"


-- |End the current branch.
endBranch :: BodyBuilder ()
endBranch = do
    (maybeParent,st) <- gets popParent
    case maybeParent of
        Nothing -> 
          shouldnt "endBranch with no parent state"
        Just parent@Forked{} -> do
          logBuild $ ">>>> >>>> Ending branch "
              ++ show (length $ stForkBods parent)
              ++ " on " ++ show (stForkVar parent)
          put $ parent { stForkBods = st:stForkBods parent }
          logState
        -- Just Unforked{failed=True} ->
        --   logBuild "Ending branch after failed body"
        --   -- leave state as is
        Just Unforked{} ->
          shouldnt "endBranch with unforked parent"



-- |Return the parent of a state and remove it from the state
popParent :: BodyState -> (Maybe BodyState,BodyState)
-- popParent st@Unforked{failed=True,uParent=Nothing} = (Just st, st)
popParent st@Unforked{predecessor=Just pred} =
    let (par,_) = popParent pred
    in  (par,st)
popParent st@Unforked{uParent=parent} = (parent, st {uParent=Nothing})
popParent st@Forked{origin=orig}      = popParent orig


-- |Return Just the known value of the specified variable, or Nothing
definiteVariableValue :: PrimVarName -> BodyBuilder (Maybe PrimArg)
definiteVariableValue var = do
    arg <- expandVar var AnyType
    case arg of
        ArgVar{} -> return Nothing -- variable (unknown) result
        _ -> return $ Just arg

buildPrims :: BodyState -> BodyBuilder a -> Compiler (a,BodyState)
buildPrims st builder = runStateT builder st


-- |Augment st with whatever consequences can be deduced from the fact
--  that prim assigned var the value val.
--  
propagateBinding :: PrimVarName -> TypeSpec -> Int -> Prim -> BodyBuilder ()
propagateBinding var ty val (PrimForeign "llvm" "icmp" [cmp] [a1, a2, _]) = do
    propagateComparison var ty val cmp a1 a2
propagateBinding _ _ _ _ = return ()


-- |Augment st with whatever consequences can be deduced from the fact
--  that the specified LLVM comparison assigned var the value val.
propagateComparison :: PrimVarName -> TypeSpec -> Int -> String
                    -> PrimArg -> PrimArg -> BodyBuilder ()
propagateComparison var ty val cmp a1 a2 = do
    -- note that the negation of the test gives the negation of the result
    let (oppositeCmp,trues0,falses0) = comparisonRelatives cmp
    let (_,trues,falses) = if val == 0
                           then comparisonRelatives oppositeCmp
                           else ("", trues0, falses0)
    let allConsequences = (oppositeCmp,1-val)
                          :  zip trues (repeat 1)
                          ++ zip falses (repeat 0)
    logBuild $ "Adding consequences of branch:  "
               ++ show (List.map (\(c,v) ->
                                  PrimForeign "llvm" "icmp" [c]
                                  [a1, a2, ArgInt (fromIntegral v) ty])
                        allConsequences)
    let insertInstr (c,v)
            = Map.insert
              (PrimForeign "llvm" "icmp" [c] [canonicaliseArg a1,
                                              canonicaliseArg a2])
              [ArgInt (fromIntegral v) ty]
    modify (\s -> s {subExprs = List.foldr insertInstr (subExprs s)
                                allConsequences
                    })
    mp <- gets subExprs
    logBuild $ "After adding consequences, subExprs = " ++ show mp


-- |Given an LLVM comparison instruction name, returns a triple of
--  (1) the negation of the comparison
--  (2) a list of comparisons that are true whenever it is true
--  (3) a list of comparisons that are false whenever it is true, other than
--      the negation (1)
comparisonRelatives :: String -> (String,[String],[String])
comparisonRelatives "eq"  = ("ne", ["sle", "sge", "ule", "uge"],
                          ["slt", "sgt", "ult", "ugt"])
comparisonRelatives "ne"  = ("eq", [], [])
comparisonRelatives "slt" = ("sge", ["sle", "ne"], [])
comparisonRelatives "sge" = ("slt", [], [])
comparisonRelatives "sgt" = ("sle", ["sge", "ne"], [])
comparisonRelatives "sle" = ("sgt", [], [])
comparisonRelatives "ult" = ("uge", ["ule", "ne"], [])
comparisonRelatives "uge" = ("ult", [], [])
comparisonRelatives "ugt" = ("ule", ["uge", "ne"], [])
comparisonRelatives "ule" = ("ugt", [], [])
comparisonRelatives comp = shouldnt $ "unknown llvm comparison " ++ comp



-- |Add an instruction to the current body, after applying the current
--  substitution. If it's a move instruction, add it to the current
--  substitution.
instr :: Prim -> OptPos -> BodyBuilder ()
instr prim pos = do
    st <- get
    case st of
      Unforked{failed=True}  -> do -- ignore if we've already failed
        logBuild $ "  Failing branch:  ignoring instruction " ++ show prim
        return ()
      Unforked{failed=False} -> do
        prim' <- argExpandedPrim prim
        logBuild $ "Generating instr " ++ show prim ++ " -> " ++ show prim'
        instr' prim' pos
      Forked{} ->
        shouldnt "instr in Forked context"


instr' :: Prim -> OptPos -> BodyBuilder ()
instr' prim@(PrimForeign "llvm" "move" []
           [val, argvar@(ArgVar var _ flow _ _)]) pos
  = do
    logBuild $ "  Expanding move(" ++ show val ++ ", " ++ show argvar ++ ")"
    unless (flow == FlowOut && argFlowDirection val == FlowIn) $ 
      shouldnt "move instruction with wrong flow"
    outVar <- gets (Map.findWithDefault var var . outSubst)
    addSubst outVar val
    rawInstr prim pos
-- XXX this is a bit of a hack to work around not threading a heap
--     through the code, which causes the compiler to try to reuse
--     the results of calls to alloc.  Since the mutate primitives
--     already have an output value, that should stop us from trying
--     to reuse modified structures or the results of calls to
--     access after a structure is modified, so alloc should be
--     the only problem that needs fixing.  We don't want to fix this
--     by threading a heap through, because it's fine to reorder calls
--     to alloc.
instr' prim@(PrimForeign "lpvm" "alloc" [] args) pos = do
    logBuild $ "  Leaving alloc alone"
    rawInstr prim pos
instr' prim@(PrimTest (ArgInt 0 _)) pos = do
    rawInstr prim pos
    logBuild $ "  Found fail instruction; noting failing branch"
    -- note guaranteed failure
    modify (\s -> s { failed=True })
instr' prim pos = do
    let (prim',newOuts) = splitPrimOutputs prim
    logBuild $ "Looking for computed instr " ++ show prim' ++ " ..."
    currSubExprs <- gets subExprs
    logBuild $ "  with subExprs = " ++ show currSubExprs
    match <- gets (Map.lookup prim' . subExprs)
    case match of
        Nothing -> do
            -- record prim executed (and other modes), and generate instr
            logBuild "not found"
            addAllModes prim
            rawInstr prim pos
        Just oldOuts -> do
            -- common subexpr: just need to record substitutions
            logBuild $ "found it; substituting "
                       ++ show oldOuts ++ " for " ++ show newOuts
            mapM_ (\(newOut,oldOut) -> addSubst (outArgVar newOut)
                                       (outVarIn oldOut))
                  $ zip newOuts oldOuts


outVarIn :: PrimArg -> PrimArg
outVarIn (ArgVar name ty FlowOut ftype lst) =
    ArgVar name ty FlowIn Ordinary False
outVarIn arg@ArgInt{} = arg
outVarIn arg@ArgFloat{} = arg
outVarIn arg@ArgString{} = arg
outVarIn arg@ArgChar{} = arg
outVarIn arg = shouldnt $ "outVarIn not actually out: " ++ show arg


argExpandedPrim :: Prim -> BodyBuilder Prim
argExpandedPrim (PrimCall pspec args) = do
    args' <- mapM expandArg args
    return $ PrimCall pspec args'
argExpandedPrim (PrimForeign lang nm flags args) = do
    args' <- mapM expandArg args
    return $ simplifyForeign lang nm flags args'
argExpandedPrim (PrimTest arg) = do
    arg' <- expandArg arg
    return $ PrimTest arg'

splitPrimOutputs :: Prim -> (Prim, [PrimArg])
splitPrimOutputs (PrimCall pspec args) =
    let (inArgs,outArgs) = splitArgsByMode args
    in (PrimCall pspec inArgs, outArgs)
splitPrimOutputs (PrimForeign lang nm flags args) = 
    let (inArgs,outArgs) = splitArgsByMode args
    in (PrimForeign lang nm flags inArgs, outArgs)
splitPrimOutputs tst@(PrimTest arg) = (tst, [])


-- |Add a binding for a variable. If that variable is an output for the
--  proc being defined, also add an explicit assignment to that variable.
addSubst :: PrimVarName -> PrimArg -> BodyBuilder ()
addSubst var val = do
    logBuild $ "      adding subst " ++ show var ++ " -> " ++ show val
    modify (\s -> s { currSubst = Map.insert var val $ currSubst s })
    subst <- gets currSubst
    logBuild $ "      new subst = " ++ show subst


-- |Add all instructions equivalent to the input prim to the lookup table,
--  so if we later see an equivalent instruction we don't repeat it but
--  reuse the already-computed outputs.  This implements common subexpression
--  elimination.  It can also handle optimisations like recognizing the
--  reconstruction of a deconstructed value.
--  XXX Doesn't yet handle multiple modes.
addAllModes :: Prim -> BodyBuilder ()
addAllModes instr@(PrimCall pspec args) = do
    let (inArgs,outArgs) = splitArgsByMode args
    let fakeInstr = PrimCall pspec inArgs
    logBuild $ "Recording computed instr " ++ show fakeInstr
    modify (\s -> s {subExprs = Map.insert fakeInstr outArgs $ subExprs s,
                     definers = List.foldr
                                (flip Map.insert instr . argVarName)
                                (definers s) outArgs})
addAllModes instr@(PrimForeign lang nm flags args)  = do
    let (inArgs,outArgs) = splitArgsByMode args
    let fakeInstr = PrimForeign lang nm flags inArgs
    logBuild $ "Recording computed instr " ++ show fakeInstr
    modify (\s -> s {subExprs = Map.insert fakeInstr outArgs $ subExprs s,
                     definers = List.foldr
                                (flip Map.insert instr . argVarName)
                                (definers s)
                                outArgs})
addAllModes _ = return () -- No other instrs equivalent to a PrimTest





-- |Unconditionally add an instr to the current body
rawInstr :: Prim -> OptPos -> BodyBuilder ()
rawInstr prim pos = do
    logBuild $ "---- adding instruction " ++ show prim
    validateInstr prim
    modify $ addInstrToState (maybePlace prim pos)


splitArgsByMode :: [PrimArg] -> ([PrimArg], [PrimArg])
splitArgsByMode args =
    let (ins,outs) = List.partition ((==FlowIn) . argFlowDirection) args
    in  (List.map canonicaliseArg ins, outs)


-- |Standardise unimportant info in an arg, so that it is equal to any
--  other arg with the same content.
canonicaliseArg :: PrimArg -> PrimArg      
canonicaliseArg (ArgVar nm _ fl _ _) = ArgVar nm AnyType fl Ordinary False
canonicaliseArg (ArgInt v _)         = ArgInt v AnyType
canonicaliseArg (ArgFloat v _)       = ArgFloat v AnyType
canonicaliseArg (ArgString v _)      = ArgString v AnyType
canonicaliseArg (ArgChar v _)        = ArgChar v AnyType


validateInstr :: Prim -> BodyBuilder ()
validateInstr i@(PrimCall _ args) =        mapM_ (validateArg i) args
validateInstr i@(PrimForeign _ _ _ args) = mapM_ (validateArg i) args
validateInstr (PrimTest _) = return ()

validateArg :: Prim -> PrimArg -> BodyBuilder ()
validateArg instr (ArgVar _ ty _ _ _) = validateType ty instr
validateArg instr (ArgInt    _ ty)    = validateType ty instr
validateArg instr (ArgFloat  _ ty)    = validateType ty instr
validateArg instr (ArgString _ ty)    = validateType ty instr
validateArg instr (ArgChar   _ ty)    = validateType ty instr

validateType :: TypeSpec -> Prim -> BodyBuilder ()
validateType InvalidType instr =
    shouldnt $ "InvalidType in argument of " ++ show instr
-- XXX AnyType is now a valid type treated as a word type
-- validateType AnyType instr =
--     shouldnt $ "AnyType in argument of " ++ show instr
validateType _ instr = return ()


addInstrToState :: Placed Prim -> BodyState -> BodyState
addInstrToState ins st@Unforked{} = st { currBuild = ins:currBuild st}
addInstrToState ins st@Forked{}
    = st { stForkBods = List.map (addInstrToState ins) $ stForkBods st }


-- |Return the current state if it's Unforked, or its origin if it's Forked
leadingUnbranchedOp :: (BodyState -> a) -> BodyBuilder a
leadingUnbranchedOp fn = do
    st <- get
    case st of
      Unforked{}         -> return $ fn st
      Forked{origin=st'} -> return $ fn st'


-- |Return the current ultimate value of the specified variable name and type
expandVar :: PrimVarName -> TypeSpec -> BodyBuilder PrimArg
expandVar var ty = expandArg $ ArgVar var ty FlowIn Ordinary False


-- |Return the current ultimate value of the input argument.
expandArg :: PrimArg -> BodyBuilder PrimArg
expandArg arg@(ArgVar var _ FlowIn _ _) = do
    var' <- leadingUnbranchedOp (Map.lookup var . currSubst)
    logBuild $ "Expanded " ++ show var ++ " to variable " ++ show var'
    maybe (return arg) expandArg var'
expandArg (ArgVar var typ FlowOut ftype lst) = do
    var' <- leadingUnbranchedOp (Map.findWithDefault var var . outSubst)
    return $ ArgVar var' typ FlowOut ftype lst
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
-- XXX should probably put shift ops here, too
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
--                                  Logging
----------------------------------------------------------------

-- |Log a message, if we are logging body building activity.
logBuild :: String -> BodyBuilder ()
logBuild s = lift $ logMsg BodyBuilder s
