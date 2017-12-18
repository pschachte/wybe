--  File     : BodyBuilder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri 22 May 2015 10:59:56 AEST
--  Purpose  : A monad to build up a procedure Body, with copy propagation
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--

module BodyBuilder (
  BodyBuilder, buildBody, instr, buildFork, completeFork,
  beginBranch, endBranch
  ) where

import AST
import Snippets
import Util
import Options (LogSelection(BodyBuilder))
import Data.Map as Map
import Data.List as List
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
-- instr adds a single instruction to the procBody that will be produced.
-- Forks are produced by the following functions:
--    buildFork     initiates a fork on a specified variable
--    beginBranch   starts a new branch of the current fork
--    endBranch     ends the current branch
--    completeFork  completes the current fork
--
-- No instructions can be added between buildFork and beginBranch, or
-- between endBranch and beginBranch. A new fork can be built within a
-- branch, but must be completed before the branch is ended.
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
-- particular, we keep track of variable renaming needed to keep inlining
-- hygenic. To do this, we rename all the input parameters of the proc to
-- be inlined, and when expanding the body, we rename any variables when
-- first assigned. The exception to this is the proc's output parameters.
-- These are kept as a set. We also maintain a counter for temporary
-- variable names.
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
-- the fork structure of which it's a part. When constructing a new fork, we
-- transform the existing Unforked state into a Forked state.  When beginning
-- a new branch, we make an empty Unforked state with the existing Forked
-- state as its parent.  When ending a branch, we transfer the current state
-- into the parent's list of branch bodies and promote the parent.
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
      uParent     :: Maybe BodyState, -- ^The Forked of which this is a part
      uPred       :: Maybe BodyState  -- ^The BodyState before the current one
      }
    | Forked {
      origin      :: BodyState,       -- ^The Unforked state before the fork
      stForkVar   :: PrimVarName,     -- ^Variable that selects branch to take
      stKnownVal  :: Maybe Integer,   -- ^Definite value of stForkVar if known
      stForkVarTy :: TypeSpec,        -- ^Type of stForkVar
      stForkBods  :: [BodyState],     -- ^BodyStates of all branches so far
      fParent     :: Maybe BodyState  -- ^The Forked of which this is a part
      }
    deriving (Eq,Show)


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


-- |Extract a ProcBody from a BodyState.
-- XXX This must be prepared to generate multiple auxilliary procs.
currBody :: BodyState -> Compiler ProcBody
currBody Unforked{currBuild=prims, uPred=Nothing} = do
    logMsg BodyBuilder "Completing unforked body with no predecessor"
    return $ ProcBody (reverse prims) NoFork
currBody Unforked{currBuild=prims, uPred=Just pred} = do
    logMsg BodyBuilder "Completing unforked body with predecessor"
    pred' <- addInstrs pred prims
    (ProcBody prims' fork) <- currBody pred'
    return $ ProcBody (reverse prims ++ prims') fork
currBody (Forked unforked@Unforked{currBuild=prims} var (Just val) ty bods _) =
    case maybeNth val $ reverse bods of
        Nothing -> do
          logMsg BodyBuilder "Completing forked body with unknown decision var"
          currBody unforked
        Just bod -> do
          logMsg BodyBuilder "Completing forked body with known decision var"
          (ProcBody prims' fork) <- currBody bod
          return $ ProcBody (reverse prims ++ prims') fork
currBody (Forked Unforked{currBuild=prims} var val ty bods _) = do
    logMsg BodyBuilder "Completing forked body with unforked origin"
    bods' <- reverse <$> mapM currBody bods
    return $ ProcBody (reverse prims) $
             PrimFork var ty False bods'

-- Add a list of instrs at the end of a BodyState.  Since the instrs are
-- stored in reverse order, that means adding them at the front.
-- XXX If suffix is more than a few instructions and the state is forked,
--     this should generate a fresh proc and add a call to it as the suffix.
addInstrs :: BodyState -> [Placed Prim] -> Compiler BodyState
addInstrs st@Unforked{currBuild=prims} suffix =
    return $ st {currBuild=suffix ++ prims}
addInstrs st@Forked{stForkBods=bods} suffix = do
    bods' <- mapM (flip addInstrs suffix) bods
    return $ st {stForkBods=bods'}


initState :: VarSubstitution -> BodyState
initState oSubst =
    Unforked [] Map.empty oSubst Map.empty Map.empty Nothing Nothing


----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body
buildBody :: VarSubstitution -> BodyBuilder a -> Compiler (a,ProcBody)
buildBody oSubst builder = do
    logMsg BodyBuilder "<<<< Beginning to build a proc body"
    (a,st) <- buildPrims (initState oSubst) builder
    logMsg BodyBuilder ">>>> Finished  building a proc body:"
    body <- currBody st
    logMsg BodyBuilder $ showBlock 4 body
    return (a,body)


-- |Start a new fork on var of type ty
buildFork :: PrimVarName -> TypeSpec -> BodyBuilder ()
buildFork var ty = do
    st <- get
    logBuild $ "<<<< beginning to build a new fork on " ++ show var
    case st of
      Forked{} -> do
        shouldnt "Building a fork outside of a body or branch"
      Unforked{} -> do
        arg' <- expandArg $ ArgVar var ty FlowIn Ordinary False
        logBuild $ "     (expands to " ++ show arg' ++ ")"
        let (fvar,fval) =
              case arg' of
                  ArgInt n _ -> -- result known at compile-time
                    (var,Just n)
                  ArgVar var' varType _ _ _ -> do -- statically unknown result
                    (var',Nothing)
                  _ -> shouldnt "switch on non-integer variable"
        logBuild $ "     ( actually " ++ show fvar ++
            (maybe "" (\v -> " = " ++ show v) fval) ++ ")"
        put $ Forked st fvar fval ty [] (uParent st)


-- |Complete a fork previously initiated by buildFork.
completeFork :: BodyBuilder ()
completeFork = do
    st <- get
    case st of
      Unforked{} -> do
        shouldnt "Completing an unbegun fork"
      Forked{origin=Unforked{currSubst=subst, outSubst=osubst, subExprs=subes,
                             definers=defs, uParent=upar}} -> do
        logBuild $ ">>>> ending fork on " ++ show (stForkVar st)
        let prevUnforked = origin st
        put $ Unforked [] subst osubst subes defs upar $ Just st
      Forked{origin=Forked{}} -> shouldnt "Complete an unbuilt fork"


-- |Start a new branch for the next integer value of the switch variable.
beginBranch :: BodyBuilder ()
beginBranch = do
    st <- get
    logBuild $ "<<<< <<<< Beginning to build branch "
               ++ show (length $ stForkBods st) ++ " on " ++ show (stForkVar st)
    case st of
        Unforked{} ->
          shouldnt "beginBranch in Unforked state"
        Forked{origin=Unforked _ subst vsubst subexp defs _ _} -> do
          put $ Unforked [] subst vsubst subexp defs (Just st) Nothing
        Forked{origin=Forked{}} ->
          shouldnt "Beginning a branch outside of a fork"


-- |End the current branch.
endBranch :: BodyBuilder ()
endBranch = do
    st <- get
    case st of
        Forked{} ->
          shouldnt "endBranch in Unforked state"
        Unforked{uParent=Just parent} -> do
          logBuild $ ">>>> >>>> Ending branch "
              ++ show (length $ stForkBods parent)
              ++ " on " ++ show (stForkVar parent)
          put $ parent { stForkBods = st:stForkBods parent }
        Unforked{} ->
          shouldnt "endBranch with no parent fork"



-- buildBranch :: PrimVarName -> TypeSpec -> Maybe Prim
--             -> BodyState -> (BodyBuilder (),Int) -> Compiler BodyState
-- buildBranch var ty definer st (builder,val) = do
--     logMsg BodyBuilder $ "<<<< <<<< Beginning to build branch "
--                          ++ show val ++ " on " ++ show var
--     let st' = st { currBuild = [],
--                    currSubst = Map.insert var (ArgInt (fromIntegral val) ty)
--                                $ currSubst st }
--     branch <- buildBranch' st' $ do
--         logBuild $ "Propagating " ++ show val ++ " result of " ++ show definer
--         whenJust definer $ propagateBinding var ty val
--         builder
--     logMsg BodyBuilder $ ">>>> >>>> Finished building branch "
--                          ++ show val ++ " on " ++ show var
--     return branch
-- 
-- 
-- buildBranch' :: BodyState -> BodyBuilder () -> Compiler BodyState
-- buildBranch' st builder = snd <$> buildPrims st builder


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
      Unforked{} -> do
        prim' <- argExpandedPrim prim
        logBuild $ "Generating instr " ++ show prim ++ " -> " ++ show prim'
        instr' prim' pos
      Forked{} -> do
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
instr' prim@(PrimForeign "lpvm" "alloc" [] args) pos
  = do
    logBuild $ "  Leaving alloc alone"
    rawInstr prim pos
instr' prim pos = do
    let (prim',newOuts) = splitPrimOutputs prim
    logBuild $ "Looking for computed instr " ++ show prim' ++ " ..."
    currSubExprs <- gets subExprs
    logBuild $ "with subExprs = " ++ show currSubExprs
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


-- concatBodies :: BodyState -> BodyState -> BodyState
-- -- XXX Handle uParent parts!
-- concatBodies (Unforked revBody1 _ _ _ _ _ _)
--              (Unforked revBody2 subs osubs comp definers _ _)
--     = Unforked (revBody2 ++ revBody1) subs osubs comp definers Nothing Nothing
--     -- NB: bodies are reversed
-- -- XXX Handle uParent and fParent parts!
-- concatBodies (Unforked revBody1 _ _ _ _ _ _) (Forked revBody2 var ty bods _ _)
--     = Forked (revBody2 ++ revBody1) var ty bods Nothing Nothing -- bodies are reversed
-- concatBodies _ _ = shouldnt "Fork after fork should have been caught earlier"

addInstrToState :: Placed Prim -> BodyState -> BodyState
addInstrToState ins st@Unforked{} = st { currBuild = ins:currBuild st}
addInstrToState ins st@Forked{}
    = st { stForkBods = List.map (addInstrToState ins) $ stForkBods st }


-- |Return the current ultimate value of the input argument.
expandArg :: PrimArg -> BodyBuilder PrimArg
expandArg arg@(ArgVar var _ FlowIn _ _) = do
    var' <- gets (Map.lookup var . currSubst)
    maybe (return arg) expandArg var'
expandArg (ArgVar var typ FlowOut ftype lst) = do
    var' <- gets (Map.findWithDefault var var . outSubst)
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
