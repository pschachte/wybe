--  File     : BodyBuilder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri 22 May 2015 10:59:56 AEST
--  Purpose  : A monad to build up a procedure Body, with copy propagation
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--

module BodyBuilder (
  BodyBuilder, buildBody, instr, buildFork
  ) where

import AST
import Options (LogSelection(BodyBuilder))
import Data.Map as Map
import Data.List as List
import Data.Bits
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State


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
    currBuild     :: BodyBuildState, -- ^The body we're building
    currSubst    :: Substitution,    -- ^variable substitutions to propagate
    outSubst     :: VarSubstitution, -- ^Substitutions for variable assignments
    subExprs     :: ComputedCalls    -- ^Previously computed calls to reuse
    } deriving Show

type Substitution = Map PrimVarName PrimArg
type VarSubstitution = Map PrimVarName PrimVarName

-- To handle common subexpression elimination, we keep a map from previous
-- calls with their outputs removed to the outputs.  This type encapsulates
-- that.  In the Prim keys, all PrimArgs are inputs.
type ComputedCalls = Map Prim [PrimArg]

data BodyBuildState
    = Unforked [Placed Prim]  -- reversed list of prims
    | Forked   ProcBody


instance Show BodyBuildState where
  show (Unforked revPrims) =
      showBlock 4 $ ProcBody (reverse revPrims) NoFork
  show (Forked body) = show body

currBody :: BodyState -> ProcBody
currBody (BodyState (Unforked prims) _ _ _) =
    ProcBody (reverse prims) NoFork
currBody (BodyState (Forked body) _ _ _) = body


initState :: VarSubstitution -> BodyState
initState oSubst = BodyState (Unforked []) Map.empty oSubst Map.empty


continueState :: BodyState -> BodyState
continueState (BodyState _ subst oSubst calls) =
    BodyState (Unforked []) subst oSubst calls


----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body
buildBody :: VarSubstitution -> BodyBuilder a -> Compiler (a,ProcBody)
buildBody oSubst builder = do
    logMsg BodyBuilder "<<<< Beginning to build a proc body"
    (a,bstate) <- runStateT builder $ initState oSubst
    logMsg BodyBuilder ">>>> Finished  building a proc body"
    return (a,currBody bstate)


buildFork :: PrimVarName -> TypeSpec -> Bool -> [BodyBuilder ()] 
             -> BodyBuilder ()
buildFork var ty final branchBuilders = do
    arg' <- expandArg $ ArgVar var ty FlowIn Ordinary False
    logBuild $ "<<<< beginning to build a new fork on " ++ show arg'
      ++ " (final=" ++ show final ++ ")"
    ProcBody prims fork <- gets currBody
    case arg' of
      ArgInt n _ -> -- result known at compile-time:  only compile winner
        case drop (fromIntegral n) branchBuilders of
          [] -> shouldnt "branch constant greater than number of cases"
          (winner:_) -> do
            logBuild $ "**** condition result is " ++ show n
            winner
      ArgVar var' ty _ _ _ -> do -- normal condition with unknown result
        case fork of
          PrimFork _ _ _ _ -> 
            shouldnt "Building a fork while building a fork"
          NoFork -> 
            modify (\s -> s {currBuild = Forked $ ProcBody prims
                                         $ PrimFork var' ty final [] })
        mapM_ buildBranch branchBuilders
        ProcBody prims' fork' <- gets currBody
        case fork' of
          NoFork -> return ()
          PrimFork v ty l (b@(ProcBody pprims fork):bs) | all (==b) bs -> do
            -- all branches are equal:  don't create a new fork
            logBuild $ "All branches equal:  simplifying body to:"
            let newPrims = pprims ++ prims'
            case fork of
              NoFork -> do
                logBuild $ showPlacedPrims 4 newPrims
                modify (\s -> s { currBuild = Unforked $ reverse newPrims })
              PrimFork v ty l bods -> do
                logBuild $ showBlock 4 $ ProcBody newPrims fork
                modify (\s -> s { currBuild = Forked $ ProcBody newPrims fork })
          PrimFork v ty l revBranches ->
            modify (\s -> s { currBuild =
                              Forked $ ProcBody prims'
                                       $ PrimFork v ty l 
                                       $ reverse revBranches })
      _ -> shouldnt "Switch on non-integer value"
    logBuild $ ">>>> Finished building a fork"


buildBranch :: BodyBuilder () -> BodyBuilder ()
buildBranch builder = do
    logBuild "<<<< <<<< Beginning to build a branch"
    branch <- buildPrims builder
    logBuild ">>>> >>>> Finished  building a branch"
    ProcBody revPrims fork <- gets currBody
    case fork of
      NoFork -> shouldnt "Building a branch outside of buildFork"
      PrimFork v ty l branches ->
        modify (\s -> s { currBuild =
                          Forked $ ProcBody revPrims
                                   $ PrimFork v ty l $ branch : branches })

buildPrims :: BodyBuilder () -> BodyBuilder ProcBody
buildPrims builder = do
    oldState <- get
    ((),bstate) <- lift $ runStateT builder $ continueState oldState
    return $ currBody bstate


-- |Add an instruction to the current body, after applying the current
--  substitution. If it's a move instruction, add it to the current
--  substitution, and only add it if it assigns a protected variable.
instr :: Prim -> OptPos -> BodyBuilder ()
instr PrimNop _ = do
    -- Filter out NOPs
    return ()
instr prim pos = do         
    prim' <- argExpandedPrim prim
    instr' prim' pos


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
--     already has an output value, that should stop us from trying
--     to reuse modified structures or the results of calls to
--     access after a structure is modified, so alloc should be
--     the only problem that needs fixing.
instr' prim@(PrimForeign "lpvm" "alloc" [] args) pos
  = do
    logBuild $ "  Leaving alloc alone"
    rawInstr prim pos
instr' prim pos = do
    let (prim',newOuts) = splitPrimOutputs prim
    logBuild $ "Looking for computed instr " ++ show prim' ++ " ..."
    match <- gets (Map.lookup prim' . subExprs)
    case match of
        Nothing -> do
            -- record prim executed (and other modes), and generate instr
            logBuild $ "not found"
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
outVarIn arg =
    shouldnt $ "outVarIn not actually out: " ++ show arg


argExpandedPrim :: Prim -> BodyBuilder Prim
argExpandedPrim (PrimCall pspec args) = do
    args' <- mapM expandArg args
    return $ PrimCall pspec args'
argExpandedPrim (PrimForeign lang nm flags args) = do
    args' <- mapM expandArg args
    return $ simplifyForeign lang nm flags args'
argExpandedPrim PrimNop =
    shouldnt "argExpandedPrim: Nops should be filtered out by now"


splitPrimOutputs :: Prim -> (Prim, [PrimArg])
splitPrimOutputs (PrimCall pspec args) =
    let (inArgs,outArgs) = splitArgsByMode args
    in (PrimCall pspec inArgs, outArgs)
splitPrimOutputs (PrimForeign lang nm flags args) = 
    let (inArgs,outArgs) = splitArgsByMode args
    in (PrimForeign lang nm flags inArgs, outArgs)
splitPrimOutputs PrimNop =
    shouldnt "splitPrimOutputs: Nops should be filtered out by now"


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
--  XXX Doesn't handle arithmetic identities like commutative addition,
--      if that's a good way to handle them.
addAllModes :: Prim -> BodyBuilder ()
addAllModes (PrimCall pspec args) = do
    let (inArgs,outArgs) = splitArgsByMode args
    let fakeInstr = PrimCall pspec inArgs
    logBuild $ "Recording computed instr " ++ show fakeInstr
    modify (\s -> s {subExprs = Map.insert fakeInstr outArgs $ subExprs s})
addAllModes (PrimForeign lang nm flags args)  = do
    let (inArgs,outArgs) = splitArgsByMode args
    let fakeInstr = PrimForeign lang nm flags inArgs
    logBuild $ "Recording computed instr " ++ show fakeInstr
    modify (\s -> s {subExprs = Map.insert fakeInstr outArgs $ subExprs s})
addAllModes PrimNop =
    shouldnt "splitPrimOutputs: Nops should be filtered out by now"


-- |Unconditionally add an instr to the current body
rawInstr :: Prim -> OptPos -> BodyBuilder ()
rawInstr prim pos = do
    logBuild $ "---- adding instruction " ++ show prim
    validateInstr prim
    modify (\s -> s { currBuild = addInstrToState (maybePlace prim pos)
                                 $ currBuild s })


splitArgsByMode :: [PrimArg] -> ([PrimArg], [PrimArg])
splitArgsByMode =
    List.foldr (\a (ins,outs) -> if argFlowDirection a == FlowIn
                                 then (a:ins,outs)
                                 else (ins,a:outs))
    ([],[])


validateInstr :: Prim -> BodyBuilder ()
validateInstr instr@(PrimCall _ args) =        mapM_ (validateArg instr) args
validateInstr instr@(PrimForeign _ _ _ args) = mapM_ (validateArg instr) args
validateInstr PrimNop = return ()

validateArg :: Prim -> PrimArg -> BodyBuilder ()
validateArg instr (ArgVar _ ty _ _ _) = validateType ty instr
validateArg instr (ArgInt    _ ty)    = validateType ty instr
validateArg instr (ArgFloat  _ ty)    = validateType ty instr
validateArg instr (ArgString _ ty)    = validateType ty instr
validateArg instr (ArgChar   _ ty)    = validateType ty instr

validateType :: TypeSpec -> Prim -> BodyBuilder ()
validateType Unspecified instr =
    shouldnt $ "Unspecified type in argument of " ++ show instr
validateType (TypeSpec _ _ _) instr = return ()

addInstrToState :: Placed Prim -> BodyBuildState -> BodyBuildState
addInstrToState ins (Unforked revPrims) = Unforked $ ins:revPrims
addInstrToState ins (Forked body) = Forked $ addInstrToBody ins body

addInstrToBody ::  Placed Prim -> ProcBody -> ProcBody
addInstrToBody ins (ProcBody prims NoFork) =
    ProcBody (prims ++ [ins]) NoFork
addInstrToBody ins (ProcBody prims (PrimFork v ty l bodies)) =
    ProcBody prims
    (PrimFork v ty l (List.map (addInstrToBody ins) bodies))


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
--                          Extracting the Actual Body
----------------------------------------------------------------

----------------------------------------------------------------
--                              Constant Folding
----------------------------------------------------------------

-- |Transform primitives with all inputs known into a move instruction by
--  performing the operation at compile-time.
simplifyForeign ::  String -> ProcName -> [Ident] -> [PrimArg] -> Prim
simplifyForeign "llvm" op flags args = simplifyOp op flags args
simplifyForeign lang op flags args = PrimForeign lang op flags args


-- |If the specified argument is an input, then it is a constant
constIfInput :: PrimArg -> Bool
constIfInput (ArgVar _ _ FlowIn _ _) = False
constIfInput _ = True


-- | Simplify llvm instructions where possible.  This handles constant
--   folding and simple (single-operation) algebraic simplifications
--   (left and right identities and annihilators).
simplifyOp :: ProcName -> [Ident] -> [PrimArg] -> Prim
-- Integer ops
simplifyOp "add" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1+n2) ty, output]
simplifyOp "add" _ [ArgInt 0 ty, arg, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "add" _ [arg, ArgInt 0 ty, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "sub" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1-n2) ty, output]
simplifyOp "sub" _ [arg, ArgInt 0 _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "mul" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1*n2) ty, output]
simplifyOp "mul" _ [ArgInt 1 ty, arg, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "mul" _ [arg, ArgInt 1 ty, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "mul" _ [ArgInt 0 ty, _, output] =
  PrimForeign "llvm" "move" [] [ArgInt 0 ty, output]
simplifyOp "mul" _ [_, ArgInt 0 ty, output] =
  PrimForeign "llvm" "move" [] [ArgInt 0 ty, output]
simplifyOp "div" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1 `div` n2) ty, output]
simplifyOp "div" _ [arg, ArgInt 1 _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
-- Bitstring ops
simplifyOp "and" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" []
  [ArgInt (fromIntegral n1 .&. fromIntegral n2) ty, output]
simplifyOp "and" _ [ArgInt 0 ty, _, output] =
  PrimForeign "llvm" "move" [] [ArgInt 0 ty, output]
simplifyOp "and" _ [_, ArgInt 0 ty, output] =
  PrimForeign "llvm" "move" [] [ArgInt 0 ty, output]
simplifyOp "and" _ [ArgInt (-1) _, arg, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "and" _ [arg, ArgInt (-1) _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "or" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" []
  [ArgInt (fromIntegral n1 .|. fromIntegral n2) ty, output]
simplifyOp "or" _ [ArgInt (-1) ty, _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (-1) ty, output]
simplifyOp "or" _ [_, ArgInt (-1) ty, output] =
  PrimForeign "llvm" "move" [] [ArgInt (-1) ty, output]
simplifyOp "or" _ [ArgInt 0 _, arg, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "or" _ [arg, ArgInt 0 _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "xor" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" []
  [ArgInt (fromIntegral n1 `xor` fromIntegral n2) ty, output]
simplifyOp "xor" _ [ArgInt 0 _, arg, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "xor" _ [arg, ArgInt 0 _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
-- XXX should probably put shift ops here, too
-- Integer comparisons
simplifyOp "icmp" ["eq"] [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1==n2) ty, output]
simplifyOp "icmp" ["ne"] [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1/=n2) ty, output]
simplifyOp "icmp" ["slt"] [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1<n2) ty, output]
simplifyOp "icmp" ["sle"] [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1<=n2) ty, output]
simplifyOp "icmp" ["sgt"] [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1>n2) ty, output]
simplifyOp "icmp" ["sge"] [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1>=n2) ty, output]
-- Float ops
simplifyOp "fadd" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1+n2) ty, output]
simplifyOp "fadd" _ [ArgFloat 0 ty, arg, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "fadd" _ [arg, ArgFloat 0 ty, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "fsub" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1-n2) ty, output]
simplifyOp "fsub" _ [arg, ArgFloat 0 _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "fmul" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1*n2) ty, output]
simplifyOp "fmul" _ [arg, ArgFloat 1 _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
simplifyOp "fmul" _ [ArgFloat 1 _, arg, output] =
  PrimForeign "llvm" "move" [] [arg, output]
-- We don't handle float * 0.0 because of the semantics of IEEE floating mult.
simplifyOp "fdiv" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1/n2) ty, output]
simplifyOp "fdiv" _ [arg, ArgFloat 1 _, output] =
  PrimForeign "llvm" "move" [] [arg, output]
-- Float comparisons
simplifyOp "fcmp" ["eq"] [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1==n2) ty, output]
simplifyOp "fcmp" ["ne"] [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1/=n2) ty, output]
simplifyOp "fcmp" ["slt"] [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1<n2) ty, output]
simplifyOp "fcmp" ["sle"] [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1<=n2) ty, output]
simplifyOp "fcmp" ["sgt"] [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1>n2) ty, output]
simplifyOp "fcmp" ["sge"] [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (integerOfBool $ n1>=n2) ty, output]
simplifyOp name flags args = PrimForeign "llvm" name flags args


integerOfBool :: Bool -> Integer
integerOfBool False = 0
integerOfBool True  = 1


----------------------------------------------------------------
--                                  Logging
----------------------------------------------------------------

-- |Log a message, if we are logging body building activity.
logBuild :: String -> BodyBuilder ()
logBuild s = lift $ logMsg BodyBuilder s
