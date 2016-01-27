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
    outSubst     :: VarSubstitution  -- ^Substitutions for variable assignments
    } deriving Show

type Substitution = Map PrimVarName PrimArg
type VarSubstitution = Map PrimVarName PrimVarName


data BodyBuildState
    = Unforked [Placed Prim]  -- reversed list of prims
    | Forked   ProcBody


instance Show BodyBuildState where
  show (Unforked revPrims) =
      showBlock 4 $ ProcBody (reverse revPrims) NoFork
  show (Forked body) = show body

currBody :: BodyState -> ProcBody
currBody (BodyState (Unforked prims) _ _) =
  ProcBody (reverse prims) NoFork
currBody (BodyState (Forked body) _ _) = body


initState :: VarSubstitution -> BodyState
initState oSubst = BodyState (Unforked []) Map.empty oSubst


continueState :: Substitution -> VarSubstitution -> BodyState
continueState subst oSubst = BodyState (Unforked []) subst oSubst


----------------------------------------------------------------
--                      BodyBuilder Primitive Operations
----------------------------------------------------------------

-- |Run a BodyBuilder monad and extract the final proc body
buildBody :: VarSubstitution -> BodyBuilder a -> Compiler (a,ProcBody)
buildBody oSubst builder = do
    logMsg BodyBuilder "<<<< Beginning to build a proc body"
    -- (a,final) <- runStateT builder $ BodyState (Just []) []
    (a,bstate) <- runStateT builder $ initState oSubst
    logMsg BodyBuilder ">>>> Finished  building a proc body"
    -- return (a,astateBody final)
    return (a,currBody bstate)


buildFork :: PrimVarName -> Bool -> [BodyBuilder ()] -> BodyBuilder ()
buildFork var final branchBuilders = do
    arg' <- expandArg
            $ ArgVar var (TypeSpec ["wybe"] "int" []) FlowIn Ordinary False
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
      ArgVar var' _ _ _ _ -> do -- normal condition with unknown result
        case fork of
          PrimFork _ _ _ -> shouldnt "Building a fork while building a fork"
          NoFork -> 
            modify (\s -> s {currBuild =
                             Forked $ ProcBody prims
                                      $ PrimFork var' final [] })
        mapM_ buildBranch branchBuilders
        ProcBody revPrims' fork' <- gets currBody
        case fork' of
          NoFork -> shouldnt "Building a fork produced an empty fork"
          PrimFork v l revBranches ->
            modify (\s -> s { currBuild =
                              Forked $ ProcBody revPrims'
                                       $ PrimFork v l $ reverse revBranches })
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
      PrimFork v l branches ->
        modify (\s -> s { currBuild =
                          Forked $ ProcBody revPrims
                                   $ PrimFork v l $ branch : branches })

buildPrims :: BodyBuilder () -> BodyBuilder ProcBody
buildPrims builder = do
    subst <- gets currSubst
    oSubst <- gets outSubst
    ((),bstate) <- lift $ runStateT builder $ continueState subst oSubst
    return $ currBody bstate


-- |Add an instruction to the current body, after applying the current
--  substitution. If it's a move instruction, add it to the current
--  substitution, and only add it if it assigns a protected variable.
instr :: Prim -> OptPos -> BodyBuilder ()
instr (PrimCall pspec args) pos = do
    args' <- mapM expandArg args
    rawInstr (PrimCall pspec args') pos
instr (PrimForeign  lang nm flags args) pos = do
    args' <- mapM expandArg args
    foreignInstr (constantFold lang nm flags args') pos
instr PrimNop _ = do
    -- Filter out NOPs
    return ()


-- |Add an instr, unless it's a move to a non-protected variable, which is
--  treated as a new substitution.
foreignInstr :: Prim -> OptPos -> StateT BodyState Compiler ()
foreignInstr ins@(PrimForeign "llvm" "move" []
                    [val, argvar@(ArgVar var _ flow _ _)]) pos 
  = do
    logBuild $ "  Expanding move(" ++ show val ++ ", " ++ show argvar ++ ")"
    unless (flow == FlowOut && argFlowDirection val == FlowIn) $ 
      shouldnt "move instruction with wrong flow"
    outVar <- gets (Map.findWithDefault var var . outSubst)
    addSubst outVar val
    -- keep this assignment if it binds an important var; rawInstr will
    -- rename the output var
    -- when (isJust maybeOutVar) $ rawInstr ins pos
    -- Always insert assignment, and count on dead code elim to remove it
    -- unless the variable, rather than just the value, is needed
    rawInstr ins pos
foreignInstr prim pos = rawInstr prim pos


-- |Add a binding for a variable. If that variable is an output for the
--  proc being defined, also add an explicit assignment to that variable.
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
    validateInstr prim
    modify (\s -> s { currBuild = addInstrToState (maybePlace prim pos)
                                 $ currBuild s })


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
addInstrToBody ins (ProcBody prims (PrimFork v l bodies)) =
    ProcBody prims
    (PrimFork v l (List.map (addInstrToBody ins) bodies))


    -- ProcBody prims fork <- gets currBody
    -- case fork of
    --   -- PrimFork _ _ _ -> shouldnt "adding an instr after a fork"
    --   -- XXX should add a single instruction at the end of the fork
    --   NoFork ->     
    --     modify (\s -> s { currBody = ProcBody (maybePlace prim pos : prims) fork })

-- |Return the current ultimate value of the input argument.
expandArg :: PrimArg -> BodyBuilder PrimArg
expandArg arg@(ArgVar var _ FlowIn _ _) = do
    var' <- gets (Map.lookup var . currSubst)
    maybe (return arg) expandArg var'
expandArg (ArgVar var typ FlowOut ftype lst) = do
    var' <- gets (Map.findWithDefault var var . outSubst)
    return $ ArgVar var' typ FlowOut ftype lst
expandArg arg = return arg


-- setPrimArgFlow :: PrimFlow -> ArgFlowType -> PrimArg -> PrimArg
-- setPrimArgFlow flow ftype (ArgVar n t _ _ lst) = (ArgVar n t flow ftype lst)
-- setPrimArgFlow FlowIn _ arg = arg
-- setPrimArgFlow FlowOut _ arg =
--     -- XXX eventually want this to generate a comparison, once we allow failure
--     shouldnt $ "trying to make " ++ show arg ++ " an output argument"


----------------------------------------------------------------
--                          Extracting the Actual Body
----------------------------------------------------------------

----------------------------------------------------------------
--                              Constant Folding
----------------------------------------------------------------

-- |Transform primitives with all inputs known into a move instruction by
--  performing the operation at compile-time.
constantFold ::  String -> ProcName -> [Ident] -> [PrimArg] -> Prim
constantFold "llvm" op flags args
  | all constIfInput args = simplifyOp op flags args
constantFold lang op flags args = PrimForeign lang op flags args


-- |If the specified argument is an input, then it is a constant
constIfInput :: PrimArg -> Bool
constIfInput (ArgVar _ _ FlowIn _ _) = False
constIfInput _ = True


simplifyOp :: ProcName -> [Ident] -> [PrimArg] -> Prim
simplifyOp "add" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1+n2) ty, output]
simplifyOp "sub" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1-n2) ty, output]
simplifyOp "mul" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1*n2) ty, output]
simplifyOp "div" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1 `div` n2) ty, output]
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
simplifyOp "fadd" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1+n2) ty, output]
simplifyOp "fsub" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1-n2) ty, output]
simplifyOp "fmul" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1*n2) ty, output]
simplifyOp "fdiv" _ [ArgFloat n1 ty, ArgFloat n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgFloat (n1/n2) ty, output]
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

-- |Log a message, if we are logging unbrancher activity.
logBuild :: String -> BodyBuilder ()
logBuild s = lift $ logMsg BodyBuilder s
