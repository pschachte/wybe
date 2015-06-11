--  File     : Expansion.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 14:58:14 2014
--  Purpose  : Replace certain procedure calls with others
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--
--  This code is used for inlining procedures and other similar
--  transformations.  As part of this, variables are also renamed.
--  This code operates on LPVM (Prim) form.
--
--  This code is used bottom-up, ie, callees are expanded before 
--  their callers, so it does not need to recursively expand calls.

module Expansion (procExpansion) where

import AST
import BodyBuilder
import Options (LogSelection(Expansion))
import Data.Map as Map
import Data.List as List
import Data.Set as Set
import Data.Maybe
import Control.Monad
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.Trans.State

import Debug.Trace


-- | Expand the supplied ProcDef, inlining as desired.
procExpansion :: ProcDef -> Compiler ProcDef
procExpansion def = do
    logMsg Expansion $ "\nTry to expand proc " ++ show (procName def)
    let ProcDefPrim proto body = procImpln def
    let tmp = procTmpCount def
    (expander,body') <- buildBody (outputParams proto) $ 
                        execStateT (expandBody body) $
                          initExpanderState tmp $ outputParams proto
    let def' = def { procImpln = ProcDefPrim proto body',
                     procTmpCount = tmpCount expander }
    when (def /= def') $
      logMsg Expansion $
        "Expanded:" ++ showProcDef 4 def ++
        "\nTo:" ++ showProcDef 4 def'
    return def'



-- |Type to remember the variable renamings.
type Renaming = Map PrimVarName PrimArg


-- |A Renaming that doesn't substitute anything
identityRenaming :: Renaming
identityRenaming = Map.empty


----------------------------------------------------------------
--                       The Expander Monad
--
-- This monad keeps track of variable renaming needed to keep inlining
-- hygenic.  To do this, we rename all the input parameters of the proc to 
-- be inlined, and when expanding the body, we rename any variables when 
-- first assigned.  The exception to this is the proc's output parameters.  
-- These are kept as a set.  We also maintain a counter for temporary 
-- variable names.
----------------------------------------------------------------

data ExpanderState = Expander {
    inlining     :: Bool,         -- ^Whether we are currently inlining (and
                                  --  therefore should not inline calls)
    renaming     :: Renaming,     -- ^The current variable renaming
    tmpCount     :: Int,          -- ^Next available tmp variable number
    noFork       :: Bool          -- ^There's no fork at the end of this body
    }


type Expander = StateT ExpanderState BodyBuilder

-- |Return a fresh variable name.  This assumes that all variables in inlined code
-- are given fresh variable names, so temp names appearing in procs being inlined
-- don't clash.
tmpVar :: Expander PrimVarName
tmpVar = do
    tmp <- gets tmpCount
    modify (\s -> s { tmpCount = tmp+1 })
    return $ PrimVarName (mkTempName tmp) 0


-- |Substitute a fresh temp variable for the specified variable
freshVar :: PrimVarName -> TypeSpec -> Expander PrimArg
freshVar oldVar typ = do
    tmp <- gets tmpCount
    modify (\s -> s { tmpCount = tmp+1 })
    let newVar = PrimVarName (mkTempName tmp) 0
    addRenaming oldVar $ ArgVar newVar typ FlowIn Ordinary False
    return $ ArgVar newVar typ FlowOut Ordinary False


-- |Add a binding for a variable.  If that variable is an output for the proc being
--  defined, also add an explicit assignment to that variable.
addRenaming :: PrimVarName -> PrimArg -> Expander ()
addRenaming var val = do
    logExpansion $ "      adding renaming " ++ show var ++ " -> " ++ show val
    modify (\s -> s { renaming = Map.insert var val $ renaming s })
-- Need to add renaming even if it's an identity, because renamings 
-- are used to tell which variables shoudn't be renamed.


addInstr :: Prim -> OptPos -> Expander ()
addInstr prim pos = lift $ instr prim pos


initExpanderState :: Int -> Set PrimVarName -> ExpanderState
initExpanderState tmpCount varSet = 
    Expander False identityRenaming tmpCount True


----------------------------------------------------------------
--                        Expanding Proc Bodies
----------------------------------------------------------------

expandBody :: ProcBody -> Expander ()
expandBody (ProcBody prims fork) = do
    modify (\s -> s { noFork = fork == NoFork })
    expandPrims prims
    state <- get
    case fork of
      NoFork -> return ()
      PrimFork var last bodies -> do
        logExpansion $ "Now expanding fork (" ++ 
          (if inlining state then "without" else "WITH") ++ " inlining)"
        let var' = case Map.lookup var $ renaming state of
              Nothing -> var
              Just (ArgVar v _ _ _ _) -> v 
              -- XXX should handle case of switch on int constant
              Just _ -> shouldnt "expansion led to non-var conditional"
        lift $ buildFork var' last 
          $ List.map (\b -> fmap fst $ runStateT (expandBody b) state) bodies
        logExpansion $ "Finished expanding fork"


expandPrims :: [Placed Prim] -> Expander ()
expandPrims pprims = do
    mapM_ (\(p:rest) -> expandPrim (content p) (place p) (List.null rest))
      $ init $ tails pprims

-- XXX allow this to handle primitives that can fail with all inputs known, like 
--     less than, removing ops that succeed and killing branches that fail.
-- XXX allow this to handle non-primitives with all inputs known by inlining.
expandPrim :: Prim -> OptPos -> Bool -> Expander ()
expandPrim call@(PrimCall pspec args) pos last = do
    args' <- mapM expandArg args
    let call' = PrimCall pspec args'
    logExpansion $ "  Expand call " ++ show call'
    inlining <- gets inlining
    if inlining
      then do
        logExpansion $ "  Cannot inline:  already inlining"
        addInstr call' pos
      else do
        def <- lift $ lift $ getProcDef pspec
        let ProcDefPrim proto body = procImpln def
        if procInline def
          then inlineCall proto args' body pos
          else do
            inlinableLast <- gets (((last && singleCaller def 
                                     && procVis def == Private) &&) 
                                   . noFork)
            if inlinableLast
              then do
                inlineCall proto args' body pos
              else do
                logExpansion $ "  Not inlinable"
                addInstr call' pos
expandPrim (PrimForeign lang nm flags args) pos _ = do
    state <- get
    logExpansion $ "  Expanding " ++ show (PrimForeign lang nm flags args)
    logExpansion $ "    with renaming = " ++ show (renaming state)
    args' <- mapM expandArg args
    logExpansion $ "  --> " ++ show (PrimForeign lang nm flags args')
    addInstr (constantFold lang nm flags args')  pos
    state <- get
    logExpansion $ "    renaming = " ++ show (renaming state)
expandPrim prim pos _ = do
    addInstr prim pos


inlineCall :: PrimProto -> [PrimArg] -> ProcBody -> OptPos -> Expander ()
inlineCall proto args body pos = do
    saved <- get
    logExpansion $ "  Before inlining:"
    logExpansion $ "    renaming = " ++ show (renaming saved)
    modify (\s -> s { renaming = identityRenaming, 
                      inlining = True })
    mapM_ (addInputAssign pos) $ zip (primProtoParams proto) args
    logExpansion $ "  Inlining defn: " ++ showBlock 4 body
    expandBody body
    tmp' <- gets tmpCount
    subst <- gets ((Map.filterWithKey (\k _ -> List.elem k $ outputArgs args)) 
                   . renaming)
    mapM_ (addOutputAssign pos) $ zip (primProtoParams proto) args
    -- Throw away state after inlining, except ...
    put saved
    -- ... put back temp count
    modify (\s -> s { tmpCount = tmp' })
                      -- renaming = Map.union subst $ renaming s})
    state <- get
    logExpansion $ "  After inlining:"
    logExpansion $ "    renaming = " ++ show (renaming state)


expandArg :: PrimArg -> Expander PrimArg
expandArg arg@(ArgVar var typ flow _ _) = do
    renameAll <- gets inlining
    if renameAll
      then case flow of
      FlowOut -> freshVar var typ
      FlowIn ->
        gets (Map.findWithDefault 
              (shouldnt $ "inlining: reference to unassigned variable " ++ show var) 
              var . renaming)
      else return arg
expandArg arg = return arg


outputParams :: PrimProto -> Set PrimVarName
outputParams proto = 
  Set.fromList $ List.map primParamName $
  List.filter ((==FlowOut) . primParamFlow) $ primProtoParams proto


outputArgs :: [PrimArg] -> [PrimVarName]
outputArgs args =
    List.map outArgVar $ List.filter ((FlowOut ==) . argFlowDirection) args

-- |Add an assignment of input argument to parameter in preparation for inlining
--  a call.  The parameter name must be substituted with a new name; the argument
--  has already been renamed as appropriate for the calling context.
addInputAssign :: OptPos -> (PrimParam,PrimArg) -> Expander ()
addInputAssign _ (PrimParam k ty FlowOut _ _,v) = return ()
addInputAssign pos (param@(PrimParam name ty FlowIn _ _),v) = do
    when (Unspecified == ty) $
      shouldnt $ "Danger: untyped param: " ++ show param
    when (Unspecified == argType v) $
      shouldnt $ "Danger: untyped argument: " ++ show v
    newVar <- freshVar name ty
    addInstr (PrimForeign "llvm" "move" [] [v,newVar]) pos
             

-- |Add an assignment of output parameter to argument following inlining of
--  a call.  The parameter has been substituted with a new name, but the
--  argument should be interpreted without renaming.
addOutputAssign :: OptPos -> (PrimParam,PrimArg) -> Expander ()
addOutputAssign _ (PrimParam k ty FlowIn _ _,v) = return ()
addOutputAssign pos (param@(PrimParam pname ty FlowOut _ _), v) = do
    when (Unspecified == ty) $
      shouldnt $ "Danger: untyped param: " ++ show param
    when (Unspecified == argType v) $
      shouldnt $ "Danger: untyped argument: " ++ show v
    oldVar <- expandArg (ArgVar pname ty FlowIn Ordinary False)
    addInstr (PrimForeign "llvm" "move" [] [oldVar,v]) pos

-- renameParam :: Renaming -> PrimParam -> PrimParam
-- renameParam renaming param@(PrimParam name typ FlowOut ftype inf ) = 
--     maybe param 
--     (\arg -> case arg of
--           ArgVar name' _ _ _ _ -> PrimParam name' typ FlowOut ftype inf
--           _ -> param) $
--     Map.lookup name renaming
-- renameParam _ param = param


singleCaller :: ProcDef -> Bool
singleCaller def =
    let m = procCallers def
    in  Map.size m == 1 && (snd . Map.findMin) m == 1


-- |Log a message, if we are logging unbrancher activity.
logExpansion :: String -> Expander ()
logExpansion s = lift $ lift $ logMsg Expansion s


----------------------------------------------------------------
--                              Constant Folding
----------------------------------------------------------------

-- |Transform primitives with all inputs known into a move instruction by performing
--  the operation at compile-time.
constantFold ::  String -> ProcName -> [Ident] -> [PrimArg] -> Prim
constantFold "llvm" op flags args
  | all constIfInput args = simplifyOp op flags args
-- XXX finish this for remaining primitives
constantFold lang op flags args = PrimForeign lang op flags args


-- |If the specified argument is an input, then it is a constant
constIfInput :: PrimArg -> Bool
constIfInput (ArgVar _ _ FlowIn _ _) = False
constIfInput _ = True


simplifyOp :: ProcName -> [Ident] -> [PrimArg] -> Prim
simplifyOp "add" _ [ArgInt n1 ty, ArgInt n2 _, output] =
  PrimForeign "llvm" "move" [] [ArgInt (n1+n2) ty, output]
simplifyOp name flags args = PrimForeign "llvm" name flags args