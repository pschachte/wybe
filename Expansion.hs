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
    (expander,body') <- buildBody $ execStateT (expandBody body) $
                          initExpanderState tmp $ outputParams proto
    let proto' = proto { primProtoParams =
                              List.map (renameParam $ substitution expander) $
                              primProtoParams proto }
    let def' = def { procImpln = ProcDefPrim proto body',
                     procTmpCount = tmpCount expander }
    when (def /= def') $
      logMsg Expansion $
        "Expanded:" ++ showProcDef 4 def ++
        "\nTo:" ++ showProcDef 4 def'
    return def'



-- |Type to remember the variable renamings.
type Substitution = Map PrimVarName PrimArg


-- |A Substitution that doesn't substitute anything
identitySubstitution :: Substitution
identitySubstitution = Map.empty


-- meetSubsts :: Substitution -> Substitution -> Substitution
-- meetSubsts = Map.mergeWithKey
--              (\k v1 v2 -> if v1 == v2 then Just v1 else Nothing)
--              (const Map.empty) 
--              (const Map.empty) 


-- projectSubst :: Set PrimVarName -> Substitution -> Substitution
-- projectSubst protected subst = 
--     Map.fromAscList $
--     List.filter (flip Set.member protected . fst) $
--     Map.toAscList subst


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
    substitution :: Substitution,     -- ^The current variable substitution
    protected    :: Set PrimVarName,  -- ^Variables that cannot be renamed
    tmpCount     :: Int,              -- ^Next available tmp variable number
    finalFork    :: PrimFork,         -- ^The fork ending this body
    inlining     :: Bool,             -- ^Whether we are currently inlining (and
                                      --  therefore should not inline calls)
    inliningFork :: Bool              -- ^Whether the finalFork results from inlining
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

-- |Add a binding for a variable.  If that variable is an output for the proc being
--  defined, also add an explicit assignment to that variable.
addSubst :: PrimVarName -> PrimArg -> Expander ()
addSubst var val = do
    logExpansion $ "      adding subst " ++ show var ++ " -> " ++ show val
    modify (\s -> s { substitution = Map.insert var val $ substitution s })


addInstr :: Prim -> OptPos -> Expander ()
addInstr (PrimForeign "llvm" "move" [] [val, argvar@(ArgVar var _ flow _ _)]) pos = do
    logExpansion $ "  Expanding move(" ++ show val ++ ", ?" ++ show var ++ ")"
    unless (flow == FlowOut) $
      shouldnt "move instruction with wrong mode"
    addSubst var val
    noSubst <- gets (Set.member var . protected)
    when noSubst $ -- do we need to keep this assignment (to an output)?
      lift $ instr $ maybePlace
      (PrimForeign "llvm" "move" [] 
       [val, ArgVar var (argType val) FlowOut Ordinary False])
      Nothing
addInstr PrimNop _ = do
    -- Filter out NOPs
    return ()
addInstr prim pos = lift $ instr $ maybePlace prim pos


insertFinalFork :: PrimFork -> Expander ()
insertFinalFork fork = do
    currFork <- gets finalFork
    checkError "Forks are piling up" (fork /= NoFork && currFork /= NoFork)
    when (fork /= NoFork) $ 
      modify (\s -> s { finalFork = fork })
    return ()


resetFinalFork :: Expander PrimFork
resetFinalFork = do
    fork <- gets finalFork
    modify (\s -> s { finalFork = NoFork })
    return fork


initExpanderState :: Int -> Set PrimVarName -> ExpanderState
initExpanderState tmpCount varSet = 
    Expander identitySubstitution varSet tmpCount NoFork False False


----------------------------------------------------------------
--                        Expanding Proc Bodies
----------------------------------------------------------------

expandBody :: ProcBody -> Expander ()
expandBody (ProcBody prims fork) = do
    insertFinalFork fork
    expandPrims prims
    state <- get
    case finalFork state of
      NoFork -> return ()
      PrimFork var last bodies -> do
        logExpansion $ "Now expanding fork (" ++ 
          (if inliningFork state then "without" else "WITH") ++ " inlining)"
        lift $ beginFork var last
        let var' = case Map.lookup var $ substitution state of
              Nothing -> var
              Just (ArgVar v _ _ _ _) -> v 
              Just _ -> shouldnt "expansion led to non-var conditional"
        let state' = state { inlining = inliningFork state, finalFork = NoFork }
        pairs <- lift $ mapM (\b -> runStateT (expandBranch b) state') bodies
        logExpansion $ "Finished expanding fork"
        lift $ finishFork
        -- Don't actually need this:
        -- let baseSubst = projectSubst (protected state) (substitution state)
        -- let subst = List.foldr meetSubsts baseSubst $
        --             List.map (substitution . snd) pairs
        return ()


expandBranch :: ProcBody -> Expander ()
expandBranch body = do
    lift nextBranch
    expandBody body
                                
expandPrims :: [Placed Prim] -> Expander ()
expandPrims pprims = do
    mapM_ (\(p:rest) -> expandPrim (content p) (place p) (List.null rest))
      $ init $ tails pprims

-- XXX allow this to handle primitives with all inputs known, such as addition
-- XXX allow this to handle primitives that can fail with all inputs known, like 
--     less than, removing ops that succeed and killing branches that fail.
-- XXX Ensure forks with only one branch are turned into straight-line code.
expandPrim :: Prim -> OptPos -> Bool -> Expander ()
expandPrim call@(PrimCall pspec args) pos last = do
    args' <- mapM expandArg args
    logExpansion $ "  Try to inline call " ++ show call
    inlining <- gets inlining
    if inlining
      then do
        logExpansion $ "  Cannot inline:  already inlining"
        addInstr call pos
      else do
        def <- lift $ lift $ getProcDef pspec
        let ProcDefPrim proto body = procImpln def
        if procInline def
          then inlineCall proto args' body
          else do
            inlinableLast <- gets (((last && singleCaller def 
                                     && procVis def == Private) &&) 
                                   . (== NoFork) . finalFork)
            if inlinableLast
              then do
                insertFinalFork $ bodyFork body
                modify (\s -> s { inliningFork = True })
                inlineCall proto args' body
              else do
                logExpansion $ "  Not inlinable"
                addInstr call pos

expandPrim (PrimForeign lang nm flags args) pos _ = do
    args' <- mapM expandArg args
    addInstr (PrimForeign lang nm flags args')  pos
expandPrim prim pos _ = do
    addInstr prim pos


inlineCall :: PrimProto -> [PrimArg] -> ProcBody -> Expander ()
inlineCall proto args body = do
    saved <- get
    logExpansion $ "  Before inlining:"
    logExpansion $ "    subst = " ++ show (substitution saved)
    logExpansion $ "    prot  = " ++ show (protected saved)
    modify (\s -> s { substitution = identitySubstitution, 
                      -- protected = Set.empty,
                      inlining = True })
    mapM_ addParamSubst $ zip (primProtoParams proto) args
    logExpansion $ "  Inlining defn: " ++ showBlock 4 body
    expandPrims $ bodyPrims body
    tmp' <- gets tmpCount
    subst <- gets ((Map.filterWithKey (\k _ -> List.elem k $ outputArgs args)) 
                   . substitution)
    -- Throw away state after inlining, except ...
    put saved
    -- ... put back temp count and output substitutions
    modify (\s -> s { tmpCount = tmp', 
                      substitution = Map.union subst $ substitution s})
    state <- get
    logExpansion $ "  After inlining:"
    logExpansion $ "    subst = " ++ show (substitution state)
    -- Now assign outputs
    -- mapM_ flip addInstr Nothing $ PrimForeign "llvm" "move" [] [val, argvar]


expandArg :: PrimArg -> Expander PrimArg
expandArg arg@(ArgVar var typ flow ftype _) = do
    -- logExpansion $ "expanding " ++ show arg
    renameAll <- gets inlining
    maybeArg <- gets (Map.lookup var . substitution)
    arg' <- case (maybeArg,renameAll,flow) of
        (Just a,_,_) -> return $ setPrimArgFlow flow ftype a
        (Nothing,False,_) -> return arg
        (Nothing,True,FlowIn) ->
            -- shouldnt $ "variable " ++ show var ++ " used before defined"
            return arg
        (Nothing,True,FlowOut) -> do
            freshVar <- tmpVar
            addSubst var $ ArgVar freshVar typ FlowIn ftype False
            return $ ArgVar freshVar typ FlowOut ftype False
    -- logExpansion $ " to " ++ show arg'
    return arg'
expandArg arg = return arg


setPrimArgFlow :: PrimFlow -> ArgFlowType -> PrimArg -> PrimArg
setPrimArgFlow flow ftype (ArgVar n t _ _ lst) = (ArgVar n t flow ftype lst)
setPrimArgFlow FlowIn _ arg = arg
setPrimArgFlow FlowOut _ arg =
    -- XXX eventually want this to generate a comparison, once we allow failure
    shouldnt $ "trying to make " ++ show arg ++ " an output argument"


outputParams :: PrimProto -> Set PrimVarName
outputParams proto = 
  Set.fromList $ List.map primParamName $
  List.filter ((==FlowOut) . primParamFlow) $ primProtoParams proto


outputArgs :: [PrimArg] -> [PrimVarName]
outputArgs args =
    List.map outArgVar $ List.filter ((FlowOut ==) . argFlowDirection) args


addParamSubst :: (PrimParam,PrimArg) -> Expander ()
addParamSubst param@(PrimParam k ty dir _ _,v) = do
    when (Unspecified == ty) $
      liftIO $ putStrLn $ "Danger: untyped param: " ++ show param
    when (Unspecified == argType v) $
      liftIO $ putStrLn $ "Danger: untyped argument: " ++ show v
    addSubst k v
             

renameParam :: Substitution -> PrimParam -> PrimParam
renameParam subst param@(PrimParam name typ FlowOut ftype inf ) = 
    maybe param 
    (\arg -> case arg of
          ArgVar name' _ _ _ _ -> PrimParam name' typ FlowOut ftype inf
          _ -> param) $
    Map.lookup name subst
renameParam _ param = param


singleCaller :: ProcDef -> Bool
singleCaller def =
    let m = procCallers def
    in  Map.size m == 1 && (snd . Map.findMin) m == 1


-- |Log a message, if we are logging unbrancher activity.
logExpansion :: String -> Expander ()
logExpansion s = lift $ lift $ logMsg Expansion s
