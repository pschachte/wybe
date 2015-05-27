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
    let outputs = List.map primParamName $
                  List.filter ((==FlowOut) . primParamFlow) $
                    primProtoParams proto
    (expander,body') <- buildBody $ execStateT (expandBody body) $
                          initExpanderState tmp $ Set.fromList outputs
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


addSubstitution :: PrimVarName -> PrimArg -> Substitution -> Substitution
addSubstitution = Map.insert


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
    doInline     :: Bool,             -- ^Whether to inline code
    doInlineFork :: Bool              -- ^Whether to inline the finalFork
    }


type Expander = StateT ExpanderState BodyBuilder


tmpVar :: Expander PrimVarName
tmpVar = do
    tmp <- gets tmpCount
    modify (\s -> s { tmpCount = tmp+1 })
    return $ PrimVarName (mkTempName tmp) 0


addSubst :: PrimVarName -> PrimArg -> Expander ()
addSubst var val = do
    modify (\s -> s { substitution = Map.insert var val $ substitution s })
    return ()


addInstr :: Prim -> OptPos -> Expander ()
addInstr (PrimForeign "llvm" "move" [] 
          [val, argvar]) pos = do
    val' <- expandArg val
    argvar'@(ArgVar var _ flow _ _) <- expandArg argvar
    unless (flow == FlowOut) $
      shouldnt "move instruction with wrong mode"
    addSubst var val'
    noSubst <- gets (Set.member var . protected)
    logExpansion $ "  Expanding move(" ++ show val' ++ ", ?" ++ show var 
      ++ "); protected = " ++ show noSubst
    state <- get
    logExpansion $ "    subst = " ++ show (substitution state)
    logExpansion $ "    prot  = " ++ show (protected state)
    if noSubst -- do we need to keep this assignment (to an output)?
      then lift $ instr $ maybePlace 
           (PrimForeign "llvm" "move" [] [val', argvar'])  
           pos
      else return ()
addInstr (PrimForeign lang nm flags args) pos = do
    args' <- mapM expandArg args
    lift $ instr $ maybePlace (PrimForeign lang nm flags args')  pos
addInstr (PrimCall pspec args) pos = do
    args' <- mapM expandArg args
    lift $ instr $ maybePlace (PrimCall pspec args')  pos
addInstr PrimNop _ = do
    -- Filter out NOPs
    return ()


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
    Expander identitySubstitution varSet tmpCount NoFork True True


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
          (if doInlineFork state then "WITH" else "without") ++ " inlining)"
        let var' = case Map.lookup var $ substitution state of
              Nothing -> var
              Just (ArgVar v _ _ _ _) -> v 
              Just _ -> shouldnt "expansion led to non-var conditional"
        let state' = state { doInline = doInlineFork state, finalFork = NoFork }
        pairs <- lift $ mapM (\b -> runStateT (expandBody b) state') bodies
        logExpansion $ "Finished expanding fork"
        -- Don't actually need this:
        -- let baseSubst = projectSubst (protected state) (substitution state)
        -- let subst = List.foldr meetSubsts baseSubst $
        --             List.map (substitution . snd) pairs
        return ()

                                
expandPrims :: [Placed Prim] -> Expander ()
expandPrims pprims = do
    mapM_ (\(p:rest) -> expandPrim (content p) (place p) (List.null rest))
      $ init $ tails pprims


expandPrim :: Prim -> OptPos -> Bool -> Expander ()
expandPrim call@(PrimCall pspec args) pos last = do
    doInline <- gets doInline
    logExpansion $
      (if doInline then "  Try to inline " else "  Expanding ") ++ "call " ++ show call
    def <- lift $ lift $ getProcDef pspec
    inlinableLast <- gets (((last && singleCaller def && 
                             procVis def == Private) &&) . (== NoFork) . finalFork)

    -- addInstr call pos

    if doInline && ( procInline def || inlinableLast)
    then do
        let ProcDefPrim proto body = procImpln def
        let thisFork = bodyFork body
        when inlinableLast $ do
          insertFinalFork thisFork
          modify (\s -> s { doInlineFork = False })
        saved <- get
        modify (\s -> s { substitution = identitySubstitution, 
                          protected = Set.empty, 
                          doInline = False })
        mapM_ addParamSubst $ zip (primProtoParams proto) args
        logExpansion $ "  Inlining defn: " ++ showBlock 4 body
        expandPrims $ bodyPrims body
        tmp' <- gets tmpCount
        put saved
        modify (\s -> s { tmpCount = tmp' })
        -- Record that it is being inlined
        -- XXX this doesn't work:
        -- lift $ updateProcDef (\d -> d {procInline = True}) pspec
        -- logExpansion $ "  After subst:" ++
        --   showBlock 4 (ProcBody defPrims' NoFork)
    else do
      when doInline $ logExpansion $ "  Cannot inline."
      addInstr call pos
expandPrim prim pos _ = do
    addInstr prim pos


-- |Record the substitution if the Prim is an assignment, and remove 
--  the assignment if permitted.  Assignments are turned into move 
--  primitives, because that's what they expand to, so that's what we 
--  look for here.
expandIfAssign :: Prim -> Placed Prim -> Expander [Placed Prim]
expandIfAssign (PrimForeign "llvm" "move" [] 
                [val, ArgVar var _ FlowOut _ _]) pprim = do
    addSubst var val
    noSubst <- gets (Set.member var . protected)
    return $ if noSubst then [pprim] else []
expandIfAssign _ pprim = return [pprim]


expandArg :: PrimArg -> Expander PrimArg
expandArg arg@(ArgVar var typ flow ftype _) = do
    -- logExpansion $ "expanding " ++ show arg
    renameAll <- gets (not . doInline)
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
    shouldnt $ "trying to make " ++ show arg ++ " an output argument"


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
