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

module Expansion (procExpansion) where

import AST
import Data.Map as Map
import Data.List as List
import Data.Set as Set
import Data.Maybe
import Control.Monad
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.Trans.State

import Debug.Trace

procExpansion :: ProcDef -> Compiler ProcDef
procExpansion def = do
    let ProcDefPrim proto body  = procImpln def
    let tmp = procTmpCount def
    let outputs = List.map primParamName $
                  List.filter ((==FlowOut) . primParamFlow) $
                    primProtoParams proto
    (body',expander) <- runStateT (expandBody body) $
                          initExpanderState tmp $ Set.fromList outputs
    let proto' = proto { primProtoParams =
                              List.map (renameParam $ substitution expander) $
                              primProtoParams proto }
    let def' = def { procImpln = ProcDefPrim proto' body',
                     procTmpCount = tmpCount expander }
    -- liftIO $ putStrLn $
    --        "\nExpanded:" ++ showProcDef 4 def ++
    --                 "\nTo:" ++ showProcDef 4 def'
    return def'



-- |Type to remember the variable renamings.  A variable that maps to 
--  Nothing is not permitted to be renamed, because it is a parameter. 
type Substitution = Map PrimVarName PrimArg


-- |A Substitution that doesn't substitute anything
identitySubstitution :: Substitution
identitySubstitution = Map.empty


addSubstitution :: PrimVarName -> PrimArg -> Substitution -> Substitution
addSubstitution = Map.insert


meetSubsts :: Substitution -> Substitution -> Substitution
meetSubsts = Map.mergeWithKey
             (\k v1 v2 -> if v1 == v2 then Just v1 else Nothing)
             (const Map.empty) 
             (const Map.empty) 


projectSubst :: Set PrimVarName -> Substitution -> Substitution
projectSubst protected subst = 
    Map.fromAscList $
    List.filter (flip Set.member protected . fst) $
    Map.toAscList subst


----------------------------------------------------------------
--                       The Expansion Monad
----------------------------------------------------------------

data ExpanderState = Expander {
    substitution :: Substitution,     -- ^The current variable substitution
    protected    :: Set PrimVarName,  -- ^Variables that cannot be renamed
    tmpCount     :: Int               -- ^Next available tmp variable number
    }


type Expander = StateT ExpanderState Compiler


tmpVar :: Expander PrimVarName
tmpVar = do
    tmp <- gets tmpCount
    modify (\s -> s { tmpCount = tmp+1 })
    return $ PrimVarName (mkTempName tmp) 0


addSubst :: PrimVarName -> PrimArg -> Expander ()
addSubst var val = do
    modify (\s -> s { substitution = Map.insert var val $ substitution s })
    return ()


initExpanderState :: Int -> Set PrimVarName -> ExpanderState
initExpanderState tmpCount varSet = 
    Expander identitySubstitution varSet tmpCount


expandBody :: ProcBody -> Expander ProcBody
expandBody (ProcBody prims fork) = do
    prims' <- expandPrims False False prims
    fork' <- expandFork fork
    return $ ProcBody prims' fork'
                                

expandFork :: PrimFork -> Expander PrimFork
expandFork NoFork = return NoFork
expandFork (PrimFork var last bodies) = do
    state <- get
    let baseSubst = projectSubst (protected state) (substitution state)
    pairs <- lift $ mapM (\b -> runStateT (expandBody b) state) bodies
    let subst = List.foldr meetSubsts baseSubst $
                List.map (substitution . snd) pairs
    modify (\s -> s { substitution = subst })
    return $ PrimFork var last $ List.map fst pairs


expandPrims :: Bool -> Bool -> [Placed Prim] -> Expander [Placed Prim]
expandPrims noInline renameAll pprims = do
    fmap concat $ mapM (placedApply (expandPrim noInline renameAll)) pprims


expandPrim :: Bool -> Bool -> Prim -> OptPos -> Expander [Placed Prim]
expandPrim noInline renameAll call@(PrimCall pspec args) pos = do
    -- liftIO $ putStrLn $ "Try to expand " ++ 
    --   (if noInline then "" else "and inline ") ++ show call
    args' <- mapM (expandArg renameAll) args
    def <- lift $ getProcDef pspec
    -- liftIO $ putStrLn $ "Definition:" ++ showProcDef 4 def
    prims <- if (not noInline) && procInline def
             then do
                 saved <- get
                 modify (\s -> s { substitution = identitySubstitution, 
                                   protected = Set.empty })
                 let ProcDefPrim proto body = procImpln def
                 mapM_ addParamSubst $ zip (primProtoParams proto) args'
                 unless (NoFork == bodyFork body) $
                   shouldnt $ "Inlined proc with non-empty fork" ++
                              show pspec
                 -- liftIO $ putStrLn $ "Found expansion: " ++ showBlock 4 body
                 let defPrims = bodyPrims body
                 defPrims' <- expandPrims True True defPrims
                 tmp' <- gets tmpCount
                 put saved
                 modify (\s -> s { tmpCount = tmp' })
                 -- liftIO $ putStrLn $ "After subst " ++
                 --   showBlock 4 (ProcBody defPrims' NoFork)
                 return defPrims'
             else return [maybePlace (PrimCall pspec args') pos]
    primsList <- mapM (\p -> expandIfAssign (content p) p) prims
    return $ concat primsList
expandPrim _ renameAll (PrimForeign lang nm flags args) pos = do
    subst <- gets substitution
    args' <- mapM (expandArg renameAll) args
    return $ [maybePlace (PrimForeign lang nm flags args') pos]
expandPrim _ _ prim pos = return $ [maybePlace prim pos]


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


expandArg :: Bool -> PrimArg -> Expander PrimArg
expandArg renameAll arg@(ArgVar var typ flow ftype _) = do
    -- liftIO $ putStr $ "  expanding " ++ show arg
    maybeArg <- gets (Map.lookup var . substitution)
    arg' <- case (maybeArg,renameAll,flow) of
        (Just a,_,_) -> do return $ setPrimArgFlow flow ftype a
        (Nothing,False,_) -> return arg
        (Nothing,True,FlowIn) -> 
            shouldnt $ "variable " ++ show var ++ " used before defined"
        (Nothing,True,FlowOut) -> do
            freshVar <- tmpVar
            addSubst var $ ArgVar freshVar typ FlowIn ftype False
            return $ ArgVar freshVar typ FlowOut ftype False
    -- liftIO $ putStrLn $ " to " ++ show arg'
    return arg'
expandArg _ arg = return arg


setPrimArgFlow :: PrimFlow -> ArgFlowType -> PrimArg -> PrimArg
setPrimArgFlow flow ftype (ArgVar n t _ _ lst) = (ArgVar n t flow ftype lst)
setPrimArgFlow FlowIn _ arg = arg
setPrimArgFlow FlowOut _ arg = 
    shouldnt $ "trying to make " ++ show arg ++ " an output argument"


addParamSubst :: (PrimParam,PrimArg) -> Expander ()
addParamSubst param@(PrimParam k ty dir _,v) = do
    when (Unspecified == ty) $
      liftIO $ putStrLn $ "Danger: untyped param: " ++ show param
    when (Unspecified == argType v) $
      liftIO $ putStrLn $ "Danger: untyped argument: " ++ show v
    addSubst k v
             

renameParam :: Substitution -> PrimParam -> PrimParam
renameParam subst param@(PrimParam name typ FlowOut ftype) = 
    maybe param 
    (\arg -> case arg of
          ArgVar name' _ _ _ _ -> PrimParam name' typ FlowOut ftype
          _ -> param) $
    Map.lookup name subst
renameParam _ param = param
