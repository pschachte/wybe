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
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.Trans.State

import Debug.Trace

procExpansion :: ProcDef -> Compiler ProcDef
procExpansion def = do
    let body  = procBody def
    let proto = procProto def
    let outputs = List.map primParamName $
                  List.filter ((==FlowOut) . primParamFlow) $
                    primProtoParams proto
    (body',paramSubst) <- evalStateT (expandBody body) $
                          initExpanderState $ Set.fromList outputs
    let proto' = proto { primProtoParams =
                             List.map (renameParam paramSubst) $
                                 primProtoParams proto }
    return $ def { procProto = proto', procBody = body' }



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
    protected    :: Set PrimVarName   -- ^Variables that cannot be renamed
    }


type Expander = StateT ExpanderState Compiler


initExpanderState :: Set PrimVarName -> ExpanderState
initExpanderState varSet = Expander identitySubstitution varSet


expandBody :: ProcBody -> Expander (ProcBody,Substitution)
expandBody (ProcBody prims fork) = do
    prims' <- fmap concat $ mapM (placedApply expandPrim) prims
    (fork',substs) <- expandFork fork
    state <- get
    let baseSubst = projectSubst (protected state) (substitution state)
    let subst = List.foldr meetSubsts baseSubst substs
    return (ProcBody prims' fork', subst)
                                

expandFork :: PrimFork -> Expander (PrimFork,[Substitution])
expandFork NoFork = return (NoFork,[])
expandFork (PrimFork var bodies) = do
    state <- get
    pairs <- lift $ mapM (\b -> evalStateT (expandBody b) state) bodies
    let bodies' = List.map fst pairs
    return (PrimFork var bodies',List.map snd pairs)


expandPrim :: Prim -> OptPos -> Expander [Placed Prim]
expandPrim call@(PrimCall md nm pspec args) pos = do
    -- liftIO $ putStrLn $ "Try to expand " ++ show call
    args' <- mapM expandArg args
    case (nm,args') of  -- special case handling of assignment
      ("=",[ArgVar var _ FlowOut _ _, val]) ->
          expandAssign var val $ maybePlace call pos
      ("=",[val, ArgVar var _ FlowOut _ _]) ->
          expandAssign var val $ maybePlace call pos
      _ -> do
        expn <- lift $ gets expansion
        case pspec >>= flip Map.lookup expn of
          Nothing -> return [maybePlace (PrimCall md nm pspec args') pos]
          Just (params,body) -> do
              -- liftIO $ putStrLn $ "Found expansion: " ++ show body
              return $ List.map (fmap (applySubst $ paramSubst params args'))
                     body
expandPrim (PrimForeign lang nm flags args) pos = do
    subst <- gets substitution
    return $ [maybePlace 
              (PrimForeign lang nm flags $ List.map (renameArg subst) args) 
              pos]
expandPrim PrimNop pos = return $ [maybePlace PrimNop pos]


expandAssign :: PrimVarName -> PrimArg -> Placed Prim -> Expander [Placed Prim]
expandAssign var val pprim = do
    modify (\s -> s { substitution = Map.insert var val $ substitution s })
    noSubst <- gets (Set.member var . protected)
    return $ if noSubst then [pprim] else []


expandArg :: PrimArg -> Expander PrimArg
expandArg arg@(ArgVar var _ _ _ _) = do
    gets (fromMaybe arg . Map.lookup var . substitution)
-- XXX Is this the right code:
-- expandArg arg@(ArgVar var _ _ _ _) = do
--     noSubst <- gets (Set.member var . protected)
--     if noSubst 
--       then return arg
--       else gets (fromMaybe arg . Map.lookup var . substitution)
expandArg arg = return arg


paramSubst :: [PrimParam] -> [PrimArg] -> Substitution
paramSubst params args = 
    List.foldr (\(PrimParam k _ dir _,v) subst -> Map.insert k v subst)
    identitySubstitution $ zip params args
             
               


renameParam :: Substitution -> PrimParam -> PrimParam
renameParam subst param@(PrimParam name typ dir ftype) = 
    maybe param 
    (\arg -> case arg of
          ArgVar name' _ _ _ _ -> PrimParam name' typ dir ftype
          _ -> param) $
    Map.lookup name subst

applySubst :: Substitution -> Prim -> Prim
applySubst subst (PrimCall md nm pspec args) =
    PrimCall md nm pspec $ List.map (renameArg subst) args
applySubst subst (PrimForeign lang nm flags args) =
    PrimForeign lang nm flags $ List.map (renameArg subst) args
applySubst subst PrimNop = PrimNop


renameArg :: Substitution -> PrimArg -> PrimArg
renameArg subst var@(ArgVar name _ flow _ _) =
    maybe var (setPrimArgFlow flow) $ Map.lookup name subst
renameArg subst primArg = primArg

setPrimArgFlow :: PrimFlow -> PrimArg -> PrimArg
setPrimArgFlow flow (ArgVar n t _ ft lst) = (ArgVar n t flow ft lst)
setPrimArgFlow FlowIn arg = arg
setPrimArgFlow FlowOut arg = 
    shouldnt $ "trying to make " ++ show arg ++ " an output argument"
