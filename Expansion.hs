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

module Expansion (CallExpansion, identityExpansion, addExpansion,
                  Substitution, identitySubstitution,
                  ) where

import AST
import Data.Map as Map
import Data.List as List
import Data.Set as Set
import Data.Maybe
import Control.Monad.Trans.State

-- |Type to remember proc call expansions.  For each proc, we remember
-- the parameters of the call, to bind to the actual arguments, and
-- the body of the definition.  We also store a set of the variable
-- names used in the body, so that they can be renamed if necessary to
-- avoid variable capture.
type CallExpansion = Map ProcSpec ([PrimParam],[Placed Prim])


-- |A CallExpansion that doesn't expand anything
identityExpansion :: CallExpansion
identityExpansion = Map.empty


addExpansion :: ProcSpec -> [PrimParam] -> [Placed Prim] -> CallExpansion ->
                CallExpansion
addExpansion proc params body expn = Map.insert proc (params,body) expn

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


procExpansion :: CallExpansion -> Int -> ProcDef -> ProcDef
procExpansion expn id def = def { procProto = proto', procBody = body' }
  where
    body  = procBody def
    proto = procProto def
    outputs = List.map primParamName $
              List.filter ((==FlowOut) . primParamFlow) $
              primProtoParams proto
    (body',paramSubst) = evalState (expandBody body) $
                         initExpanderState expn $ Set.fromList outputs
    proto' = proto { primProtoParams =
                          List.map (renameParam paramSubst) $
                          primProtoParams proto }


----------------------------------------------------------------
--                       The Expansion Monad
----------------------------------------------------------------

data ExpanderState = Expander {
    substitution :: Substitution,     -- ^The current variable substitution
    expansion    :: CallExpansion,    -- ^The expansions in effect (read-only)
    protected    :: Set PrimVarName       -- ^Variables that cannot be renamed
    }


type Expander = State ExpanderState


initExpanderState :: CallExpansion -> Set PrimVarName -> ExpanderState
initExpanderState expn varSet = 
    Expander identitySubstitution expn varSet


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
    let pairs = List.map (\b -> evalState (expandBody b) state) bodies
    let bodies' = List.map fst pairs
    return (PrimFork var bodies',List.map snd pairs)


expandPrim :: Prim -> OptPos -> Expander [Placed Prim]
expandPrim asn@(PrimCall _ "=" _ [ArgVar var _ FlowOut _ _, val]) pos = do
    expandAssign var val $ maybePlace asn pos
expandPrim asn@(PrimCall _ "=" _ [val, ArgVar var _ FlowOut _ _]) pos = do
    expandAssign var val $ maybePlace asn pos
expandPrim (PrimCall md nm pspec args) pos = do
    args' <- mapM expandArg args
    expn <- gets expansion
    case pspec >>= flip Map.lookup expn of
        Nothing -> return [maybePlace (PrimCall md nm pspec args') pos]
        Just (params,body) -> 
            return $ List.map (fmap (applySubst $ paramSubst params args')) body
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
    noSubst <- gets (Set.member var . protected)
    if noSubst 
      then return arg
      else gets (fromMaybe arg . Map.lookup var . substitution)


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
renameArg subst var@(ArgVar name _ FlowIn _ _) =
    fromMaybe var $ Map.lookup name subst
renameArg subst primArg = primArg
