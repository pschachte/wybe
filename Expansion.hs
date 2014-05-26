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
    let tmp = procTmpCount def
    let outputs = List.map primParamName $
                  List.filter ((==FlowOut) . primParamFlow) $
                    primProtoParams proto
    (body',expander) <- runStateT (expandBody body) $
                          initExpanderState tmp $ Set.fromList outputs
    let proto' = proto { primProtoParams =
                              List.map (renameParam $ substitution expander) $
                              primProtoParams proto }
    let def' = def { procProto = proto', procBody = body', 
                     procTmpCount = tmpCount expander }
    -- liftIO $ putStrLn $
    --        "Expanded:\n" ++ showProcDef 4 def ++
    --                 "\nTo:\n" ++ showProcDef 4 def'
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


initExpanderState :: Int -> Set PrimVarName -> ExpanderState
initExpanderState tmpCount varSet = 
    Expander identitySubstitution varSet tmpCount


expandBody :: ProcBody -> Expander ProcBody
expandBody (ProcBody prims fork) = do
    prims' <- fmap concat $ mapM (placedApply expandPrim) prims
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


expandPrim :: Prim -> OptPos -> Expander [Placed Prim]
expandPrim call@(PrimCall md nm (Just pspec) args) pos = do
    -- liftIO $ putStrLn $ "Try to expand " ++ show call
    args' <- mapM expandArg args
    def <- lift $ getProcDef pspec
    prims <- if procInline def
             then do
                 -- liftIO $ putStrLn $ "Found expansion: " ++ show body
                 let subst = paramSubst (primProtoParams $ procProto def) args'
                 let body = procBody def
                 let bodyMap = bodyVars body
                 tmp <- gets tmpCount
                 let (tmp',subst') =
                         mapAccumWithKey
                         (\n v t -> (n+1,
                                     ArgVar (PrimVarName (mkTempName n) 0)
                                     t FlowIn Ordinary False))
                         tmp bodyMap
                 let subst'' = Map.union subst subst'
                 modify (\s -> s { tmpCount = tmp' })
                 return $ List.map (fmap (applySubst subst))
                            (bodyPrims $ procBody def)
             else return [maybePlace (PrimCall md nm (Just pspec) args') pos]

    primsList <- mapM (\p -> expandIfAssign (content p) p) prims
    return $ concat primsList
expandPrim (PrimForeign lang nm flags args) pos = do
    subst <- gets substitution
    return $ [maybePlace 
              (PrimForeign lang nm flags $ List.map (renameArg subst) args) 
              pos]
expandPrim prim pos = return $ [maybePlace prim pos]


-- |Record the substitution if the Prim is an assignment, and remove 
--  the assignment if permitted.  Assignments are turned into move 
--  primitives, because that's what they expand to, so that's what we 
--  look for here.
expandIfAssign :: Prim -> Placed Prim -> Expander [Placed Prim]
expandIfAssign (PrimForeign "llvm" "move" [] 
                [val, ArgVar var _ FlowOut _ _]) pprim = do
    modify (\s -> s { substitution = Map.insert var val $ substitution s })
    noSubst <- gets (Set.member var . protected)
    return $ if noSubst then [pprim] else []
expandIfAssign _ pprim = return [pprim]


expandArg :: PrimArg -> Expander PrimArg
expandArg arg@(ArgVar var _ _ _ _) = do
    gets (fromMaybe arg . Map.lookup var . substitution)
expandArg arg = return arg


paramSubst :: [PrimParam] -> [PrimArg] -> Substitution
paramSubst params args = 
    List.foldr (\(PrimParam k _ dir _ _,v) subst -> Map.insert k v subst)
    identitySubstitution $ zip params args
             

renameParam :: Substitution -> PrimParam -> PrimParam
renameParam subst param@(PrimParam name typ FlowOut ftype needed) = 
    maybe param 
    (\arg -> case arg of
          ArgVar name' _ _ _ _ -> PrimParam name' typ FlowOut ftype needed
          _ -> param) $
    Map.lookup name subst
renameParam _ param = param


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


bodyVars :: ProcBody -> Map PrimVarName TypeSpec
bodyVars body = mapBodyPrims primVars Map.union Map.empty
                Map.union Map.empty body


primVars :: Prim -> Map PrimVarName TypeSpec
primVars (PrimCall _ _ _ args) = argsVars args
primVars (PrimForeign _ _ _ args) = argsVars args
primVars (PrimNop) = Map.empty

argsVars :: [PrimArg] -> Map PrimVarName TypeSpec
argsVars = List.foldr (Map.union . argVars) Map.empty

argVars :: PrimArg -> Map PrimVarName TypeSpec
argVars (ArgVar name typ FlowOut _ _) = Map.singleton name typ
argVars _ = Map.empty
