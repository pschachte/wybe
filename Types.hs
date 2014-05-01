--  File     : Types.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

-- |Support for type checking/inference.
module Types (typeCheckModSCC) where

import AST
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.State
import Data.Maybe
import Data.Graph


-- |The reason a variable is given a certain type
data TypeReason = ReasonParam Int                  -- Specified param
                | ReasonCallArg (Placed Prim) Int  -- Specified call arg 
                deriving (Show,Eq)

data Typing = ValidTyping (Map VarName (TypeSpec,TypeReason))
            | InvalidTyping TypeReason TypeReason   -- conflicting uses
            deriving (Show,Eq)

initTyping :: Typing
initTyping = ValidTyping Map.empty


validTyping :: Typing -> Bool
validTyping (ValidTyping _) = True
validTyping (InvalidTyping _ _) = False


addOneType :: TypeReason -> PrimVarName -> TypeSpec -> Typing -> Typing
addOneType _ (PrimVarName name _) typ invalid@(InvalidTyping _ _) = invalid
addOneType reason (PrimVarName name _) typ valid@(ValidTyping types) =
    case Map.lookup name types of
        Nothing -> ValidTyping $ Map.insert name (typ,reason) types
        Just (oldTyp,oldReason) ->
            if typ == oldTyp 
            then valid
            else if typ `properSubtypeOf` oldTyp
                 then ValidTyping $ Map.insert name (typ,reason) types
                 else if typ `properSubtypeOf` oldTyp
                      then valid
                      else InvalidTyping oldReason reason


-- |Returns the first argument restricted to the variables appearing 
--  in the second.
projectTyping :: Typing -> Typing -> Typing
projectTyping (ValidTyping typing) (ValidTyping interest) =
    ValidTyping $
    Map.filterWithKey (\k _ -> isJust $ Map.lookup k interest) typing
projectTyping typing _ = typing


-- Simple subtype relation for now; every type is a subtype of the 
-- unspecified type.
properSubtypeOf :: TypeSpec -> TypeSpec -> Bool
properSubtypeOf _ Unspecified = True
properSubtypeOf _ _ = False


-- |Type check a strongly connected component in the module dependency graph.
--  This code assumes that all lower sccs have already been checked.
typeCheckModSCC :: [ModSpec] -> Compiler ()
typeCheckModSCC [modspec] = do  -- immediate fixpoint when no mutual dependency
    typeCheckMod [modspec] modspec
    return ()
typeCheckModSCC scc = do        -- must find fixpoint
    changed <- mapM (typeCheckMod scc) scc
    when (or changed) $ typeCheckModSCC scc


-- |Type check a single module named in the second argument; the 
--  first argument is a list of all the modules in this module 
-- dependency SCC.
typeCheckMod :: [ModSpec] -> ModSpec -> Compiler Bool
typeCheckMod scc thisMod = do
    procs <- getSpecModule thisMod
            (Map.toList . modProcs . fromJust . modImplementation)
    let ordered =
            stronglyConnComp
            [((name,procs),name,nub
                                $ localCalledProcs thisMod
                                $ List.map content
                                $ concat
                                $ concat
                                $ List.map procBody procs) 
            | (name,procs) <- fromJust procs]
    changed <- mapM (typecheckProcSCC thisMod scc) ordered
    return $ or changed


-- |The list of procs in the current module called in the specified 
--  list of prims.  
localCalledProcs :: ModSpec -> [Prim] -> [Ident]
localCalledProcs _ [] = []
localCalledProcs thisMod (PrimCall Nothing name _ _:rest) =
    name:localCalledProcs thisMod rest
localCalledProcs thisMod (PrimCall (Just m) name _ _:rest)
  | m == thisMod = name:localCalledProcs thisMod rest
localCalledProcs thisMod (_:rest) = localCalledProcs thisMod rest


-- |Type check one strongly connected component in the local call graph
--  of a module.  The call graph contains only procs in the one module,
--  because this is being done for type inference, and imported procs
--  must have had their types declared.  Returns True if the inferred 
--  types are more specific than the old ones and some proc(s) in the 
--  SCC depend on procs in the list of mods.  In this case, we will 
--  have to rerun the typecheck after typechecking the other modules 
--  on that list. 
typecheckProcSCC :: ModSpec -> [ModSpec] -> SCC (Ident,[ProcDef]) ->
                    Compiler Bool
typecheckProcSCC m mods (AcyclicSCC (name,defs)) = do
    -- A single pass is always enough for non-cyclic SCCs
    liftIO $ putStrLn $ "Type checking non-recursive proc " ++ name
    (_,allAgain) <- typecheckProcDefs m mods name defs
    return allAgain
typecheckProcSCC m mods (CyclicSCC list) = do
    liftIO $ putStrLn $ "Type checking recursive procs " ++ 
      intercalate ", " (List.map fst list)
    (modAgain,allAgain) <- 
        foldM (\(modAgain,allAgain) (name,defs) -> do
                    (modAgain',allAgain') <- typecheckProcDefs m mods name defs
                    return (modAgain || modAgain', allAgain || allAgain'))
        (False, False) list
    if modAgain
      then typecheckProcSCC m mods $ CyclicSCC list
      else return allAgain


-- |Type check a list of procedure definitions and update the 
--  definitions stored in the Compiler monad.  Returns a pair of 
--  Bools, the first saying whether any defnition has been udpated, 
--  and the second saying whether any public defnition has been 
--  updated.
typecheckProcDefs :: ModSpec -> [ModSpec] -> ProcName -> [ProcDef] ->
                     Compiler (Bool,Bool)
typecheckProcDefs m mods name defs = do
    (revdefs,modAgain,allAgain) <- 
        foldM (\(ds,modAgain,allAgain) def -> do
                    (d,mA,aA) <- typecheckProcDef m mods def
                    return (d:ds,modAgain || mA,allAgain || aA))
        ([],False,False) defs
    when modAgain $
      updateModImplementation
      (\imp -> imp { modProcs = Map.insert name (reverse revdefs) 
                                $ modProcs imp })
    return (modAgain,allAgain)
    

-- |Type check a single procedure definition.
typecheckProcDef :: ModSpec -> [ModSpec] -> ProcDef ->
                    Compiler (ProcDef,Bool,Bool)
-- typecheckProcDef _ _ def = return def
typecheckProcDef m mods pd@(ProcDef name proto@(PrimProto pn params) 
                         def pos tmpCnt vis) 
  = do
    let typing = List.foldr addDeclaredType initTyping $ zip params [1..]
    if validTyping typing
      then do
        liftIO $ putStrLn $ "** Type checking " ++ name ++
          ": " ++ show typing
        (typing',def') <- typecheckBody m mods typing def
        liftIO $ putStrLn $ "*resulting types " ++ name ++
          ": " ++ show typing'
        let params' = updateParamTypes typing' params
        let modAgain = typing /= typing'
        liftIO $ putStrLn $ "** check again   " ++ name ++
          ": " ++ show modAgain
        return (ProcDef name (PrimProto pn params') def' pos tmpCnt vis,
                modAgain,modAgain && vis == Public)
      else
        shouldnt $ "Inconsistent param typing for proc " ++ name


addDeclaredType :: (PrimParam,Int) -> Typing -> Typing
addDeclaredType (PrimParam name typ _ _,argNum) typs =
     addOneType (ReasonParam argNum) name typ typs


updateParamTypes :: Typing -> [PrimParam] -> [PrimParam]
updateParamTypes (InvalidTyping _ _) params = params
updateParamTypes (ValidTyping dict) params =
    List.map (\p@(PrimParam name@(PrimVarName n _) typ fl afl) ->
               case Map.lookup n dict of
                   Nothing -> p
                   Just (newTyp,_) -> (PrimParam name newTyp fl afl)) params


    -- case alternatives of
    --     [] -> do
    --         if invalidTyping typing1
    --           then message Error ("type error in proc " ++ name) pos
    --           else message Error ("ambiguous type in definition of " ++ name) 
    --                pos
    --         return (pd,False,False)
    --     Just uniq -> do
    --         let (params',changed) = updateParamTypes uniq params
    --         return (ProcDef name (PrimProto pn params') def' pos tmpCnt vis,
    --                 changed,changed && vis==Public)

-- |Type check the body of a single proc definition by type checking 
--  each clause in turn using the declared parameter typing plus the 
--  typing of all parameters inferred from previous clauses.  We can 
--  stop once we've found a contradiction.
typecheckBody :: ModSpec -> [ModSpec] -> Typing -> [[Placed Prim]] -> 
                    Compiler (Typing,[[Placed Prim]])
typecheckBody m mods paramTypes body = do
    bodyTypes <- foldM (typecheckClause m mods) [(paramTypes,[])] body
    return (paramTypes,body)
    -- return (reconcileClauseTypes $ List.map fst pairs,List.map snd pairs)


-- |Type check a single clause starting with each possible parameter 
--  typing. 
typecheckClause :: ModSpec -> [ModSpec] -> [(Typing, [[Placed Prim]])] -> 
                   [Placed Prim] -> Compiler [(Typing,[[Placed Prim]])]
typecheckClause m mods possibles prims = do
    possibles' <- mapM (typecheckPrims m mods prims) possibles
    return $ concat possibles'


-- |Type all prims in a clause starting with one possible parameter 
--  typing and producing all possible typings and the corresponding 
--  clause body.  The clause is returned in reverse.
typecheckPrims :: ModSpec -> [ModSpec] -> [Placed Prim] ->
                  (Typing, [[Placed Prim]]) ->
                  Compiler [(Typing,[[Placed Prim]])]
typecheckPrims m mods clause (types,clauses) = do
    clauseTypes <- foldM (typecheckPlacedPrim m mods) [(types,[])] clause
    return $ List.map (\(clTyping,cl) ->
                        (projectTyping clTyping types, cl:clauses))
      clauseTypes

-- |Type check a single placed primitive operation given a list of 
--  possible starting typings and corresponding clauses up to this prim.
typecheckPlacedPrim :: ModSpec -> [ModSpec] -> [(Typing,[Placed Prim])] ->
                       Placed Prim -> Compiler [(Typing,[Placed Prim])]
typecheckPlacedPrim m mods possibilities pprim = do
    liftIO $ putStrLn $ "Type checking prim " ++ show pprim
    possposs <- mapM (typecheckPrim m mods (content pprim) (place pprim)) 
                possibilities
    return $ concat possposs
    

-- |Type check a single primitive operation, producing a list of 
--  possible typings and corresponding clauses.
typecheckPrim :: ModSpec -> [ModSpec] -> Prim -> OptPos ->
                 (Typing,[Placed Prim]) ->
                 Compiler [(Typing,[Placed Prim])]
typecheckPrim m mods prim pos (typing,body) = do
    possibilities <- typecheckSingle m mods prim pos typing
    return $ List.map (\(typing',prim') -> 
                        (typing',maybePlace prim' pos:body)) possibilities


-- |Type check one primitive operation, producing a list of 
--  possible typings and corresponding resolved primitives.
typecheckSingle :: ModSpec -> [ModSpec] -> Prim -> OptPos -> Typing ->
                 Compiler [(Typing,Prim)]
typecheckSingle m mods (PrimCall cm name id args) pos typing = do
    -- procs <- case id of
    --     Nothing -> do
    --         impl <- getModule (fromJust . modImplementation)
    --         callTargets impl cm name
    --     Just spec -> return [spec]
    return [(typing,PrimCall cm name id args)]
typecheckSingle _ _ (PrimForeign lang name id args) pos typing = do
    return [(typing,PrimForeign lang name id args)]
typecheckSingle m mods (PrimGuard body val) pos typing = do
    checked <- foldM (typecheckPlacedPrim m mods) [(typing,[])] body
    return $ List.map (\(ty,body') -> (ty,PrimGuard (reverse body') val))
      checked
typecheckSingle _ _ PrimFail pos typing = return [(typing,PrimFail)]
typecheckSingle _ _ PrimNop pos typing = return [(typing,PrimNop)]


argType :: Typing -> PrimArg -> TypeSpec
argType (ValidTyping dict) (ArgVar (PrimVarName var _) _ _) = 
    case Map.lookup var dict of
        Nothing -> Unspecified
        Just (typ,_) -> typ
argType (InvalidTyping _ _) (ArgVar _ _ _) = Unspecified
argType _ (ArgInt _) = TypeSpec "int" []
argType _ (ArgFloat _) = TypeSpec "float" []
argType _ (ArgString _) = TypeSpec "string" []
argType _ (ArgChar _) = TypeSpec "char" []

-- checkOrInferParamTypes :: Typing -> OptPos -> PrimProto 
--                          -> Compiler PrimProto
-- checkOrInferParamTypes dict pos (PrimProto name params) = do
--     params' <- mapM (checkOrInferParamType dict name pos) params
--     return $ PrimProto name params'

-- checkOrInferParamType :: Typing -> Ident -> OptPos -> Param 
--                         -> Compiler Param
-- checkOrInferParamType dict proc pos (Param var typ flow) = do
--     let typ' = Map.findWithDefault Unspecified var dict
--     -- XXX wrong test; must allow declared type to be more specific, but not 
--     -- more general, than actual type
--     typ'' <- meetTypes typ' typ
--     when (isNothing typ'' || typ' /= (fromJust typ''))
--       (message Error 
--        ("Type error in " ++ proc ++ ":  " 
--         ++ var ++ " declared " ++ show typ 
--         ++ " but actually " ++ show typ')
--        pos)
--     return $ Param var typ' flow

-- -- -- |Find all possibilities for the argument types for a proc.  
-- -- procTypes :: ModSpec -> Ident -> Maybe Int -> [PrimArg] -> Compiler [[Type]]
-- -- --  Specified proc is imported from a different module, and so 
-- -- --  its type is known (all exported procs must have types declared), 
-- -- --  or it is defined in the current module.  In the latter case, if 
-- -- --  its types are not declared and not yet inferred, we must do so now.  
-- -- procTypes thisMod name num args = do

-- -- |Find the most specific generalisation of two types.
-- meetTypes :: TypeSpec -> TypeSpec -> Compiler (Maybe TypeSpec)
-- meetTypes Unspecified typ = return $ Just typ
-- meetTypes typ Unspecified = return $ Just typ
-- meetTypes t1 t2 =
--     if t1 == t2 then 
--         return $ Just t1
--     else
--         return Nothing
