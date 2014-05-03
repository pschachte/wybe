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
data TypeReason = ReasonParam Int     -- Specified by param type/flow
                | ReasonArg OptPos ProcSpec Int
                                      -- Specified by call type/flow
                deriving (Eq)

instance Show TypeReason where
    show (ReasonParam num) = "Parameter " ++ show num
    show (ReasonArg pos pspec num) =
        makeMessage pos $
        "Argument " ++ show num ++ " of call to " ++ show pspec

data Typing = ValidTyping (Map VarName (TypeSpec,TypeReason))
            | InvalidTyping2 TypeReason TypeReason   -- conflicting var uses
            | InvalidTyping1 TypeReason              -- conflict w/callee
            deriving (Show,Eq)

initTyping :: Typing
initTyping = ValidTyping Map.empty


validTyping :: Typing -> Bool
validTyping (ValidTyping _) = True
validTyping _ = False


addOneType :: TypeReason -> PrimVarName -> TypeSpec -> Typing -> Typing
addOneType reason (PrimVarName name _) typ valid@(ValidTyping types) =
    case Map.lookup name types of
        Nothing -> ValidTyping $ Map.insert name (typ,reason) types
        Just (oldTyp,oldReason) ->
            if typ == oldTyp 
            then valid
            else if typ `properSubtypeOf` oldTyp
                 then ValidTyping $ Map.insert name (typ,reason) types
                 else InvalidTyping2 oldReason reason
addOneType _ _ _ invalid = invalid


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


subtypeOf :: TypeSpec -> TypeSpec -> Bool
subtypeOf sub super = sub == super || sub `properSubtypeOf` super


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
-- XXX must check submodules, too.
typeCheckMod :: [ModSpec] -> ModSpec -> Compiler Bool
typeCheckMod scc thisMod = do
    reenterModule thisMod
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
    exitModule
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
    -- liftIO $ putStrLn $ "Type checking non-recursive proc " ++ name
    (_,allAgain) <- typecheckProcDefs m mods name defs
    return allAgain
typecheckProcSCC m mods (CyclicSCC list) = do
    -- liftIO $ putStrLn $ "Type checking recursive procs " ++ 
    --   intercalate ", " (List.map fst list)
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
        -- liftIO $ putStrLn $ "** Type checking " ++ name ++
        --   ": " ++ show typing
        (typing',def') <- typecheckBody m mods typing def
        -- liftIO $ putStrLn $ "*resulting types " ++ name ++
        --   ": " ++ show typing'
        let params' = updateParamTypes typing' params
        let modAgain = typing /= typing'
        -- liftIO $ putStrLn $ "** check again   " ++ name ++
        --   ": " ++ show modAgain
        return (ProcDef name (PrimProto pn params') def' pos tmpCnt vis,
                modAgain,modAgain && vis == Public)
      else
        shouldnt $ "Inconsistent param typing for proc " ++ name


addDeclaredType :: (PrimParam,Int) -> Typing -> Typing
addDeclaredType (PrimParam name typ _ _,argNum) typs =
     addOneType (ReasonParam argNum) name typ typs


updateParamTypes :: Typing -> [PrimParam] -> [PrimParam]
updateParamTypes (ValidTyping dict) params =
    List.map (\p@(PrimParam name@(PrimVarName n _) typ fl afl) ->
               case Map.lookup n dict of
                   Nothing -> p
                   Just (newTyp,_) -> (PrimParam name newTyp fl afl)) params
updateParamTypes _ params = params


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
    -- liftIO $ putStrLn $ "Type checking prim " ++ show pprim
    possposs <- mapM (typecheckPrim m mods (content pprim) (place pprim)) 
                possibilities
    -- liftIO $ putStrLn $ "Done checking prim " ++ show pprim
    return $ concat possposs
    

-- |Type check a single primitive operation, producing a list of 
--  possible typings and corresponding clauses.
typecheckPrim :: ModSpec -> [ModSpec] -> Prim -> OptPos ->
                 (Typing,[Placed Prim]) ->
                 Compiler [(Typing,[Placed Prim])]
typecheckPrim m mods prim pos (typing,body) = do
    -- liftIO $ putStrLn $ "Type checking prim " ++ show prim
    -- liftIO $ putStrLn $ "   with types " ++ show typing
    possibilities <- typecheckSingle m mods prim pos typing
    return $ List.map (\(typing',prim') -> 
                        (typing',maybePlace prim' pos:body)) possibilities


-- |Type check one primitive operation, producing a list of 
--  possible typings and corresponding resolved primitives.
typecheckSingle :: ModSpec -> [ModSpec] -> Prim -> OptPos -> Typing ->
                 Compiler [(Typing,Prim)]
typecheckSingle m mods call@(PrimCall cm name id args) pos typing = do
    procs <- case id of
        Nothing   -> callTargets cm name
        Just spec -> return [spec]
    if List.null procs 
    then do
      -- message Error ("Call to unknown " ++ name) pos
      return [(typing,PrimCall cm name id args)]
    else do
      pairsList <- mapM (\p -> do
                           params <- getParams p
                           if length params == length args
                           then do
                             let typing' = List.foldr (typecheckArg pos p) 
                                           typing $ zip3 [1..] params args
                             return [(typing',PrimCall cm name (Just p) args)]
                           else
                               return [])
                   procs
      let pairs = concat pairsList
      let validPairs = List.filter (validTyping . fst) pairs
      if List.null validPairs 
      then do
        message Error ("Error in call:\n" ++ 
                       reportTypeErrors (List.map fst pairs)) pos
        return [(typing,PrimCall cm name id args)]
      else
          return validPairs
typecheckSingle _ _ (PrimForeign lang name id args) pos typing = do
    -- XXX must get type and flow from foreign calls
    return [(typing,PrimForeign lang name id args)]
typecheckSingle m mods (PrimGuard body val) pos typing = do
    checked <- foldM (typecheckPlacedPrim m mods) [(typing,[])] body
    return $ List.map (\(ty,body') -> (ty,PrimGuard (reverse body') val))
      checked
typecheckSingle _ _ PrimFail pos typing = return [(typing,PrimFail)]
typecheckSingle _ _ PrimNop pos typing = return [(typing,PrimNop)]


reportTypeErrors :: [Typing] -> String
reportTypeErrors reasons = intercalate "\n" $ List.map reportError reasons


reportError :: Typing -> String
reportError (InvalidTyping2 reason1 reason2) =
    "    " ++ show reason1 ++ " conflicts with\n     " ++ show reason2
reportError (InvalidTyping1 reason) =
    "    " ++ show reason ++ " conflicts with definition"
reportError _ = "NOT ACTUALLY A TYPE ERROR"


argType :: Typing -> PrimArg -> TypeSpec
argType (ValidTyping dict) (ArgVar (PrimVarName var _) _ _) = 
    case Map.lookup var dict of
        Nothing -> Unspecified
        Just (typ,_) -> typ
argType _ (ArgVar _ _ _) = Unspecified
argType _ (ArgInt _) = TypeSpec "int" []
argType _ (ArgFloat _) = TypeSpec "float" []
argType _ (ArgString _) = TypeSpec "string" []
argType _ (ArgChar _) = TypeSpec "char" []


typecheckArg :: OptPos -> ProcSpec -> (Int,PrimParam,PrimArg) ->
                Typing -> Typing
typecheckArg pos pspec (argNum,param,arg) typing =
    let actualFlow = argFlowDirection arg
        formalFlow = primParamFlow param
        reason = ReasonArg pos pspec argNum
    in  if not $ validTyping typing
        then typing
        else if formalFlow /= actualFlow
             then InvalidTyping1 reason
             else case arg of
                    ArgVar var _ _ ->
                        addOneType reason var (primParamType param) typing
                    _ ->
                        if (argType typing arg) `subtypeOf`
                               (primParamType param)
                        then typing
                        else InvalidTyping1 reason
