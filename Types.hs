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

type VarTypes = Map VarName TypeSpec

-- |Type check a strongly connected component in the module dependency graph.
--  This code assumes that all lower sccs have already been checked.
typeCheckModSCC :: [ModSpec] -> Compiler ()
typeCheckModSCC scc = do
    mapM_ (typeCheckMod scc) scc

-- |Type check a single module named in the second argument; the 
--  first argument is a list of all the modules in this module 
-- dependency SCC.
typeCheckMod :: [ModSpec] -> ModSpec -> Compiler ()
typeCheckMod scc modspec = do
    procs <- getSpecModule modspec 
            (Map.toList . modProcs . fromJust . modImplementation)
    let ordered =
            stronglyConnComp
            [((name,procs),name,localCalledProcs 
                                $ List.map content
                                $ concat
                                $ List.map procBody procs) 
            | (name,procs) <- fromJust procs]
    mapM_ (typecheckProcSCC modspec) ordered


-- |The list of procs in the current module called in the specified 
--  list of prims.  
--  XXX Looks like it collects non-local called procs, too.
localCalledProcs :: [Prim] -> [Ident]
localCalledProcs [] = []
localCalledProcs (PrimCall name _ _:rest) = name:localCalledProcs rest
localCalledProcs (PrimCond _ cases:rest) = 
    (concat $ List.map (localCalledProcs . List.map content) cases) 
    ++ localCalledProcs rest
localCalledProcs (PrimLoop body:rest) = 
    (localCalledProcs $ List.map content body) ++ localCalledProcs rest
localCalledProcs (_:rest) = localCalledProcs rest

-- |Type check one strongly connected component in the local call graph
--  of a module.  The call graph contains only procs in the one module,
--  because this is being done for type inference, and imported procs
--  must have had their types declared.
typecheckProcSCC :: ModSpec -> SCC (Ident,[ProcDef]) -> Compiler ()
typecheckProcSCC m (AcyclicSCC (name,defs)) = do
    -- A single pass is always enough for non-cyclic SCCs
    defs' <- mapM (typecheckProcDef m) defs
    updateModImplementation
      (\imp -> imp { modProcs = Map.insert name defs' $ modProcs imp })
typecheckProcSCC m (CyclicSCC list) = do
    list' <- mapM (\(name,defs) -> do
                       defs' <- mapM (typecheckProcDef m) defs
                       return (name,defs')) list
    updateModImplementation
      (\imp -> 
        imp { modProcs = 
                   List.foldl (\m (name,defs') -> Map.insert name defs' m)
                   (modProcs imp) list' })
    unless (list' == list) $
      typecheckProcSCC m $ CyclicSCC list'

-- |Type check a single procedure definition.
typecheckProcDef :: ModSpec -> ProcDef -> Compiler ProcDef
typecheckProcDef _ def = return def
-- typecheckProcDef m (ProcDef name proto@(ProcProto pn params) def pos) = do
--     posses <- typecheckPrims m Map.empty def
--     case posses of
--         [] -> error $ "type error in proc " ++ name
--         [(dict,def')] -> do
--             proto' <- checkOrInferParamTypes dict pos proto
--             return $ ProcDef name proto' def' pos
--         _ -> error $ "ambiguous type in proc " ++ name

-- typecheckPrims :: ModSpec -> VarTypes -> [Placed Prim] -> 
--                  Compiler [(VarTypes,[Placed Prim])]
-- typecheckPrims _ dict [] = return [(dict,[])]
-- typecheckPrims m dict (p:ps) = do
--     posses <- typecheckPlacedPrim m dict p
--     posses' <- mapM (typeCheckPrimsRest m ps) posses
--     return $ concat posses'

-- -- |Type check a single primitive operation.
-- typecheckPlacedPrim :: ModSpec -> VarTypes -> Placed Prim -> 
--                        Compiler [(VarTypes,Placed Prim)]
-- typecheckPlacedPrim m dict pprim = do
--     unplaced <- typecheckPrim m dict (content pprim)
--     return $ [(d,maybePlace p (place pprim)) | (d,p) <- unplaced]

-- typeCheckPrimsRest :: ModSpec -> [Placed Prim] -> (VarTypes,Placed Prim) ->
--                  Compiler [(VarTypes,[Placed Prim])]
-- typeCheckPrimsRest m ps (dict,p') = do
--     posses <- typecheckPrims m dict ps
--     return $ [(d,p':ps') | (d,ps') <- posses]

-- -- |Type check a single primitive operation.
-- typecheckPrim :: ModSpec -> VarTypes -> Prim -> Compiler [(VarTypes,Prim)]
-- typecheckPrim m dict (PrimCall name id args) = do
--     let argtypes = List.map (argType dict) args
-- --    procs <- matchingProcs m name
--     return [(dict,PrimCall name id args)]
-- typecheckPrim _ dict (PrimForeign lang name id args) = do
--     return [(dict,PrimForeign lang name id args)]
-- typecheckPrim m dict (PrimCond var primslist) = do
-- --    addTypeConstraint var $ TypeSpec "Bool" []
--     primspairlist <- typecheckPrimsList m dict primslist
--     return [(dict',PrimCond var primslist') 
--            | (dict',primslist') <- primspairlist]
-- typecheckPrim m dict (PrimLoop prims) = do
--     prims' <- typecheckPrims m dict prims
--     return [(d,PrimLoop ps) | (d,ps)<-prims']
-- typecheckPrim _ dict (PrimBreakIf var) = do
-- --    addTypeConstraint var $ TypeSpec "Bool" []
--     return [(dict,PrimBreakIf var)]
-- typecheckPrim _ dict (PrimNextIf var) = do
-- --    addTypeConstraint var $ TypeSpec "Bool" []
--     return [(dict,PrimNextIf var)]

-- typecheckPrimsList :: ModSpec -> VarTypes -> [[Placed Prim]] ->
--                      Compiler [[(VarTypes,[Placed Prim])]]
-- typecheckPrimsList _ dict [] = return []
-- typecheckPrimsList m dict (arm:arms) = do
--     checked <- typecheckPrims m dict arm
--     checkedtail <- typecheckPrimsList m dict arms
--     return $ checked:checkedtail

-- argType :: VarTypes -> PrimArg -> TypeSpec
-- argType dict (ArgVar var _) = Map.findWithDefault Unspecified var dict
-- argType _ (ArgInt _) = TypeSpec "int" []
-- argType _ (ArgFloat _) = TypeSpec "float" []
-- argType _ (ArgString _) = TypeSpec "string" []
-- argType _ (ArgChar _) = TypeSpec "char" []

-- checkOrInferParamTypes :: VarTypes -> OptPos -> ProcProto 
--                          -> Compiler ProcProto
-- checkOrInferParamTypes dict pos (ProcProto name params) = do
--     params' <- mapM (checkOrInferParamType dict name pos) params
--     return $ ProcProto name params'

-- checkOrInferParamType :: VarTypes -> Ident -> OptPos -> Param 
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
