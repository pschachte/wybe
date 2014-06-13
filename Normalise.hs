--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Convert parse tree into AST
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

-- |Support for normalising wybe code as parsed to a simpler form
--  to make compiling easier.
module Normalise (normalise) where

import AST
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Maybe
import Text.ParserCombinators.Parsec.Pos
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans (lift,liftIO)
import Flatten
import Unbranch


-- |Normalise a list of file items, storing the results in the current module.
normalise :: ([ModSpec] -> Compiler ()) -> [Item] -> Compiler ()
normalise modCompiler items = do
    mapM_ (normaliseItem modCompiler) items
    -- liftIO $ putStrLn "File compiled"
    -- every module imports stdlib
    addImport ["wybe"] (ImportSpec (Just Set.empty) Nothing)
    -- Now generate main proc if needed
    stmts <- getModule stmtDecls 
    unless (List.null stmts)
      $ normaliseItem modCompiler 
            (ProcDecl Private (ProcProto "" [] initResources) 
                          (List.reverse stmts) Nothing)

-- |The resources available at the top level
-- XXX this should be all resources with initial values
initResources :: [ResourceFlowSpec]
-- initResources = [ResourceFlowSpec (ResourceSpec ["wybe"] "io") ParamInOut]
initResources = [ResourceFlowSpec (ResourceSpec ["wybe","io"] "io") ParamInOut]


-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: ([ModSpec] -> Compiler ()) -> Item -> Compiler ()
normaliseItem modCompiler (TypeDecl vis (TypeProto name params) items pos) = do
    addType name (TypeDef (length params) pos) vis
    let ty = TypeSpec [] name []
    let eq1 = ProcDecl Public
              (ProcProto "=" [Param "x" ty ParamOut Ordinary,
                              Param "y" ty ParamIn Ordinary] [])
              [Unplaced $
               ForeignCall "llvm" "move" [] [Unplaced $
                                             Var "y" ParamIn Ordinary,
                                             Unplaced $
                                             Var "x" ParamOut Ordinary]]
              Nothing
    let eq2 = ProcDecl Public
              (ProcProto "=" [Param "y" ty ParamIn Ordinary,
                              Param "x" ty ParamOut Ordinary] [])
              [Unplaced $
               ForeignCall "llvm" "move" [] [Unplaced $
                                             Var "y" ParamIn Ordinary,
                                             Unplaced $
                                             Var "x" ParamOut Ordinary]]
              Nothing
    normaliseSubmodule modCompiler name (Just params) vis pos (eq1:eq2:items)
normaliseItem modCompiler (ModuleDecl vis name items pos) = do
    normaliseSubmodule modCompiler name Nothing vis pos items
normaliseItem _ (ImportMods vis modspecs pos) = do
    mapM_ (\spec -> addImport spec (importSpec Nothing vis)) modspecs
normaliseItem _ (ImportItems vis modspec imports pos) = do
    addImport modspec (importSpec (Just imports) vis)
normaliseItem _ (ResourceDecl vis name typ init pos) =
  addSimpleResource name (SimpleResource typ init pos) vis
normaliseItem modCompiler (FuncDecl vis (FnProto name params resources) 
               resulttype result pos) =
  let flowType = Implicit pos
  in  normaliseItem modCompiler
   (ProcDecl
    vis
    (ProcProto name (params ++ [Param "$" resulttype ParamOut flowType]) 
     resources)
    [maybePlace (ProcCall [] "=" [Unplaced $ Var "$" ParamOut flowType, result])
     pos]
    pos)
normaliseItem _ decl@(ProcDecl _ _ _ _) = do
    (ProcDecl vis proto@(ProcProto _ params resources) stmts pos,tmpCtr) <- 
        flattenProcDecl decl
    -- (proto' <- flattenProto proto
    -- (stmts,tmpCtr) <- flattenBody stmts
    -- liftIO $ putStrLn $ "Flattened proc:\n" ++ show (ProcDecl vis proto' stmts pos)
    (stmts',genProcs) <- unbranchBody params resources stmts
    mainProc <- compileProc tmpCtr $ ProcDecl vis proto stmts' pos
    auxProcs <- mapM (compileProc tmpCtr) genProcs
    addProc mainProc auxProcs
normaliseItem modCompiler (CtorDecl vis proto pos) = do
    modspec <- getModuleSpec
    Just modparams <- getModuleParams
    addCtor modCompiler vis (last modspec) modparams proto pos
normaliseItem _ (StmtDecl stmt pos) = do
    updateModule (\s -> s { stmtDecls = maybePlace stmt pos : stmtDecls s})


normaliseSubmodule :: ([ModSpec] -> Compiler ()) -> Ident -> 
                      Maybe [Ident] -> Visibility -> OptPos -> 
                      [Item] -> Compiler ()
normaliseSubmodule modCompiler name typeParams vis pos items = do
    dir <- getDirectory
    parentModSpec <- getModuleSpec
    let subModSpec = parentModSpec ++ [name]
    addImport subModSpec (importSpec Nothing vis)
    enterModule dir subModSpec typeParams
    normalise modCompiler items
    mods <- exitModule
    unless (List.null mods) $ modCompiler mods
    return ()


-- |Add a contructor for the specified type.
addCtor :: ([ModSpec] -> Compiler ()) -> Visibility -> Ident -> [Ident] ->
           FnProto -> OptPos -> Compiler ()
addCtor modCompiler vis typeName typeParams (FnProto ctorName params _) pos = do
    let typespec = TypeSpec [] typeName $ 
                   List.map (\n->TypeSpec [] n []) typeParams
    let flowType = Implicit pos
    normaliseItem modCompiler
      (FuncDecl Public (FnProto ctorName params []) typespec
       (Unplaced $ Where
        ([Unplaced $ ForeignCall "$" "alloc" []
          [Unplaced $ StringValue typeName, Unplaced $ StringValue ctorName,
           Unplaced $ Var "$rec" ParamOut flowType]]
         ++
         (List.map (\(Param var _ dir paramFlowType) ->
                     (Unplaced $ ForeignCall "$" "mutate" []
                      [Unplaced $ StringValue $ typeName,
                       Unplaced $ StringValue ctorName,
                       Unplaced $ StringValue var,
                       Unplaced $ Var "$rec" ParamInOut flowType,
                       Unplaced $ Var var ParamIn paramFlowType]))
          params))
        (Unplaced $ Var "$rec" ParamIn flowType))
       pos)
    mapM_ (addGetterSetter modCompiler vis typespec ctorName pos) params

-- |Add a getter and setter for the specified type.
addGetterSetter :: ([ModSpec] -> Compiler ()) -> Visibility -> TypeSpec ->
                   Ident -> OptPos -> Param -> Compiler ()
addGetterSetter modCompiler vis rectype ctorName pos
                    (Param field fieldtype _ _) = do
    normaliseItem modCompiler $ FuncDecl vis
      (FnProto field [Param "$rec" rectype ParamIn Ordinary] [])
      fieldtype 
      (Unplaced $ ForeignFn "$" "access" []
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamIn Ordinary])
      pos
    normaliseItem modCompiler $ ProcDecl vis 
      (ProcProto field 
       [Param "$rec" rectype ParamInOut Ordinary,
        Param "$field" fieldtype ParamIn Ordinary] [])
      [Unplaced $ ForeignCall "$" "mutate" []
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamInOut Ordinary,
        Unplaced $ Var "$field" ParamIn Ordinary]]
       pos

----------------------------------------------------------------
--                 Clause compiler monad
----------------------------------------------------------------

-- |The clause compiler monad is a state transformer monad carrying the 
--  clause compiler state over the compiler monad.
type ClauseComp = StateT ClauseCompState Compiler


-- |The state of compilation of a clause; used by the ClauseComp
-- monad.
data ClauseCompState = ClauseComp {
    varMap :: Map VarName Int,   -- ^current var number for each var
    resourceMap :: Map ResourceName Int
                                    -- ^var number and type for each resource
  }


initClauseComp :: ClauseCompState
initClauseComp = ClauseComp Map.empty Map.empty


nextVar :: String -> ClauseComp PrimVarName
nextVar name = do
    resMap <- gets resourceMap
    case Map.lookup name resMap of
        Nothing -> do
            modify (\s -> s { varMap = Map.alter (Just . maybe 0 (+1)) name $ 
                                       varMap s })
        Just n ->
            modify (\s -> s { resourceMap = Map.insert name (n+1) $
                                            resourceMap s})
    currVar name Nothing


currVar :: String -> OptPos -> ClauseComp PrimVarName
currVar name pos = do
    resMap <- gets resourceMap
    case Map.lookup name resMap of
        Nothing -> do
            dict <- gets varMap
            case Map.lookup name dict of
                Nothing -> do
                       lift $ message Error
                           ("Uninitialised variable '" ++ name ++ "'") pos
                       return $ PrimVarName name (-1)
                Just n -> return $ PrimVarName name n
        Just n -> return $ PrimVarName name n



mkPrimVarName :: Map String Int -> String -> PrimVarName
mkPrimVarName dict name =
    case Map.lookup name dict of
        Nothing -> PrimVarName name 0
        -- must have been introduced in resource expansion, which always uses 0
        -- Nothing -> shouldnt $ "Undefined variable '" ++ name ++ "'"
        Just n  -> PrimVarName name n


-- |Run a clause compiler function from the Compiler monad to compile
--  a generated procedure.
evalClauseComp :: ClauseComp t -> Compiler t
evalClauseComp clcomp =
    evalStateT clcomp initClauseComp


compileProc :: Int -> Item -> Compiler ProcDef
compileProc tmpCtr (ProcDecl vis (ProcProto name params resources) body pos) 
  = do
    (params',body') <- evalClauseComp $ do
        mapM_ nextVar $ List.map paramName $ 
          List.filter (flowsIn . paramFlow) params
        startVars <- gets varMap
        -- liftIO $ putStrLn $ "Compiling body of " ++ name ++ "..."
        let resMap = List.foldr (\r m -> 
                                     Map.insert (resourceName
                                                 (resourceFlowRes r)) 0 m)
                     Map.empty resources
        modify (\s -> s { resourceMap = resMap })
        compiled <- compileBody body
        -- liftIO $ putStrLn $ "Compiled"
        endVars <- gets varMap
        return (List.map (primParam startVars endVars) params, compiled)
    let def = ProcDef name (PrimProto name params') resources body' pos
              tmpCtr 0 vis False Nothing []
    -- liftIO $ putStrLn $ "Compiled version:\n" ++ showProcDef 0 def
    return def
compileProc _ decl =
    shouldnt $ "compileProc applied to non-proc " ++ show decl


-- |Convert a Param to single PrimParam.  Only ParamIn and ParamOut 
--  params should still exist at this point. 
primParam :: Map VarName Int -> Map VarName Int -> Param -> PrimParam
primParam initVars finalVars (Param name typ ParamIn flowType) =
    PrimParam (mkPrimVarName initVars name) typ FlowIn flowType True
primParam initVars finalVars (Param name typ ParamOut flowType) =
    PrimParam (mkPrimVarName finalVars name) typ FlowOut flowType True
primParam _ _ param =
    shouldnt $ "Flattening error: param '" ++ show param ++ "' remains"



-- |Compile a proc body to LPVM form.  By the time we get here, the 
--  form of the body is very limited:  it is either a single Cond 
--  statement, or it is a list of ProcCalls and ForeignCalls.  
--  Everything else has already been transformed away.
compileBody :: [Placed Stmt] -> ClauseComp ProcBody
compileBody [placed]
  | case content placed of
      Cond _ _ _ _ -> True
      _ -> False
 = do
      let Cond tstStmts tstVar thn els = content placed
      initial <- gets varMap
      tstStmts' <- mapM compileSimpleStmt tstStmts
      tstVar' <- placedApplyM compileArg tstVar
      thn' <- mapM compileSimpleStmt thn
      afterThen <- gets varMap
      modify (\s -> s { varMap = initial })
      els' <- mapM compileSimpleStmt els
      afterElse <- gets varMap
      let final = Map.intersectionWith max afterThen afterElse
      modify (\s -> s { varMap = final })
      let thn'' = thn' ++ reconcilingAssignments afterThen final
      let els'' = els' ++ reconcilingAssignments afterElse final
      case tstVar' of
        ArgVar var _ FlowIn _ _ ->
            return $ ProcBody tstStmts' $
                   PrimFork var False [ProcBody els'' NoFork,
                                       ProcBody thn'' NoFork]
        ArgInt n _ ->
            return $ ProcBody (if n/=0 then tstStmts'++thn'' else els'') NoFork
        _ -> do
            lift $ message Error 
                   ("Condition is non-bool constant or output '" ++
                    show tstVar' ++ "'") $
                 betterPlace (place placed) tstVar
            return $ ProcBody [] NoFork


compileBody stmts = do
    prims <- mapM compileSimpleStmt stmts
    return $ ProcBody prims NoFork

compileSimpleStmt :: Placed Stmt -> ClauseComp (Placed Prim)
compileSimpleStmt stmt = do
    stmt' <- compileSimpleStmt' (content stmt)
    return $ maybePlace stmt' (place stmt)

compileSimpleStmt' :: Stmt -> ClauseComp Prim
compileSimpleStmt' (ProcCall maybeMod name args) = do
    args' <- mapM (placedApply compileArg) args
    return $ PrimCall maybeMod name Nothing args'
compileSimpleStmt' (ForeignCall lang name flags args) = do
    args' <- mapM (placedApply compileArg) args
    return $ PrimForeign lang name flags args'
compileSimpleStmt' (Nop) = do
    return $ PrimNop
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


compileArg :: Exp -> OptPos -> ClauseComp PrimArg
compileArg = compileArg' Unspecified

compileArg' :: TypeSpec -> Exp -> OptPos -> ClauseComp PrimArg
compileArg' typ (IntValue int) _ = return $ ArgInt int typ
compileArg' typ (FloatValue float) _ = return $ ArgFloat float typ
compileArg' typ (StringValue string) _ = return $ ArgString string typ
compileArg' typ (CharValue char) _ = return $ ArgChar char typ
compileArg' typ (Var name ParamIn flowType) pos = do
    name' <- currVar name pos
    return $ ArgVar name' typ FlowIn flowType False
compileArg' typ (Var name ParamOut flowType) _ = do
    name' <- nextVar name
    return $ ArgVar name' typ FlowOut flowType False
compileArg' _ (Typed exp typ) pos = compileArg' typ exp pos
compileArg' _ arg _ =
    shouldnt $ "Normalisation left complex argument: " ++ show arg


reconcilingAssignments :: Map VarName Int -> Map VarName Int -> [Placed Prim]
reconcilingAssignments caseVars jointVars =
    let vars =
          List.filter (\v -> caseVars ! v /= jointVars ! v) $ keys jointVars
    in  List.map (reconcileOne caseVars jointVars) vars


reconcileOne :: (Map VarName Int) -> (Map VarName Int) -> VarName -> Placed Prim
reconcileOne caseVars jointVars var =
    Unplaced $
    PrimCall [] "=" Nothing [
        ArgVar (mkPrimVarName jointVars var) Unspecified FlowOut Ordinary False,
        ArgVar (mkPrimVarName caseVars var) Unspecified FlowIn Ordinary False]
