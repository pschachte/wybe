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
normalise :: [Item] -> Compiler ()
normalise items = do
    mapM_ normaliseItem items
    -- liftIO $ putStrLn "File compiled"
    addImport ["wybe"] True Nothing Private -- every module imports stdlib
    -- Now generate main proc if needed
    stmts <- getModule stmtDecls 
    unless (List.null stmts)
      $ normaliseItem (ProcDecl Private (ProcProto "" []) (List.reverse stmts) 
                       Nothing)
    

-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) items pos) = do
    dir <- getDirectory
    parentmod <- getModuleSpec
    addType name (TypeDef (length params) pos) vis
    enterModule dir (parentmod ++ [name]) (Just params)
    normalise items
    mod <- finishModule
    addSubmod name mod pos vis
    return ()
normaliseItem (ModuleDecl vis name items pos) = do
    dir <- getDirectory
    parentmod <- getModuleSpec
    enterModule dir (parentmod ++ [name]) Nothing
    normalise items
    mod <- finishModule
    addSubmod name mod pos vis
    return ()
normaliseItem (ImportMods vis imp modspecs pos) = do
    mapM_ (\spec -> addImport spec imp Nothing vis) modspecs
normaliseItem (ImportItems vis imp modspec imports pos) = do
    addImport modspec imp (Just imports) vis
normaliseItem (ResourceDecl vis name typ pos) =
  addResource name (SimpleResource typ pos) vis
normaliseItem (FuncDecl vis (FnProto name params) resulttype result pos) =
  let flowType = Implicit pos
  in  normaliseItem
   (ProcDecl
    vis
    (ProcProto name $ params ++ [Param "$" resulttype ParamOut flowType])
    [Unplaced $ ProcCall [] "=" [Unplaced $ Var "$" ParamOut flowType, result]]
    pos)
normaliseItem decl@(ProcDecl _ _ _ _) = do
    (ProcDecl vis proto@(ProcProto _ params) stmts pos,tmpCtr) <- 
        flattenProcDecl decl
    -- (proto' <- flattenProto proto
    -- (stmts,tmpCtr) <- flattenBody stmts
    -- liftIO $ putStrLn $ "Flattened proc:\n" ++ show (ProcDecl vis proto' stmts pos)
    (stmts',genProcs) <- unbranchBody params stmts
    let procs = ProcDecl vis proto stmts' pos:genProcs
    -- liftIO $ mapM_ (\item -> putStrLn $ show item) procs
    mapM_ (compileProc tmpCtr) procs
normaliseItem (CtorDecl vis proto pos) = do
    modspec <- getModuleSpec
    Just modparams <- getModuleParams
    addCtor vis (last modspec) modparams proto pos
normaliseItem (StmtDecl stmt pos) = do
    updateModule (\s -> s { stmtDecls = maybePlace stmt pos : stmtDecls s})


-- |Add a contructor for the specified type.
addCtor :: Visibility -> Ident -> [Ident] -> FnProto -> OptPos -> Compiler ()
addCtor vis typeName typeParams (FnProto ctorName params) pos = do
    let typespec = TypeSpec [] typeName $ 
                   List.map (\n->TypeSpec [] n []) typeParams
    let flowType = Implicit pos
    normaliseItem
      (FuncDecl Public (FnProto ctorName params) typespec
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
       Nothing)
    mapM_ (addGetterSetter vis typespec ctorName pos) params

-- |Add a getter and setter for the specified type.
addGetterSetter :: Visibility -> TypeSpec -> Ident -> OptPos -> Param -> Compiler ()
addGetterSetter vis rectype ctorName pos (Param field fieldtype _ _) = do
    normaliseItem $ FuncDecl vis
      (FnProto field [Param "$rec" rectype ParamIn Ordinary])
      fieldtype 
      (Unplaced $ ForeignFn "$" "access" []
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamIn Ordinary])
      pos
    normaliseItem $ ProcDecl vis 
      (ProcProto field 
       [Param "$rec" rectype ParamInOut Ordinary,
        Param "$field" fieldtype ParamIn Ordinary])
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
    vars :: Map VarName Int    -- ^current var number for each var
  }


initClauseComp :: ClauseCompState
initClauseComp = ClauseComp Map.empty


nextVar :: String -> ClauseComp PrimVarName
nextVar name = do
    modify (\s -> s { vars = Map.alter incrMaybe name $ vars s })
    currVar name


currVar :: String -> ClauseComp PrimVarName
currVar name = do
    dict <- gets vars
    return $ mkPrimVarName dict name


mkPrimVarName :: Map String Int -> String -> PrimVarName
mkPrimVarName dict name =
    case Map.lookup name dict of
        -- Nothing -> shouldnt $ "Referred to undefined variable '" ++ name ++ "'"
        Nothing -> PrimVarName name (-1)
        Just n  -> PrimVarName name n


incrMaybe :: Maybe Int -> Maybe Int
incrMaybe Nothing = Just 0
incrMaybe (Just n) = Just $ n + 1


-- |Run a clause compiler function from the Compiler monad to compile
--  a generated procedure.
evalClauseComp :: ClauseComp t -> Compiler t
evalClauseComp clcomp =
    evalStateT clcomp initClauseComp


compileProc :: Int -> Item -> Compiler ()
compileProc tmpCtr (ProcDecl vis (ProcProto name params) body pos) = do
    (params',body') <- evalClauseComp $ do
        mapM_ nextVar $ List.map paramName $ 
          List.filter (flowsIn . paramFlow) params
        startVars <- gets vars
        -- liftIO $ putStrLn $ "Compiling body of " ++ name ++ "..."
        compiled <- compileBody body
        -- liftIO $ putStrLn $ "Compiled"
        endVars <- gets vars
        return (List.map (primParam startVars endVars) params, compiled)
    let def = ProcDef name (PrimProto name params') body' pos tmpCtr 0 vis
    -- liftIO $ putStrLn $ "Compiled version:\n" ++ showProcDef 0 def
    addProc def
    return ()
compileProc _ decl =
    shouldnt $ "compileProc applied to non-proc " ++ show decl


-- |Convert a Param to single PrimParam.  Only ParamIn and ParamOut 
--  params should still exist at this point. 
primParam :: Map VarName Int -> Map VarName Int -> Param -> PrimParam
primParam initVars finalVars (Param name typ ParamIn flowType) =
    PrimParam (mkPrimVarName initVars name) typ FlowIn flowType
primParam initVars finalVars (Param name typ ParamOut flowType) = do
    PrimParam (mkPrimVarName finalVars name) typ FlowOut flowType
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
      initial <- gets vars
      tstStmts' <- mapM compileSimpleStmt tstStmts
      tstVar' <- compileArg $ content tstVar
      thn' <- mapM compileSimpleStmt thn
      afterThen <- gets vars
      modify (\s -> s { vars = initial })
      els' <- mapM compileSimpleStmt els
      afterElse <- gets vars
      let final = Map.intersectionWith max afterThen afterElse
      modify (\s -> s { vars = final })
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
    args' <- mapM (compileArg . content) args
    return $ PrimCall maybeMod name Nothing args'
compileSimpleStmt' (ForeignCall lang name flags args) = do
    args' <- mapM (compileArg . content) args
    return $ PrimForeign lang name flags args'
compileSimpleStmt' (Nop) = do
    return $ PrimNop
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


compileArg :: Exp -> ClauseComp PrimArg
compileArg = compileArg' Unspecified

compileArg' :: TypeSpec -> Exp -> ClauseComp PrimArg
compileArg' typ (IntValue int) = return $ ArgInt int typ
compileArg' typ (FloatValue float) = return $ ArgFloat float typ
compileArg' typ (StringValue string) = return $ ArgString string typ
compileArg' typ (CharValue char) = return $ ArgChar char typ
compileArg' typ (Var name ParamIn flowType) = do
    name' <- currVar name
    return $ ArgVar name' typ FlowIn flowType False
compileArg' typ (Var name ParamOut flowType) = do
    name' <- nextVar name
    return $ ArgVar name' typ FlowOut flowType False
compileArg' _ (Typed exp typ) = compileArg' typ exp
compileArg' _ arg =
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
