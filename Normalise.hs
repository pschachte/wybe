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
    -- Now generate main proc if needed
    stmts <- gets stmtDecls
    unless (List.null stmts)
      $ normaliseItem (ProcDecl Private (ProcProto "" []) (List.reverse stmts) 
                       Nothing)
    

-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) items pos) = do
    dir <- getDirectory
    parentmod <- getModuleSpec
    enterModule dir (parentmod ++ [name]) (Just params)
    addType name (TypeDef (length params) pos) vis
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
  normaliseItem $
  ProcDecl 
  vis
  (ProcProto name $ params ++ [Param "$" resulttype ParamOut])
  [Unplaced $ ProcCall "=" [Unplaced $ Var "$" ParamOut, result]]
  pos
normaliseItem (ProcDecl vis proto@(ProcProto name params) stmts pos) = do
    proto' <- flattenProto proto
    stmts' <- flattenBody stmts
    -- liftIO $ putStrLn $ "Flattened proc:\n" ++ show (ProcDecl vis proto' stmts' pos)
    (stmts'',genProcs) <- unbranchBody params stmts'
    let procs = ProcDecl vis proto' stmts'' pos:genProcs
    -- liftIO $ mapM_ (\item -> putStrLn $ show item) procs
    mapM_ compileProc procs
normaliseItem (CtorDecl vis proto pos) = do
    modspec <- getModuleSpec
    Just modparams <- getModuleParams
    addCtor vis (last modspec) modparams proto
normaliseItem (StmtDecl stmt pos) = do
    modify (\s -> s { stmtDecls = maybePlace stmt pos : stmtDecls s})


-- |Add a contructor for the specified type.
addCtor :: Visibility -> Ident -> [Ident] -> FnProto -> Compiler ()
addCtor vis typeName typeParams (FnProto ctorName params) = do
    let typespec = TypeSpec typeName $ List.map (\n->TypeSpec n []) typeParams
    normaliseItem 
      (FuncDecl Public (FnProto ctorName params) typespec
       (Unplaced $ Where 
        ([Unplaced $ ForeignCall "$" "alloc" [Unplaced $ StringValue typeName,
                                              Unplaced $ StringValue ctorName,
                                              Unplaced $ Var "$rec" ParamOut]]
         ++
         (List.map (\(Param var _ dir) ->
                     (Unplaced $ ForeignCall "$" "mutate"
                      [Unplaced $ StringValue $ typeName,
                       Unplaced $ StringValue ctorName,
                       Unplaced $ StringValue var,
                       Unplaced $ Var "$rec" ParamInOut,
                       Unplaced $ Var var ParamIn]))
          params))
        (Unplaced $ Var "$rec" ParamIn))
       Nothing)
    mapM_ (addGetterSetter vis typespec ctorName) params

-- |Add a getter and setter for the specified type.
addGetterSetter :: Visibility -> TypeSpec -> Ident -> Param -> Compiler ()
addGetterSetter vis rectype ctorName (Param field fieldtype _) = do
    normaliseItem $ FuncDecl vis 
      (FnProto field [Param "$rec" rectype ParamIn])
      fieldtype 
      (Unplaced $ ForeignFn "$" "access" 
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamIn])
      Nothing
    normaliseItem $ ProcDecl vis 
      (ProcProto field 
       [Param "$rec" rectype ParamInOut,
        Param "$field" fieldtype ParamIn])
      [Unplaced $ ForeignCall "$" "mutate"
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamInOut,
        Unplaced $ Var "$field" ParamIn]]
       Nothing

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


compileProc :: Item -> Compiler ()
compileProc (ProcDecl vis (ProcProto name params) body pos) = do
    (params',body') <- evalClauseComp $ do
        mapM_ nextVar $ List.map paramName $ 
          List.filter (flowsIn . paramFlow) params
        startVars <- gets vars
        compiled <- compileBody body
        endVars <- gets vars
        return (List.map (primParam startVars endVars) params, compiled)
    addProc name (PrimProto name params') body' pos vis
    return ()
compileProc decl =
    shouldnt $ "compileProc applied to non-proc " ++ show decl


-- |Convert a Param to single PrimParam.  Only ParamIn and ParamOut 
--  params should still exist at this point. 
primParam :: Map VarName Int -> Map VarName Int -> Param -> PrimParam
primParam initVars finalVars (Param name typ ParamIn) =
    PrimParam (mkPrimVarName initVars name) typ FlowIn Ordinary
primParam initVars finalVars (Param name typ ParamOut) = do
    PrimParam (mkPrimVarName finalVars name) typ FlowOut Ordinary
primParam _ _ param =
    shouldnt $ "Flattening error: param '" ++ show param ++ "' remains"



-- |Compile a proc body to LPVM form.  By the time we get here, the 
--  form of the body is very limited:  it is either a single Cond 
--  statement, or it is a list of ProcCalls and ForeignCalls.  
--  Everything else has already been transformed away.
compileBody :: [Placed Stmt] -> ClauseComp [[Placed Prim]]
compileBody [placed]
  | case content placed of
      Cond _ _ _ -> True
      _ -> False
 = do
      let Cond tst thn els = content placed
      initial <- gets vars
      tst' <- mapM compileSimpleStmt tst
      thn' <- mapM compileSimpleStmt thn
      afterThen <- gets vars
      modify (\s -> s { vars = initial })
      els' <- mapM compileSimpleStmt els
      afterElse <- gets vars
      let final = Map.intersectionWith max afterThen afterElse
      modify (\s -> s { vars = final })
      let thn'' = thn' ++ reconcilingAssignments afterThen final
      let els'' = els' ++ reconcilingAssignments afterElse final
      return [Unplaced (PrimGuard tst' 1):thn'',
              Unplaced (PrimGuard tst' 0):els'']
compileBody stmts = do
    prims <- mapM compileSimpleStmt stmts
    return [prims]

compileSimpleStmt :: Placed Stmt -> ClauseComp (Placed Prim)
compileSimpleStmt stmt = do
    stmt' <- compileSimpleStmt' (content stmt)
    return $ maybePlace stmt' (place stmt)

compileSimpleStmt' :: Stmt -> ClauseComp Prim
compileSimpleStmt' (ProcCall name args) = do
    args' <- mapM (compileArg . content) args
    return $ PrimCall name Nothing args'
compileSimpleStmt' (ForeignCall lang name args) = do
    args' <- mapM (compileArg . content) args
    return $ PrimForeign lang name Nothing args'
compileSimpleStmt' (Nop) = do
    return $ PrimNop
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


compileArg :: Exp -> ClauseComp PrimArg
compileArg (IntValue int) = return $ ArgInt int
compileArg (FloatValue float) = return $ ArgFloat float
compileArg (StringValue string) = return $ ArgString string
compileArg (CharValue char) = return $ ArgChar char
compileArg (Var name ParamIn) = do
    name' <- currVar name
    return $ ArgVar name' FlowIn Ordinary
compileArg (Var name ParamOut) = do
    name' <- nextVar name
    return $ ArgVar name' FlowOut Ordinary
compileArg arg =
    shouldnt $ "Normalisation left complex argument: " ++ show arg


reconcilingAssignments :: Map VarName Int -> Map VarName Int -> [Placed Prim]
reconcilingAssignments caseVars jointVars =
    let vars =
          List.filter (\v -> caseVars ! v /= jointVars ! v) $ keys jointVars
    in  List.map (reconcileOne caseVars jointVars) vars


reconcileOne :: (Map VarName Int) -> (Map VarName Int) -> VarName -> Placed Prim
reconcileOne caseVars jointVars var =
    Unplaced $
    PrimCall "=" Nothing [
        ArgVar (mkPrimVarName jointVars var) FlowOut Ordinary,
        ArgVar (mkPrimVarName caseVars var) FlowIn Ordinary]
