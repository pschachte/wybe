--  File     : Clause.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Sat Jun 28 22:40:58 2014
--  Purpose  : Convert Wybe code to clausal (LPVM) form
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--

module Clause (compileProc) where

import AST
import Options (LogSelection(Clause))
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Maybe
import Text.ParserCombinators.Parsec.Pos
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans (lift,liftIO)


----------------------------------------------------------------
--                 Clause compiler monad
----------------------------------------------------------------

-- |The clause compiler monad is a state transformer monad carrying the 
--  clause compiler state over the compiler monad.
type ClauseComp = StateT ClauseCompState Compiler


-- |The state of compilation of a clause; used by the ClauseComp
-- monad.
type ClauseCompState = Map VarName Int   -- ^current var number for each var


initClauseComp :: ClauseCompState
initClauseComp = Map.empty


nextVar :: String -> ClauseComp PrimVarName
nextVar name = do
    modify (Map.alter (Just . maybe 0 (+1)) name)
    currVar name Nothing


currVar :: String -> OptPos -> ClauseComp PrimVarName
currVar name pos = do
    dict <- get
    case Map.lookup name dict of
        Nothing -> do
            lift $ message Error
                     ("Uninitialised variable '" ++ name ++ "'") pos
            return $ PrimVarName name (-1)
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


-- |Compile a ProcDefSrc to a ProcDefPrim, ie, compile a proc 
--  definition in source form to one in clausal form.
compileProc :: ProcDef -> Compiler ProcDef
compileProc proc = do
    evalClauseComp $ do
        let ProcDefSrc body = procImpln proc
        let proto = procProto proc
        let params = procProtoParams proto
        mapM_ nextVar $ List.map paramName $ 
          List.filter (flowsIn . paramFlow) params
        startVars <- get
        logClause $ "Compiling body:\n" ++ showBody 4 body
        compiled <- compileBody body
        logClause $ "Compiled to:\n"  ++ showBlock 4 compiled
        endVars <- get
        logClause $ "startVars: " ++ show startVars
        logClause $ "endVars  : " ++ show endVars
        logClause $ "params   : " ++ show params
        let params' = List.map (compileParam startVars endVars) params
        let proto' = PrimProto (procProtoName proto) params'
        logClause $ "comparams: " ++ show params'
        return $ proc { procImpln = ProcDefPrim proto' compiled }



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
      initial <- get
      tstStmts' <- mapM compileSimpleStmt tstStmts
      tstVar' <- placedApplyM compileArg tstVar
      thn' <- mapM compileSimpleStmt thn
      afterThen <- get
      put initial
      els' <- mapM compileSimpleStmt els
      afterElse <- get
      let final = Map.intersectionWith max afterThen afterElse
      put final
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
    logClause $ "Compiling " ++ showStmt 4 (content stmt)
    stmt' <- compileSimpleStmt' (content stmt)
    return $ maybePlace stmt' (place stmt)

compileSimpleStmt' :: Stmt -> ClauseComp Prim
compileSimpleStmt' call@(ProcCall maybeMod name procID args) = do
    logClause $ "Compiling call " ++ showStmt 4 call
    args' <- mapM (placedApply compileArg) args
    return $ PrimCall (ProcSpec maybeMod name $
                       trustFromJust "compileSimpleStmt'" procID)
      args'
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
    PrimForeign "wybe" "move" []
    [ArgVar (mkPrimVarName caseVars var) Unspecified FlowIn Ordinary False,
     ArgVar (mkPrimVarName jointVars var) Unspecified FlowOut Ordinary False]


compileParam :: ClauseCompState -> ClauseCompState -> Param -> PrimParam
compileParam startVars endVars param@(Param name ty flow ftype) =
    let (pflow,num) =
            case flow of
                ParamIn -> (FlowIn, Map.findWithDefault 0 name startVars)
                ParamOut -> (FlowOut, Map.findWithDefault 0 name endVars)
                             -- trustFromJust
                             -- ("compileParam for param " ++ show param)
                             -- $ Map.lookup name endVars)
                _ -> shouldnt "non-simple parameter flow in compileParam"
    in PrimParam (PrimVarName name num)
       ty pflow ftype (ParamInfo False)


-- |Log a message, if we are logging unbrancher activity.
logClause :: String -> ClauseComp ()
logClause s = lift $ logMsg Clause s
