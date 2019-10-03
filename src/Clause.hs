--  File     : Clause.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Sat Jun 28 22:40:58 2014
--  Purpose  : Convert Wybe code to clausal (LPVM) form
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--

module Clause (compileProc) where

import           AST
import           Control.Monad
import           Control.Monad.Trans               (lift, liftIO)
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           Data.List                         as List
import           Data.Map                          as Map
import           Data.Maybe                        as Maybe
import           Data.Set                          as Set
import           Options                           (LogSelection (Clause))
import           Snippets
import           Text.ParserCombinators.Parsec.Pos
import           Util


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


closingStmts :: Determinism -> ClauseComp [Placed Prim]
closingStmts Det = return []
closingStmts SemiDet = do
    tested <- gets $ Map.member "$$"
    return $ if tested
             then []
             else [Unplaced $ primMove
                   (ArgInt 1 boolType)
                   (ArgVar (PrimVarName "$$" 0) boolType
                    FlowOut Ordinary False)]


-- |Run a clause compiler function from the Compiler monad to compile
--  a generated procedure.
evalClauseComp :: ClauseComp t -> Compiler t
evalClauseComp clcomp =
    evalStateT clcomp initClauseComp


-- |Compile a ProcDefSrc to a ProcDefPrim, ie, compile a proc
--  definition in source form to one in clausal form.
compileProc :: ProcDef -> Compiler ProcDef
compileProc proc =
    evalClauseComp $ do
        let detism = procDetism proc
        let ProcDefSrc body = procImpln proc
        let proto = procProto proc
        let params = procProtoParams proto
        let params' = case detism of
                         SemiDet -> params ++ [testOutParam]
                         Det     -> params
        logClause $ "--------------\nCompiling proc " ++ show proto
        mapM_ (nextVar . paramName) $ List.filter (flowsIn . paramFlow) params
        startVars <- get
        compiled <- compileBody body params' detism
        logClause $ "Compiled to:"  ++ showBlock 4 compiled
        endVars <- get
        logClause $ "  startVars: " ++ show startVars
        logClause $ "  endVars  : " ++ show endVars
        logClause $ "  params   : " ++ show params
        let params'' = List.map (compileParam startVars endVars) params'
        let proto' = PrimProto (procProtoName proto) params''
        logClause $ "  comparams: " ++ show params''
        return $ proc { procImpln = ProcDefPrim proto' compiled
                                        (ProcAnalysis initUnionFind)}



-- |Compile a proc body to LPVM form. By the time we get here, the form of the
--  body is very limited: it is a list of ProcCalls and ForeignCalls, possibly
--  ending with a single Cond statement whose test is a single TestBool
--  statement and whose then and else branches are also bodies satisfying these
--  conditions. If the proc is SemiDet, then the body must ends with a TestBool
--  statement, or with a Cond statement whose then and else branches satisfy
--  this condition. Everything else has already been transformed away.
--  Furthermore, TestBool statements only appear as the condition of a Cond
--  statement or, in the case of a SemiDet proc, as the final statement of a
--  body. This code assumes that these invariants are observed, and does not
--  worry whether the proc is Det or SemiDet.
compileBody :: [Placed Stmt] -> [Param] -> Determinism -> ClauseComp ProcBody
compileBody [] _params detism = do
    end <- closingStmts detism
    return $ ProcBody end NoFork
compileBody stmts params detism = do
    logClause $ "Compiling body:" ++ showBody 4 stmts
    let final = last stmts
    case content final of
        Cond tst thn els ->
          case content tst of
              TestBool var -> do
                front <- mapM compileSimpleStmt $ init stmts
                compileCond front (place final) var thn els params detism
              tstStmt ->
                shouldnt $ "CompileBody of Cond with non-simple test:\n"
                           ++ show tstStmt
        _ -> do
          prims <- mapM compileSimpleStmt stmts
          end <- closingStmts detism
          return $ ProcBody (prims++end) NoFork


compileCond :: [Placed Prim] -> OptPos -> Exp -> [Placed Stmt]
    -> [Placed Stmt] -> [Param] -> Determinism -> ClauseComp ProcBody
compileCond front pos (Typed expr _typ _) thn els params detism =
    compileCond front pos expr thn els params detism
compileCond front pos expr thn els params detism = do
          name' <- case expr of
              Var var ParamIn _ -> Just <$> currVar var Nothing
              _                 -> return Nothing
          logClause $ "conditional on " ++ show expr ++ " new name = " ++ show name'
          beforeTest <- get
          thn' <- compileBody thn params detism
          afterThen <- get
          logClause $ "  vars after then: " ++ show afterThen
          put beforeTest
          els' <- compileBody els params detism
          afterElse <- get
          logClause $ "  vars after else: " ++ show afterElse
          let final = Map.intersectionWith max afterThen afterElse
          put final
          logClause $ "  vars after ite: " ++ show final
          let thnAssigns = reconcilingAssignments afterThen final params
          let elsAssigns = reconcilingAssignments afterElse final params
          case expr of
              IntValue 0 ->
                return $ prependToBody front $ appendToBody els' elsAssigns
              IntValue _ ->
                return $ prependToBody front $ appendToBody thn' thnAssigns
              Var _ ParamIn _ ->
                return $ ProcBody front
                    $ PrimFork (fromJust name') boolType False
                    [appendToBody els' elsAssigns, appendToBody thn' thnAssigns]
              _ ->
                shouldnt $ "TestBool with invalid argument " ++ show expr

-- |Add the specified statements at the end of the given body
appendToBody :: ProcBody -> [Placed Prim] -> ProcBody
appendToBody (ProcBody prims NoFork) after
    = ProcBody (prims++after) NoFork
appendToBody (ProcBody prims (PrimFork v ty lst bodies)) after
    = let bodies' = List.map (flip appendToBody after) bodies
      in ProcBody prims $ PrimFork v ty lst bodies'

-- |Add the specified statements at the front of the given body
prependToBody :: [Placed Prim] -> ProcBody -> ProcBody
prependToBody before (ProcBody prims fork)
    = ProcBody (before++prims) fork

compileSimpleStmt :: Placed Stmt -> ClauseComp (Placed Prim)
compileSimpleStmt stmt = do
    logClause $ "Compiling " ++ showStmt 4 (content stmt)
    stmt' <- compileSimpleStmt' (content stmt)
    logClause $ "Compiled to " ++ show stmt'
    return $ maybePlace stmt' (place stmt)

compileSimpleStmt' :: Stmt -> ClauseComp Prim
compileSimpleStmt' call@(ProcCall maybeMod name procID _ _ args) = do
    logClause $ "Compiling call " ++ showStmt 4 call
    args' <- mapM (placedApply compileArg) args
    return $ PrimCall (ProcSpec maybeMod name $
                       trustFromJust
                       ("compileSimpleStmt' for " ++ showStmt 4 call)
                       procID)
        args'
compileSimpleStmt' (ForeignCall lang name flags args) = do
    args' <- mapM (placedApply compileArg) args
    return $ PrimForeign lang name flags args'
compileSimpleStmt' (TestBool expr) =
    -- Only for handling a TestBool other than as the condition of a Cond:
    compileSimpleStmt' $ content $ move expr (boolVarSet "$$")
compileSimpleStmt' Nop = return $ PrimTest $ ArgInt 1 intType
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


compileArg :: Exp -> OptPos -> ClauseComp PrimArg
compileArg = compileArg' AnyType

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
compileArg' _ (Typed exp typ _) pos = compileArg' typ exp pos
compileArg' _ arg _ =
    shouldnt $ "Normalisation left complex argument: " ++ show arg


reconcilingAssignments :: Map VarName Int -> Map VarName Int
                       -> [Param] -> [Placed Prim]
reconcilingAssignments caseVars jointVars params =
    Maybe.mapMaybe (reconcileOne caseVars jointVars) params


reconcileOne :: (Map VarName Int) -> (Map VarName Int) -> Param
             -> Maybe (Placed Prim)
reconcileOne caseVars jointVars (Param name ty flow ftype) =
    case (Map.lookup name caseVars,
          Map.lookup name jointVars)
    of (Just caseNum, Just jointNum) ->
         if caseNum /= jointNum && elem flow [ParamOut, ParamInOut]
         then Just $ Unplaced $
              PrimForeign "llvm" "move" []
              [ArgVar (PrimVarName name caseNum) ty FlowIn Ordinary False,
               ArgVar (PrimVarName name jointNum) ty FlowOut Ordinary False]
         else Nothing
       _ -> Nothing


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


-- |A synthetic output parameter carrying the test result
testOutParam :: Param
testOutParam = Param "$$" boolType ParamOut $ Implicit Nothing


-- |Log a message, if we are logging clause generation.
logClause :: String -> ClauseComp ()
logClause s = lift $ logMsg Clause s
