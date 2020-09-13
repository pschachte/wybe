--  File     : Clause.hs
--  Author   : Peter Schachte
--  Purpose  : Convert Wybe code to clausal (LPVM) form
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


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


-- |Associate a version number with each variable name.
type Numbering = Map VarName Int


-- |The state of compilation of a clause; used by the ClauseComp monad.
-- This allows us to assign a "version" number to each variable; each
-- time a variable is assigned, the number increments.  All input uses
-- (reads) of a variable in a given statement use the current number of
-- the variable, and output (write) uses use the next number.  This
-- ensures that even a input use that follows an output use in the same
-- statement gets the current number.  At the end of each statement, the
-- next variable map is copied to the current variable map, so input
-- uses of a variable in the following statement refer to the output
-- variables of the previous statement.
data ClauseCompState = ClauseCompState {
        currVars       :: Numbering,   -- ^current var number for each var
        nextVars       :: Numbering,   -- ^var numbers after current stmt
        nextCallSiteID :: CallSiteID   -- ^The next callSiteID to use
        }


initClauseComp :: ClauseCompState
initClauseComp = ClauseCompState Map.empty Map.empty 0


-- |Get the next versioned name of the specified variable
nextVar :: String -> ClauseComp PrimVarName
nextVar name = do
    newNum <- gets (maybe 0 (+1) . Map.lookup name . nextVars)
    modify $ \st -> st {nextVars = Map.insert name newNum $ nextVars st}
    return $ PrimVarName name newNum


-- |Get the current versioned name of the specified variable
currVar :: String -> OptPos -> ClauseComp PrimVarName
currVar name pos = do
    dict <- gets currVars
    case Map.lookup name dict of
        Nothing -> do
            lift $ message Error
                     ("Uninitialised variable '" ++ name ++ "'") pos
            return $ PrimVarName name (-1)
        Just n -> return $ PrimVarName name n


-- |Get the current numbering
getCurrNumbering :: ClauseComp Numbering
getCurrNumbering = gets nextVars


-- |Set both current and next numberings to the specified mapping.
putNumberings :: Numbering -> ClauseComp ()
putNumberings numbering = 
    modify (\st -> st {currVars = numbering, nextVars = numbering})


-- |Prepare for the next statement, promoting the final variable
-- numbering of the previous statement to be the current variable
-- numbering for the next statement.
finishStmt :: ClauseComp ()
finishStmt = getCurrNumbering >>= putNumberings


-- |Return a list of prims to complete a proc body.  For a SemiDet body
-- that hasn't already had $$ assigned a value, this will assign it
-- True; otherwise it'll be empty.
closingStmts :: Determinism -> ClauseComp [Placed Prim]
closingStmts Det = return []
closingStmts SemiDet = do
    tested <- Map.member "$$" <$> getCurrNumbering
    return $ if tested
             then []
             else [Unplaced $ primMove
                   (ArgInt 1 boolType)
                   (ArgVar (PrimVarName "$$" 0) boolType False
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
        unless (procDetism proc == Det)
          $ shouldnt $ "SemiDet proc left by unbranching:  "
                       ++ showProcDef 4 proc
        let ProcDefSrc body = procImpln proc
        let proto = procProto proc
        let params = procProtoParams proto
        modify (\st -> st {nextCallSiteID = (procCallSiteCount proc)})
        logClause $ "--------------\nCompiling proc " ++ show proto
        mapM_ (nextVar . paramName) $ List.filter (flowsIn . paramFlow) params
        finishStmt
        startVars <- getCurrNumbering
        compiled <- compileBody body params Det
        logClause $ "Compiled to:"  ++ showBlock 4 compiled
        endVars <- getCurrNumbering
        logClause $ "  startVars: " ++ show startVars
        logClause $ "  endVars  : " ++ show endVars
        logClause $ "  params   : " ++ show params
        let params' = List.map (compileParam startVars endVars) params
        let proto' = PrimProto (procProtoName proto) params'
        logClause $ "  comparams: " ++ show params'
        callSiteCount <- gets nextCallSiteID
        return $ proc { procImpln = ProcDefPrim proto' compiled
                                        emptyProcAnalysis Map.empty,
                        procCallSiteCount = callSiteCount}



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
        Cond tst thn els _ ->
          case content tst of
              TestBool var -> do
                front <- mapM compileSimpleStmt $ init stmts
                compileCond front (place final) var thn els params detism
              tstStmt ->
                shouldnt $ "CompileBody of Cond with non-simple test:\n"
                           ++ show tstStmt
        -- XXX There shouldn't be any semidet code here any more
        call@(ProcCall maybeMod name procID SemiDet _ args)
          | detism == SemiDet -> do
          logClause $ "Compiling SemiDet tail call " ++ showStmt 4 call
          args' <- mapM (placedApply compileArg) args
          front <- mapM compileSimpleStmt $ init stmts
          callSiteID <- gets nextCallSiteID
          let final' = Unplaced
                       $ PrimCall callSiteID
                         (ProcSpec maybeMod name
                                   (trustFromJust
                                    ("compileBody for " ++ showStmt 4 call)
                                     procID) generalVersion)
                         (args' ++
                          [ArgVar (PrimVarName "$$" 0) boolType False FlowOut
                           (Implicit Nothing) False])
          return $ ProcBody (front++[final']) NoFork

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
          beforeTest <- getCurrNumbering
          thn' <- compileBody thn params detism
          afterThen <- getCurrNumbering
          logClause $ "  vars after then: " ++ show afterThen
          putNumberings beforeTest
          els' <- compileBody els params detism
          afterElse <- getCurrNumbering
          logClause $ "  vars after else: " ++ show afterElse
          let final = Map.intersectionWith max afterThen afterElse
          putNumberings final
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
    finishStmt
    logClause $ "Compiled to " ++ show stmt'
    return $ maybePlace stmt' (place stmt)

compileSimpleStmt' :: Stmt -> ClauseComp Prim
compileSimpleStmt' call@(ProcCall maybeMod name procID _ _ args) = do
    logClause $ "Compiling call " ++ showStmt 4 call
    callSiteID <- gets nextCallSiteID
    modify (\st -> st {nextCallSiteID = callSiteID + 1})
    args' <- mapM (placedApply compileArg) args
    return $ PrimCall callSiteID (ProcSpec maybeMod name
                       (trustFromJust
                       ("compileSimpleStmt' for " ++ showStmt 4 call)
                       procID) generalVersion)
        args'
compileSimpleStmt' (ForeignCall lang name flags args) = do
    args' <- mapM (placedApply compileArg) args
    return $ PrimForeign lang name flags args'
compileSimpleStmt' (TestBool expr) =
    -- Only for handling a TestBool other than as the condition of a Cond:
    compileSimpleStmt' $ content $ move (boolCast expr) (boolVarSet "$$")
compileSimpleStmt' Nop = return $ PrimTest $ ArgInt 1 intType
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


compileArg :: Exp -> OptPos -> ClauseComp PrimArg
compileArg exp pos = do
    logClause $ "Compiling expression " ++ show exp
    arg <- compileArg' AnyType False exp pos
    logClause $ "Expression compiled to " ++ show arg
    return arg

compileArg' :: TypeSpec -> Bool -> Exp -> OptPos -> ClauseComp PrimArg
compileArg' typ _ (IntValue int) _ = return $ ArgInt int typ
compileArg' typ _ (FloatValue float) _ = return $ ArgFloat float typ
compileArg' typ _ (StringValue string) _ = return $ ArgString string typ
compileArg' typ _ (CharValue char) _ = return $ ArgChar char typ
compileArg' typ coerce (Var name ParamIn flowType) pos = do
    name' <- currVar name pos
    return $ ArgVar name' typ coerce FlowIn flowType False
compileArg' typ coerce (Var name ParamOut flowType) _ = do
    name' <- nextVar name
    return $ ArgVar name' typ coerce FlowOut flowType False
compileArg' _   _ (Typed exp typ coerce) pos = compileArg' typ coerce exp pos
compileArg' _   _ arg _ =
    shouldnt $ "Normalisation left complex argument: " ++ show arg


reconcilingAssignments :: Numbering -> Numbering
                       -> [Param] -> [Placed Prim]
reconcilingAssignments caseVars jointVars params =
    Maybe.mapMaybe (reconcileOne caseVars jointVars) params


reconcileOne :: Numbering -> Numbering -> Param
             -> Maybe (Placed Prim)
reconcileOne caseVars jointVars (Param name ty flow ftype) =
    case (Map.lookup name caseVars,
          Map.lookup name jointVars)
    of (Just caseNum, Just jointNum) ->
         if caseNum /= jointNum && elem flow [ParamOut, ParamInOut]
         then Just $ Unplaced $
              PrimForeign "llvm" "move" []
              [ArgVar (PrimVarName name caseNum) ty False FlowIn
                      Ordinary False,
               ArgVar (PrimVarName name jointNum) ty False FlowOut
                      Ordinary False]
         else Nothing
       _ -> Nothing


compileParam :: Numbering -> Numbering -> Param -> PrimParam
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
