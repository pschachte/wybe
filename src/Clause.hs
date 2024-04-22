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
import           UnivSet                           as USet
import           Options                           (LogSelection (Clause))
import           Snippets
import           Text.ParserCombinators.Parsec.Pos
import           Util
import           Resources
import UnivSet (emptyUnivSet)
import AST (emptyGlobalFlows)


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
        nextCallSiteID :: CallSiteID,  -- ^The next callSiteID to use
        clauseImpurity :: Impurity     -- ^Impurity of the enclosing proc
        }


initClauseComp :: Impurity -> ClauseCompState
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
            logClause $ "Found uninitialised variable " ++ name
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
finishStmt = do
    getCurrNumbering >>= putNumberings
    gets currVars >>= logClause . (("Finish with numbering " ++) . show)

-- |Return a list of prims to complete a proc body.  For a SemiDet body
-- that hasn't already had #success assigned a value, this will assign it
-- True; otherwise it'll be empty.
closingStmts :: Determinism -> [Param] -> ClauseComp [Placed Prim]
closingStmts detism params = do
    dict <- gets currVars
    let outs = List.filter (flowsOut . paramFlow) params
    logClause $ "Closing body with output parameters: " ++ show outs
    let undefs = List.filter (not . (`Map.member` dict) . paramName) outs
    logClause $ "  uninitialised outputs: " ++ show undefs
    assigns <- mapM (\Param{paramName=nm,paramType=ty}
                    -> assign nm ty (ArgUndef ty))
                    undefs
    tested <- Map.member outputStatusName <$> getCurrNumbering
    end <- if detism == SemiDet && not tested
               then (:assigns) <$> assign outputStatusName boolType (ArgInt 1 boolType)
               else return assigns
    logClause $ "Adding ending instructions: " ++ showPlacedPrims 4 end
    return end

-- |Return a prim to assign the specified value to the specified variable of the
-- specified type, and record the assignment.
assign :: String -> TypeSpec -> PrimArg -> ClauseComp (Placed Prim)
assign name typ val = do
    primVar <- nextVar name
    return $ Unplaced $ primMove val
           $ ArgVar primVar typ FlowOut Ordinary False


-- |Run a clause compiler function from the Compiler monad to compile
--  a generated procedure.
evalClauseComp :: Impurity -> ClauseComp t -> Compiler t
evalClauseComp impurity clcomp =
    evalStateT clcomp $ initClauseComp impurity


-- |Compile a ProcDefSrc to a ProcDefPrim, ie, compile a proc
--  definition in source form to one in clausal form.
compileProc :: ProcDef -> Int -> Compiler ProcDef
compileProc proc procID =
    evalClauseComp (procImpurity proc) $ do
        let ProcDefSrc body = procImpln proc
        let proto = procProto proc
        let procName = procProtoName proto
        let params = content <$> procProtoParams proto
        modify (\st -> st {nextCallSiteID=procCallSiteCount proc})
        logClause $ "--------------\nCompiling proc " ++ show proto
        mapM_ (nextVar . paramName) $ List.filter (flowsIn . paramFlow) params
        finishStmt
        startVars <- getCurrNumbering
        compiled <- compileBody body params Det
        logClause $ "Compiled to  :"  ++ showBlock 4 compiled
        endVars <- getCurrNumbering
        logClause $ "  startVars  : " ++ show startVars
        logClause $ "  endVars    : " ++ show endVars
        logClause $ "  params     : " ++ show params
        let idxs = scanl (\i f -> i + if flowsIn f && flowsOut f then 2 else 1) 0 $ paramFlow <$> params
            params' = concat $ zipWith (compileParam gFlows startVars endVars procName) idxs params
            gFlows  = makeGlobalFlows (zip [0..] params') $ procProtoResources proto
        let proto' = PrimProto (procProtoName proto) params' gFlows
        logClause $ "  comparams  : " ++ show params'
        logClause $ "  globalFlows: " ++ show gFlows 
        callSiteCount <- gets nextCallSiteID
        mSpec <- lift $ getModule modSpec
        let pSpec = ProcSpec mSpec procName procID Set.empty
        return $ proc { procImpln = ProcDefPrim pSpec proto' compiled
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
compileBody [] params detism = do
    logClause $ "Compiling empty body"
    end <- closingStmts detism params
    logClause $ "Compiling empty body produced:" ++ showPlacedPrims 4 end
    return $ ProcBody end NoFork
compileBody stmts params detism = do
    logClause $ "Compiling body:" ++ showBody 4 stmts
    let final = last stmts
    case content final of
        Cond tst thn els _ _ _ ->
          case content tst of
              TestBool var -> do
                front <- mapM compileSimpleStmt $ init stmts
                compileCond front (place final) var thn els params detism
              tstStmt ->
                shouldnt $ "CompileBody of Cond with non-simple test:\n"
                           ++ show tstStmt
        -- XXX There shouldn't be any semidet code here any more
        call@(ProcCall _ SemiDet _ _) ->
            shouldnt "compileBody of SemiDet call"
        _ -> do
          prims <- mapM compileSimpleStmt stmts
          end <- closingStmts detism params
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
                Nothing
        _ ->
            shouldnt $ "TestBool with invalid argument " ++ show expr

-- |Add the specified statements at the end of the given body
appendToBody :: ProcBody -> [Placed Prim] -> ProcBody
appendToBody (ProcBody prims NoFork) after
    = ProcBody (prims++after) NoFork
appendToBody (ProcBody prims (PrimFork v ty lst bodies deflt)) after
    = let bodies' = List.map (`appendToBody` after) bodies
      in ProcBody prims $ PrimFork v ty lst bodies'
                            $ (`appendToBody` after) <$> deflt

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
compileSimpleStmt' call@(ProcCall func _ _ args) = do
    logClause $ "Compiling call " ++ showStmt 4 call
    callSiteID <- gets nextCallSiteID
    modify (\st -> st {nextCallSiteID = callSiteID + 1})
    args' <- concat <$> mapM (placedApply compileArg) args
    impurity <- gets clauseImpurity
    case func of
        First mod name procID -> do
            let procID' = trustFromJust ("compileSimpleStmt' for " ++ showStmt 4 call)
                            procID
            let pSpec = ProcSpec mod name procID' generalVersion
            impurity' <- max impurity . procImpurity <$> lift (getProcDef pSpec)
            gFlows <- lift $ getProcGlobalFlows pSpec
            return $ PrimCall callSiteID pSpec impurity  args' gFlows
        Higher fn -> do
            fn' <- compileHigherFunc fn
            return $ PrimHigher callSiteID fn' impurity args'
compileSimpleStmt' (ForeignCall lang name flags args) = do
    args' <- concat <$> mapM (placedApply compileArg) args
    return $ PrimForeign lang name flags args'
compileSimpleStmt' (TestBool expr) =
    -- Only for handling a TestBool other than as the condition of a Cond:
    compileSimpleStmt' $ content $ move (boolCast expr) (boolVarSet outputStatusName)
compileSimpleStmt' Nop =
    compileSimpleStmt' $ content $ move boolTrue (boolVarSet outputStatusName)
compileSimpleStmt' Fail =
    compileSimpleStmt' $ content $ move boolFalse (boolVarSet outputStatusName)
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


compileArg :: Exp -> OptPos -> ClauseComp [PrimArg]
compileArg (Typed exp typ coerce) pos = do
    logClause $ "Compiling expression " ++ show exp
    args <- compileArg' typ exp pos
    logClause $ "Expression compiled to " ++ show args
    return args
compileArg exp pos = shouldnt $ "Compiling untyped argument " ++ show exp

compileArg' :: TypeSpec -> Exp -> OptPos -> ClauseComp [PrimArg]
compileArg' typ (IntValue int) _ = return [ArgInt int typ]
compileArg' typ (FloatValue float) _ = return [ArgFloat float typ]
compileArg' typ (StringValue string v) _ = return [ArgString string v typ]
compileArg' typ (CharValue char) _ = return [ArgChar char typ]
compileArg' typ (Global info) _ = return [ArgGlobal info typ]
compileArg' typ (Closure ms es) _ = do
    as <- concat <$> mapM (placedApply compileArg) es
    unless (sameLength es as)
           $ shouldnt "compileArg' Closure with in/out args"
    return [ArgClosure ms as typ]
compileArg' typ FailExpr _ = return [ArgInt 0 typ]
compileArg' typ var@(Var name flow flowType) pos = do
    inArg <- if flowsIn flow
        then do
            currName <- currVar name pos
            return [ArgVar currName typ FlowIn flowType False]
        else return []
    outArg <- if flowsOut flow
        then do
            nextName <- nextVar name
            return [ArgVar nextName typ FlowOut flowType False]
        else return []
    return $ inArg ++ outArg
compileArg' _ (Typed exp _ _) pos =
    shouldnt $ "Compiling multi-typed expression " ++ show exp
compileArg' typ arg _ =
    shouldnt $ "Normalisation left complex argument: " ++ show arg

compileHigherFunc :: Placed Exp -> ClauseComp PrimArg
compileHigherFunc exp = do
    exps' <- placedApply compileArg exp
    case exps' of
        [arg] -> return arg
        _ -> shouldnt $ "compileHigherFunc of " ++ show exp


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
              [ArgVar (PrimVarName name caseNum) ty FlowIn
                      ftype False,
               ArgVar (PrimVarName name jointNum) ty FlowOut
                      ftype False]
         else Nothing
       _ -> Nothing


compileParam :: GlobalFlows -> Numbering -> Numbering -> ProcName -> Int -> Param -> [PrimParam]
compileParam allFlows startVars endVars procName idx param@(Param name ty flow ftype) =
    [PrimParam (PrimVarName name num) ty FlowIn ftype (ParamInfo False gFlows)
    | flowsIn flow
    , let num = Map.findWithDefault
                (shouldnt ("compileParam for input param " ++ show param
                            ++ " of proc " ++ show procName))
                name startVars
          gFlows 
            | (isResourcefulHigherOrder ||| genericType) ty 
            = emptyGlobalFlows{globalFlowsParams=USet.singleton inIdx}
            | otherwise = emptyGlobalFlows
    ]
    ++ 
    [PrimParam (PrimVarName name num) ty FlowOut ftype (ParamInfo False gFlows)
    | flowsOut flow
    , let num = Map.findWithDefault
                (shouldnt ("compileParam for output param " ++ show param
                            ++ " of proc " ++ show procName))
                name endVars
          gFlows 
            | isResourcefulHigherOrder ty = univGlobalFlows
            | genericType ty = emptyGlobalFlows{globalFlowsParams=UniversalSet}
            | otherwise = emptyGlobalFlows
    ]
  where 
    inIdx = idx
    outIdx = if flowsIn flow then idx + 1 else idx


-- |A synthetic output parameter carrying the test result
testOutParam :: Param
testOutParam = Param outputStatusName boolType ParamOut Ordinary


-- |Log a message, if we are logging clause generation.
logClause :: String -> ClauseComp ()
logClause s = lift $ logMsg Clause s
