--  File     : Flatten.hs
--  Author   : Peter Schachte
--  Purpose  : Flatten function calls (expressions) into procedure calls
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
-- BEGIN MAJOR DOC
--  We transform away all expression types except for constants and
--  variables.  Where, let, conditional, and function call
--  expressions are turned into statements that bind a variable, and
--  then the variable is used in place of the expression.  All function
--  calls are transformed into procedure calls by adding an extra
--  argument corresponding to the function result.
--
--  Function call expressions can take one of three forms.  Expressions
--  where all arguments are inputs are turned into a procedure call
--  with a fresh temporary variable as an output, which is called before
--  the statement in which that function call appears.  The function
--  call itself is then replaced by a referenced to the temporary
--  variable.  For example, p(f(x,y),z) is replaced by f(x,y,?t); p(t,z).
--
--  A function call containing some output arguments, and perhaps some
--  inputs, is transformed into a fresh input variable, with a later
--  proc call to that function with that variable as an added input.
--  For example, p(f(?x,y),z) is transformed to p(?t,z); f(?x,y,t).

--  Finally, a function call containing some input-output arguments,
--  and perhaps some input arguments, is transformed into an
--  input-output variable, plus two procedure calls, one to compute
--  the initial value of the expression, and a second to assign it
--  the specified new value.  For example, a statement p(f(!x,y),z) is
--  transformed to f(x,y,?t); p(!t,z); f(!x,y,t).
-- END MAJOR DOC
--
----------------------------------------------------------------

module Flatten (flattenProcDecl) where

import AST
import Debug.Trace
import Snippets
import Options (LogSelection(Flatten))
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Maybe
import Text.ParserCombinators.Parsec.Pos
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans (lift,liftIO)
import Distribution.Simple.Test.Log (TestSuiteLog(logFile))
import Data.Type.Equality (inner)


----------------------------------------------------------------
--                        Exported Functions
----------------------------------------------------------------

flattenProcDecl :: Item -> Compiler (Item,Int)
flattenProcDecl (ProcDecl vis mods proto stmts pos) = do
    let params = procProtoParams proto
    logMsg Flatten $ "** Flattening "
           ++ "def " ++ showProcModifiers' mods
           ++ show proto ++ " {" ++ showBody 4 stmts ++ "}"
    let inParams = Set.fromList $
                   List.map paramName $
                   List.filter (flowsIn . paramFlow) $
                   procProtoParams proto
    let inResources = Set.map (resourceName . resourceFlowRes) $
                   Set.filter (flowsIn . resourceFlowFlow) $
                   procProtoResources proto
    (stmts',tmpCtr) <- flattenBody stmts (inParams `Set.union` inResources)
                       (modifierDetism mods)
    return (ProcDecl vis mods proto stmts' pos,tmpCtr)
flattenProcDecl _ =
    shouldnt "flattening a non-proc item"


-- |Flatten the specified statement sequence given a set of input parameter
-- and resource names.
flattenBody :: [Placed Stmt] -> Set VarName -> Determinism
            -> Compiler ([Placed Stmt],Int)
flattenBody stmts varSet detism = do
    logMsg Flatten $ "Flattening body" ++ showBody 4 stmts
    logMsg Flatten $ "Flattening with parameters = " ++ show varSet
    let varSet' = foldStmts const insertOutVar varSet stmts
    logMsg Flatten $ "Flattening with all vars = " ++ show varSet'
    finalState <- execStateT (flattenStmts stmts detism)
                  $ initFlattenerState varSet'
    return (List.reverse (flattened finalState), tempCtr finalState)


-- | Insert the expression var name if it's an output variable; otherwise leave
-- the variable set alone.
insertOutVar :: Set VarName -> Exp -> Set VarName
insertOutVar varSet (Var name ParamOut _) = Set.insert name varSet
insertOutVar varSet expr = varSet


----------------------------------------------------------------
--                       The Flattener Monad
----------------------------------------------------------------

-- |The Flattener monad is a state transformer monad carrying the 
--  flattener state over the compiler monad.
type Flattener = StateT FlattenerState Compiler


data FlattenerState = Flattener {
    flattened     :: [Placed Stmt], -- ^Flattened code generated, reversed
    postponed     :: [Placed Stmt], -- ^Flattened code to come after
    anonProcState :: AnonProcState, -- ^Information we know about anon procs
    tempCtr       :: Int,           -- ^Temp variable counter
    currPos       :: OptPos,        -- ^Position of current statement
    stmtDefs      :: Set VarName,   -- ^Variables defined by this statement
    defdVars      :: Set VarName    -- ^Variables defined somewhere in this
                                    -- proc body
    }

data AnonProcState = AnonProcState {
    totalAnons  :: Integer,      -- ^Total number of anon proc encountered
    currentAnon :: Integer,      -- ^Current anon proc number
    paramCount :: Maybe Integer, -- ^Number of params encountered in current
                                 -- anonProc. Nothing if we have numbered params
    params :: Map Integer Param  -- ^Unrocessed params
    }


initFlattenerState :: Set VarName -> FlattenerState
initFlattenerState = Flattener [] [] initAnonProcState 0 Nothing Set.empty


initAnonProcState :: AnonProcState
initAnonProcState = AnonProcState 0 0 (Just 0) Map.empty


pushAnonProcState :: AnonProcState -> AnonProcState
pushAnonProcState (AnonProcState t _ _ _) = 
    let t' = t + 1
    in initAnonProcState{totalAnons=t', currentAnon=t'}


popAnonProcState :: AnonProcState -> AnonProcState -> AnonProcState
popAnonProcState old@AnonProcState{} (AnonProcState t _ _ _) = old{totalAnons=t}


processAnonProcParams :: AnonProcState -> [Param]
processAnonProcParams AnonProcState{params=paramMap, currentAnon=current} 
    | Map.null paramMap = []
    | otherwise = List.map 
                    (\i -> Map.findWithDefault 
                            (makeAnonParam (makeAnonParamName current i) ParamIn)
                            i paramMap) 
                    [1 .. Set.findMax (Map.keysSet paramMap)]


makeAnonParamName :: Integer -> Integer -> VarName 
makeAnonParamName procNum num = specialName2 (show procNum) (show num)


makeAnonParam :: VarName -> FlowDirection -> Param 
makeAnonParam name flow = Param name AnyType flow Ordinary 



emit :: OptPos -> Stmt -> Flattener ()
emit pos stmt = do
    logFlatten $ "-- Emitting:  " ++ showStmt 14 stmt
    modify (\s -> s { flattened = maybePlace stmt pos:flattened s })


postpone :: OptPos -> Stmt -> Flattener ()
postpone pos stmt = do
    logFlatten $ "-- Postponing:  " ++ showStmt 14 stmt
    modify (\s -> s { postponed = maybePlace stmt pos:postponed s })


-- |Return a fresh variable name.
tempVar :: Flattener VarName
tempVar = do
    ctr <- gets tempCtr
    modify (\s -> s { tempCtr = ctr + 1 })
    return $ mkTempName ctr


-- |Run a flattener, ignoring its state changes except for the temp variable
--  counter.  If transparent is True, also keep changes to the set of defined
--  variables.  If isLoop is True, then flatten any loop initialisations
--  accumulated while processing the body so they are executed before entering
--  the loop; otherwise, just preserve the accumulated initialisations.
flattenInner :: Bool -> Bool -> Determinism
             -> Flattener t -> Flattener [Placed Stmt]
flattenInner isLoop transparent detism inner = do
    oldState <- get
    (_,innerState) <-
        lift (runStateT inner
              (initFlattenerState (defdVars oldState)) {
                    tempCtr = tempCtr oldState})
    logFlatten $ "-- Flattened:" ++ showBody 4 (List.reverse
                                                $ flattened innerState)
    -- logFlatten $ "-- Postponed:\n" ++ 
    --   showBody 4 (postponed innerState)
    if transparent
      then put $ oldState { tempCtr = tempCtr innerState,
                            defdVars = defdVars innerState }
      else put $ oldState { tempCtr = tempCtr innerState }
    return $ List.reverse $ flattened innerState


flattenStmtArgs :: [Placed Exp] -> OptPos -> Flattener [Placed Exp]
flattenStmtArgs args pos = do
    modify (\s -> s { stmtDefs = Set.empty, currPos = pos})
    currPostponed <- gets postponed
    unless (List.null currPostponed)
        $ shouldnt "postponed stmts remain on starting stmt flattening"
    flattenArgs args


flushPostponed ::  Flattener ()
flushPostponed = do
    currPostponed <- gets postponed
    modify (\s -> s  {flattened = reverse currPostponed ++ flattened s,
                      postponed = []})

-- | Record a variable definition.  Report an error if it was already defined in
-- the same statement.
noteVarDef :: VarName -> Flattener ()
noteVarDef var = do
    redef <- gets (Set.member var . stmtDefs)
    when redef
      (do
            pos <- gets currPos
            lift $ message Error
              ("Variable '" ++ var ++
               "' multiply defined in a single statement")
              pos
      )
    modify (\s -> s { stmtDefs = Set.insert var $ stmtDefs s })


-- | Note a variable mention; if it is an output mode, record the definition.
noteVarMention :: VarName -> FlowDirection -> Flattener ()
noteVarMention name dir = do
    when (flowsOut dir) $ noteVarDef name


-- | Note that the specified variable has been introduced, so it is a known
-- variable.  It's not an error if it was previously defined or introduced.
noteVarIntro :: VarName -> Flattener ()
noteVarIntro name =
    modify (\s -> s {defdVars = Set.insert name $ defdVars s})

----------------------------------------------------------------
--                      Flattening Statements
----------------------------------------------------------------

-- |Flatten the specified statements to primitive statements, in a context
--  whose determinism is as specified.
flattenStmts :: [Placed Stmt] -> Determinism -> Flattener ()
flattenStmts stmts detism =
    mapM_ (\pstmt -> flattenStmt (content pstmt) (place pstmt) detism) stmts


flattenStmt :: Stmt -> OptPos -> Determinism -> Flattener ()
flattenStmt stmt pos detism = do
    modify (\s -> s { stmtDefs = Set.empty,
                      currPos = pos})
    defd <- gets defdVars
    logFlatten $ "flattening " ++ show detism ++ " stmt " ++ showStmt 4 stmt ++
      " with defined vars " ++ show defd
    flattenStmt' stmt pos detism


-- |Flatten the specified statement
flattenStmt' :: Stmt -> OptPos -> Determinism -> Flattener ()
flattenStmt' stmt@(ProcCall (First [] "=" id) callDetism res [arg1,arg2]) pos detism = do
    let arg1content = innerExp $ content arg1
    let arg2content = innerExp $ content arg2
    let arg1Vars = expOutputs arg1content
    let arg2Vars = expOutputs arg2content
    logFlatten $ "Flattening assignment with outputs " ++ show arg1Vars
                 ++ " and " ++ show arg2Vars
    case (arg1content, arg2content) of
      (Var var flow1 _, _)
        | callDetism == Det && flowsOut flow1 && Set.null arg2Vars -> do
        logFlatten $ "Transforming assignment " ++ showStmt 4 stmt
        arg1' <- flattenAnonParam (content arg1) AnyType Nothing (place arg1)
        flattenAssignment (expVar $ content arg1') arg1' arg2 pos
      (_, Var var flow2 _)
        | callDetism == Det && flowsOut flow2 && Set.null arg1Vars -> do
        logFlatten $ "Transforming assignment " ++ showStmt 4 stmt
        arg1' <- flattenAnonParam (content arg1) AnyType Nothing (place arg1)
        flattenAssignment var arg2 arg1' pos
      (Fncall mod name args, _)
        | not (Set.null arg1Vars) && Set.null arg2Vars -> do
        let stmt' = ProcCall (First mod name Nothing) Det False (args++[arg2])
        flattenStmt stmt' pos detism
      (_, Fncall mod name args)
        | not (Set.null arg2Vars) && Set.null arg1Vars -> do
        arg1' <- flattenAnonParam (content arg1) AnyType Nothing (place arg1)
        let stmt' = ProcCall  (First mod name Nothing) Det False (args++[arg1'])
        flattenStmt stmt' pos detism
      (_,_) | Set.null arg1Vars && Set.null arg2Vars -> do
        logFlatten $ "Leaving equality test alone: " ++ showStmt 4 stmt
        args' <- flattenStmtArgs [arg1,arg2] pos
        emit pos $ ProcCall (First [] "=" id) Det res args'
        flushPostponed
      _ -> do
        -- Must be a mode error:  both sides want to bind variables
        logFlatten $ "Error: out=out assignment " ++ show stmt
        lift $ message Error "Cannot generate bindings on both sides of '='" pos
flattenStmt' stmt@(ProcCall (First [] "fail" _) _ _ []) pos _ =
    emit pos Fail
flattenStmt' stmt@(ProcCall (First [] "break" _) _ _ []) pos _ =
    emit pos Break
flattenStmt' stmt@(ProcCall (First [] "next" _) _ _ []) pos _ =
    emit pos Next
flattenStmt' stmt@(ProcCall (First [] name _) _ banged []) pos _ = do
    defined <- gets defdVars
    -- Convert call to no-arg proc to a bool variable test if there's a
    -- local variable with that name
    if name `elem` defined && not banged
        then emit pos $ TestBool $ Var name ParamIn Ordinary
        else emit pos stmt
flattenStmt' (ProcCall func detism res args) pos d = do
    logFlatten "   call is Det"
    args' <- flattenStmtArgs args pos
    emit pos $ ProcCall func detism res args'
    flushPostponed
flattenStmt' (ForeignCall lang name flags args) pos _ = do
    args' <- flattenStmtArgs args pos
    emit pos $ ForeignCall lang name flags args'
    flushPostponed
-- XXX must handle Flattener state more carefully.  Defined variables need
--     to be retained between condition and then branch, but forgotten for
--     the else branch.  Also note that 'transparent' arg to flattenInner is
--     always False
flattenStmt' (Cond tstStmt thn els condVars defVars) pos detism = do
    tstStmt' <- seqToStmt <$> flattenInner False True SemiDet
                (placedApply flattenStmt tstStmt SemiDet)
    thn' <- flattenInner False False detism (flattenStmts thn detism)
    els' <- flattenInner False False detism (flattenStmts els detism)
    emit pos $ Cond tstStmt' thn' els' condVars defVars
flattenStmt' (Case pexpr cases deflt) pos detism = do
    pexpr' <- flattenPExp pexpr
    flattenStmts (translateCases pexpr' pos cases deflt) detism
flattenStmt' (TestBool expr) pos SemiDet = do
    pexpr' <- flattenPExp $ Unplaced expr
    case pexpr' of
        Unplaced expr' -> emit pos $ TestBool expr'
        _ -> shouldnt $ "Flatten expr " ++ show expr
                        ++ " produced " ++ show pexpr'
flattenStmt' (TestBool expr) _pos detism =
    shouldnt $ "TestBool " ++ show expr ++ " in " ++ show detism ++ " context"
flattenStmt' (And tsts) pos SemiDet = do
    tsts' <- flattenInner False True SemiDet (flattenStmts tsts SemiDet)
    emit pos $ And tsts'
flattenStmt' stmt@And{} _pos detism =
    shouldnt $ "And in a " ++ show detism ++ " context"
flattenStmt' (Or tsts vars) pos SemiDet = do
    tsts' <- flattenInner False True SemiDet (flattenStmts tsts SemiDet)
    emit pos $ Or tsts' vars
flattenStmt' (Or tstStmts _) _pos detism =
    shouldnt $ "Or in a " ++ show detism ++ " context"
flattenStmt' (Not tstStmt) pos SemiDet = do
    tstStmt' <- seqToStmt <$> flattenInner False True SemiDet
                (placedApply flattenStmt tstStmt SemiDet)
    emit pos $ Not tstStmt'
flattenStmt' (Not tstStmt) _pos detism =
    shouldnt $ "negation in a " ++ show detism ++ " context"
flattenStmt' (Loop body defVars) pos detism = do
    body' <- flattenInner True False detism
             (flattenStmts (body ++ [Unplaced Next]) detism)
    emit pos $ Loop body' defVars
flattenStmt' for@(For pgens body) pos detism = do
    -- For loops are transformed into `do` loops
    -- E.g. for i in x, j in y {
    --          <stmts>
    --      }
    -- will be transformed into
    -- ?temp1 = x
    -- ?temp2 = y
    -- do {
    --     if { `[|]`(?i, ?temp1, temp1) :: 
    --          if { `[|]`(?j, ?temp2, temp2) ::
    --              <stmts>
    --          | else :: break
    --          }
    --     | else :: break
    --     }
    -- }
    logFlatten $ "Generating for " ++ showStmt 4 for
    let (gens, poss) = unzip $ unPlace <$> pgens
    temps <- mapM (const tempVar) gens
    -- XXX Should check for input only    
    origs <- mapM (flattenPExp . genExp) gens
    let instrs = zipWith (\orig temp ->
                            ForeignCall "llvm" "move" []
                                [orig, Unplaced $ varSet temp])
                    origs temps
    mapM_ (emit pos) instrs
    modify (\s -> s {defdVars = Set.union (Set.fromList temps) $ defdVars s})
    let loop = List.foldr 
                (\(var, gen, pos') loop -> 
                    [Unplaced $ Cond (ProcCall (First [] "[|]" Nothing) SemiDet False 
                                        [var,
                                         Unplaced $ Var gen ParamOut Ordinary,
                                         Unplaced $ Var gen ParamIn Ordinary]
                                      `maybePlace` pos')
                                loop [Unplaced Break]
                      Nothing Nothing]
                ) body $ zip3 (loopVar <$> gens) temps poss
    let generated = Loop loop Nothing
    logFlatten $ "Generated for: " ++ showStmt 4 generated
    flattenStmt' generated pos detism
flattenStmt' (UseResources res old body) pos detism = do
    oldVars <- gets defdVars
    mapM_ (noteVarIntro . resourceName) res
    body' <- flattenInner False True detism (flattenStmts body detism)
    modify $ \s -> s { defdVars = oldVars}
    emit pos $ UseResources res old body'
flattenStmt' Nop pos _ = emit pos Nop
flattenStmt' Fail pos _ = emit pos Fail
flattenStmt' Break pos _ = emit pos Break
flattenStmt' Next pos _ = emit pos Next


flattenAssignment :: Ident -> Placed Exp -> Placed Exp -> OptPos -> Flattener ()
flattenAssignment var varArg value pos = do
    [valueArg] <- flattenStmtArgs [value] pos
    let instr = ForeignCall "llvm" "move" [] [valueArg, varArg]
    logFlatten $ "  transformed to " ++ showStmt 4 instr
    noteVarDef var
    emit pos instr
    flushPostponed


translateCases :: Placed Exp -> OptPos -> [(Placed Exp,[Placed Stmt])]
               -> Maybe [Placed Stmt] -> [Placed Stmt]
translateCases val pos [] Nothing = [Unplaced Fail]
translateCases val pos [] (Just deflt) = deflt
translateCases val pos ((key,body):rest) deflt =
    [maybePlace
     (Cond (maybePlace (ProcCall (First [] "=" Nothing) SemiDet False [key,val])
                       (place key))
           body
           (translateCases val pos rest deflt)
           Nothing Nothing)
     pos]
     where testPos = place key


----------------------------------------------------------------
--                      Flattening Expressions
----------------------------------------------------------------

-- |Compile a list of expressions as proc call arguments to a list of 
--  primitive arguments, a list of statements to execute before the 
--  call to bind those arguments, and a list of statements to execute 
--  after the call to store the results appropriately.
flattenArgs :: [Placed Exp] -> Flattener [Placed Exp]
flattenArgs args = do
    logFlatten $ "  Flattening arglist " ++ show args
    argListList <- mapM flattenPExp args
    logFlatten $ "  Flattened =   " ++ show argListList
    return argListList


flattenPExp :: Placed Exp -> Flattener (Placed Exp)
flattenPExp pexp = do
    vs <- gets defdVars
    logFlatten $ "  Flattening exp " ++ show pexp ++ ", with vars " ++
           show vs
    result <- flattenExp (content pexp) AnyType Nothing (place pexp)
    logFlatten $ "  Result =   " ++ show result
    return result


-- |Flatten a single expressions with specified flow direction to
--  primitive argument(s), a list of statements to execute
--  to bind it, and a list of statements to execute 
--  after the call to store the result appropriately.
--  The first part of the output (a Placed Exp) will always be a list
--  of only atomic Exps and Var references (in any direction).
-- XXX Does this need to support SemiDet (partial) expressions?
flattenExp :: Exp -> TypeSpec -> Maybe TypeSpec -> OptPos
           -> Flattener (Placed Exp)
flattenExp expr@(IntValue _) ty castFrom pos =
    return $ typeAndPlace expr ty castFrom pos
flattenExp expr@(FloatValue _) ty castFrom pos =
    return $ typeAndPlace expr ty castFrom pos
flattenExp expr@(StringValue _ _) ty castFrom pos =
    return $ typeAndPlace expr ty castFrom pos
flattenExp expr@(CharValue _) ty castFrom pos =
    return $ typeAndPlace expr ty castFrom pos
flattenExp expr@(Var "_" ParamIn _) ty castFrom pos = do
    dummyName <- tempVar
    return $ typeAndPlace (Var dummyName ParamOut Ordinary) AnyType castFrom pos
flattenExp expr@(Var name dir _) ty castFrom pos = do
    logFlatten $ "  Flattening arg " ++ show expr
    defd <- gets (Set.member name . defdVars)
    if dir == ParamIn && not defd
    then do -- Reference to an undefined variable: assume it's meant to be
            -- a niladic function instead of a variable reference
        logFlatten $ "  Unknown variable '" ++ show name
            ++ "' flattened to niladic function call"
        flattenCall (ProcCall (regularProc name) Det False) False ty castFrom pos []
    else do
        when (flowsOut dir) $ noteVarIntro name
        noteVarMention name dir
        let expr' = typeAndPlace expr ty castFrom pos
        logFlatten $ "  Arg flattened to " ++ show expr'
        return expr'
flattenExp expr@(AnonParamVar _ _) ty castFrom pos = 
    flattenAnonParam expr ty castFrom pos
flattenExp expr@(ProcRef ms es) ty castFrom pos = do
    es' <- (content <$>) <$> mapM (flattenPExp . Unplaced) es
    return $ typeAndPlace (ProcRef ms es') ty castFrom pos
flattenExp (Where stmts pexp) _ _ _ = do
    flattenStmts stmts Det
    flattenPExp pexp
flattenExp (CondExp cond thn els) ty castFrom pos = do
    resultName <- tempVar
    flattenStmt (Cond cond
                 [maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content thn) ty castFrom (place thn),
                               Unplaced $ Var resultName ParamOut Ordinary])
                  pos]
                 [maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content els) ty castFrom (place els),
                               Unplaced $ Var resultName ParamOut Ordinary])
                  pos]
                Nothing Nothing)
        pos Det
    return $ maybePlace (Var resultName ParamIn Ordinary) pos
flattenExp expr@(AnonProc mods _ pstmts) ty castFrom pos = do
    state <- get
    let anonState = anonProcState state
    modify (\s -> s{flattened=[], postponed=[], 
                    anonProcState=pushAnonProcState anonState})
    flattenStmts pstmts $ modifierDetism mods
    flushPostponed
    state' <- get
    let anonState' = anonProcState state'
    put state{anonProcState=popAnonProcState anonState anonState', 
              tempCtr=tempCtr state'}
    let anonParams = processAnonProcParams anonState'
    return $ typeAndPlace (AnonProc mods anonParams (reverse $ flattened state')) 
                          ty castFrom pos
flattenExp (CaseExp pexpr cases deflt) ty castFrom pos = do
    resultName <- tempVar
    pexpr' <- flattenPExp pexpr
    flattenStmt (translateExpCases pexpr' resultName cases deflt) pos Det
    return $ maybePlace (Var resultName ParamIn Ordinary) pos
flattenExp (Fncall mod name exps) ty castFrom pos = do
    let stmtBuilder = ProcCall (First mod name Nothing) Det False
    flattenCall stmtBuilder False ty castFrom pos exps
flattenExp (ForeignFn lang name flags exps) ty castFrom pos = do
    flattenCall (ForeignCall lang name flags) True ty castFrom pos exps
flattenExp (Typed exp AnyType _) ty castFrom pos = do
    flattenExp exp ty castFrom pos
flattenExp (Typed exp ty castFrom) _ _ pos = do
    flattenExp exp ty castFrom pos


-- |Flatten a Wybe or foreign *function* call, returning a simple expression for
-- the value (ie, a variable).  Emits a proc call to compute the value.
flattenCall :: ([Placed Exp] -> Stmt) -> Bool -> TypeSpec -> Maybe TypeSpec
            -> OptPos -> [Placed Exp] -> Flattener (Placed Exp)
flattenCall stmtBuilder isForeign ty castFrom pos exps = do
    logFlatten $ "-- flattening args:  " ++ show exps
    resultName <- tempVar
    oldPos <- gets currPos
    defs <- gets stmtDefs
    modify (\s -> s { stmtDefs = Set.empty, currPos = pos})
    exps' <- flattenArgs exps
    defs' <- gets stmtDefs
    modify (\s -> s { stmtDefs = defs `Set.union` defs',
                      currPos = oldPos})
    logFlatten $ "-- defines:  " ++ show defs'
    let outFlows = Set.fromList
                        $ List.filter (/= ParamIn)
                        $ List.map (flattenedExpFlow . content) exps'
    logFlatten $ "-- set of out flows:  " ++ show outFlows
    varflow <- if Set.null outFlows
                then return ParamIn
                else if outFlows == Set.singleton ParamOut
                then return ParamOut
                else if outFlows == Set.singleton ParamInOut
                then return ParamInOut
                else lift $ do
                    errmsg pos "Expression mixes out and in/out arguments: "
                    return ParamOut
    when (flowsIn varflow)
        $ emit pos $ stmtBuilder
        $ ((inputOnlyExp <$>) <$> exps')
          ++ [typeAndPlace (Var resultName ParamOut Ordinary) ty castFrom pos]
    when (flowsOut varflow)
        $ postpone pos $ stmtBuilder
        $ exps' ++ [typeAndPlace (Var resultName ParamIn Ordinary) ty castFrom pos]
    return $ Unplaced $ maybeType (Var resultName varflow Ordinary) ty castFrom

flattenAnonParam :: Exp -> TypeSpec -> Maybe TypeSpec -> OptPos
            -> Flattener (Placed Exp)
flattenAnonParam expr@(AnonParamVar mbNum dir) ty castFrom pos = do
    logFlatten $ "  Flattening anon param " ++ show expr
    anonState <- gets anonProcState
    let AnonProcState _ currentAnon count params = anonState
    (num, count') <- case (mbNum, count) of
        (Nothing, Just n) -> 
            let n' = n + 1
            in return (n', Just n')
        (Just n, _) | fromMaybe 0 count == 0 -> do
            return (n, Nothing)
        _ -> do 
            lift $ message Error 
                    "Mixed use of numbered and un-numbered anonymous parameters" pos
            return (-1, count)
    let name = makeAnonParamName currentAnon num
    let var = Var name dir Ordinary 
    let paramDir = paramFlow <$> Map.lookup num params
    let paramDir' = if fromMaybe dir paramDir == dir 
                    then dir 
                    else ParamInOut
    let param = makeAnonParam name paramDir'
    modify (\s -> s{anonProcState=anonState{paramCount=count',
                                            params=Map.insert num param params}})
    if currentAnon == 0
    then do
        lift $ message Error
               ("Anonymous parameter @" ++ maybe "" show mbNum 
                ++ " outside of anonymous procedure expression")
               pos
        flattenExp var ty castFrom pos
    else do
        noteVarIntro name
        expr' <- flattenExp var ty castFrom pos
        logFlatten $ "  Anon param flattened " ++ show var ++ " -> " ++ show expr'
        return expr'
flattenAnonParam expr _ _ pos = return $ maybePlace expr pos


-- | Translate a case expression into a conditional expression, for subsequent
-- flattening.  First argument is a variable expression holding the value being
-- switched on, second is the variable in which to store the value of the
-- conditional expr, third are all the cases, and last is the Maybe default
-- value.
translateExpCases :: Placed Exp -> String -> [(Placed Exp, Placed Exp)]
                  -> Maybe (Placed Exp) -> Stmt
translateExpCases pexp varName [] Nothing = Fail
translateExpCases pexp varName [] (Just deflt) =
    ForeignCall "llvm" "move" [] [deflt, Unplaced $ varSet varName]
translateExpCases pexp varName ((pat,val):rest) deflt =
    Cond (maybePlace (ProcCall (First [] "=" Nothing) SemiDet False [pat,pexp])
                     (place pat))
        [Unplaced $ ForeignCall "llvm" "move" []
                    [val, Unplaced $ varSet varName]]
        [Unplaced (translateExpCases pexp varName rest deflt)] Nothing Nothing


-- | Attach a type, source position, and possibly a type to cast from, to a
-- given expression.
typeAndPlace :: Exp -> TypeSpec -> Maybe TypeSpec -> OptPos -> Placed Exp
typeAndPlace exp ty castFrom = maybePlace (maybeType exp ty castFrom)


maybeType :: Exp -> TypeSpec -> Maybe TypeSpec -> Exp
maybeType exp AnyType Nothing = exp
maybeType exp ty castFrom = Typed exp ty castFrom


isInExp :: Exp -> Bool
isInExp (Var _ dir _) = flowsIn dir
isInExp _ = True


-- | Return the input-only version of an Exp that is known to be either in or
-- in-out.
inputOnlyExp :: Exp -> Exp
inputOnlyExp (Var name ParamInOut flowType) = Var name ParamIn flowType
inputOnlyExp (Var name ParamOut flowType) =
    shouldnt $ "Making input-only version of output variable " ++ name
inputOnlyExp exp = exp


-- |Log a message, if we are logging flattening activity.
logFlatten :: String -> Flattener ()
logFlatten s = lift $ logMsg Flatten s
