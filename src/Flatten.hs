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

module Flatten (flattenProcBody) where

import AST
import Config
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


----------------------------------------------------------------
--                        Exported Functions
----------------------------------------------------------------

-- | Flatten the body of a proc def
flattenProcBody :: ProcDef -> Int -> Compiler ProcDef
flattenProcBody pd _ = do
    let proto = procProto pd
        params = procProtoParams proto
        inParams = Set.fromList
                 $ List.map paramName
                 $ List.filter (flowsIn . paramFlow)
                 $ content <$> params
        resources = Set.map (resourceName . resourceFlowRes)
                  $ procProtoResources proto
        ProcDefSrc body = procImpln pd

        detism = procDetism pd
        inlining = procInlining pd
        impurity = procImpurity pd
        variant = procVariant pd
        resourceful = not $ Set.null resources
        mods = ProcModifiers detism inlining impurity variant resourceful

    logMsg Flatten
        $ "** Flattening def " ++ showProcModifiers' mods ++ show proto
            ++ " {" ++ showBody 4 body ++ "}"
    mapM_ (placedApply $ flip explicitTypeSpecificationWarning . paramType) params
    
    (body',tmpCtr) <- flattenBody body (inParams `Set.union` resources) detism

    return pd{procTmpCount = tmpCtr, procImpln = ProcDefSrc body'}

-- |Flatten the specified statement sequence given a set of input parameter
-- and resource names.
flattenBody :: [Placed Stmt] -> Set VarName -> Determinism
            -> Compiler ([Placed Stmt],Int)
flattenBody stmts varSet detism = do
    logMsg Flatten $ "Flattening body" ++ showBody 4 stmts
    logMsg Flatten $ "Flattening with parameters = " ++ show varSet
    let varSet' = foldStmts (const . const) insertOutVar varSet stmts
    logMsg Flatten $ "Flattening with all vars = " ++ show varSet'
    finalState <- execStateT (flattenStmts stmts detism)
                  $ initFlattenerState varSet'
    return (List.reverse (flattened finalState), tempCtr finalState)


-- | Insert the expression var name if it's an output variable; otherwise leave
-- the variable set alone.
insertOutVar :: Set VarName -> Exp -> OptPos -> Set VarName
insertOutVar varSet (Var name ParamOut _) _ = Set.insert name varSet
insertOutVar varSet (Typed exp _ _) pos = insertOutVar varSet exp pos
insertOutVar varSet expr _ = varSet


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
    params :: Map Integer Param  -- ^Unprocessed params
    } deriving Show


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
makeAnonParamName procNum num = specialName2 "anon"
                              $ specialName2 (show procNum) (show num)


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
    let name = mkTempName ctr
    noteVarIntro name
    return name
    

-- |Run a flattener, ignoring its state changes except for the temp variable
--  counter.  If transparent is True, also keep changes to the set of defined
--  variables.
flattenInner :: Bool -> Determinism -> Flattener t -> Flattener [Placed Stmt]
flattenInner transparent detism inner = do
    oldState <- get
    (_,innerState) <-
        lift (runStateT inner
              (initFlattenerState (defdVars oldState)) {
                    tempCtr = tempCtr oldState,
                    anonProcState = anonProcState oldState})
    let stmts = List.reverse $ flattened innerState
    logFlatten $ "-- Flattened:" ++ showBody 4 stmts
    -- logFlatten $ "-- Postponed:\n" ++
    --   showBody 4 (postponed innerState)
    if transparent
      then put $ oldState { tempCtr = tempCtr innerState,
                            defdVars = defdVars innerState,
                            anonProcState = anonProcState innerState }
      else put $ oldState { tempCtr = tempCtr innerState,
                            anonProcState = anonProcState innerState }
    return stmts
    

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
flattenStmt' stmt@(ProcCall fn@(First [] "=" id) callDetism res [arg1,arg2]) pos detism = do
    let arg1content = innerExp $ content arg1
    let arg2content = innerExp $ content arg2
    let arg1outs = Set.null $ expOutputs arg1content
    let arg2outs = Set.null $ expOutputs arg2content
    logFlatten $ "Flattening assignment with arg1 outputs? " ++ show arg1outs
                 ++ " and arg2 outputs? " ++ show arg2outs
    case (arg1content, arg2content) of
      (Fncall mod name bang args, _)
        | not arg1outs && arg2outs -> do
        let stmt' = ProcCall (First mod name Nothing) Det bang (args++[arg2])
        flattenStmt stmt' pos detism
      (_, Fncall mod name bang args)
        | not arg2outs && arg1outs -> do
        (arg1':args') <- flattenStmtArgs (arg1:args) pos
        emit pos $ ProcCall (First mod name Nothing) Det bang (args'++[arg1'])
        flushPostponed
      (_,_) | callDetism == Det
                && (varCheck arg1content arg2outs || varCheck arg2content arg1outs)
                || arg1outs && arg2outs -> do
        logFlatten $ "Leaving = call alone: " ++ showStmt 4 stmt
        args' <- flattenStmtArgs [arg1,arg2] pos
        emit pos $ ProcCall fn callDetism res args'
        flushPostponed
      _ -> do
        -- Must be a mode error:  both sides want to bind variables
        logFlatten $ "Error: out=out assignment " ++ show stmt
        lift $ message Error "Cannot generate bindings on both sides of '='" pos
  where varCheck argContent hasOuts
            = expIsVar argContent && flowsOut (flattenedExpFlow argContent)
                                  && hasOuts
flattenStmt' stmt@(ProcCall (First [] "fail" _) _ _ []) pos _ =
    emit pos Fail
flattenStmt' stmt@(ProcCall (First [] "break" _) _ _ []) pos _ =
    emit pos Break
flattenStmt' stmt@(ProcCall (First [] "next" _) _ _ []) pos _ =
    emit pos Next
flattenStmt' stmt@(ProcCall func detism res args) pos d = do
    logFlatten $ " Flattening call " ++ show stmt
    args' <- flattenStmtArgs args pos
    emit pos $ ProcCall func detism res args'
    flushPostponed
flattenStmt' (ForeignCall lang name flags args) pos _ = do
    args' <- flattenStmtArgs args pos
    emit pos $ ForeignCall lang name flags args'
    flushPostponed
-- XXX must handle Flattener state more carefully.  Defined variables need
--     to be retained between condition and then branch, but forgotten for
--     the else branch.
flattenStmt' (Cond tstStmt thn els condVars defVars res) pos detism = do
    tstStmt' <- seqToStmt <$> flattenInner True SemiDet
                (placedApply flattenStmt tstStmt SemiDet)
    thn' <- flattenInner False detism (flattenStmts thn detism)
    els' <- flattenInner False detism (flattenStmts els detism)
    emit pos $ Cond tstStmt' thn' els' condVars defVars res
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
flattenStmt' (And tsts) pos detism = do
    tsts' <- flattenInner True detism (flattenStmts tsts SemiDet)
    emit pos $ And tsts'
flattenStmt' (Or tsts vars res) pos detism = do
    tsts' <- flattenDisj detism tsts
    emit pos $ Or tsts' vars res
flattenStmt' (Not tstStmt) pos SemiDet = do
    tstStmt' <- seqToStmt <$> flattenInner True SemiDet
                (placedApply flattenStmt tstStmt SemiDet)
    emit pos $ Not tstStmt'
flattenStmt' (Not tstStmt) _pos detism =
    shouldnt $ "negation in a " ++ show detism ++ " context"
flattenStmt' (Loop body defVars res) pos detism = do
    body' <- flattenInner False detism (flattenStmts body detism)
    emit pos $ Loop body' defVars res
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
                    [Unplaced $ Cond (ProcCall (regularProc "[|]") SemiDet False
                                        [var,
                                         Unplaced $ Var gen ParamOut Ordinary,
                                         Unplaced $ Var gen ParamIn Ordinary]
                                      `maybePlace` pos')
                                loop [Unplaced Break]
                      Nothing Nothing Nothing]
                ) body $ zip3 (loopVar <$> gens) temps poss
    let generated = Loop loop Nothing Nothing
    logFlatten $ "Generated for: " ++ showStmt 4 generated
    flattenStmt' generated pos detism
flattenStmt' (UseResources res vars body) pos detism = do
    oldVars <- gets defdVars
    mapM_ (noteVarIntro . resourceName) res
    body' <- flattenInner True detism (flattenStmts body detism)
    modify $ \s -> s { defdVars = oldVars}
    emit pos $ UseResources res vars body'
flattenStmt' Nop pos _ = emit pos Nop
flattenStmt' Fail pos _ = emit pos Fail
flattenStmt' Break pos _ = emit pos Break
flattenStmt' Next pos _ = emit pos Next


-- | Flatten a disjunction of statements.  Unbranching will turn disjunctions
-- into conditionals, but here we just flatten each of the disjuncts.
flattenDisj :: Determinism -> [Placed Stmt] -> Flattener [Placed Stmt]
flattenDisj _ [] = return []
flattenDisj detism (disj:disjs) = do
    disj' <- seqToStmt <$> flattenInner True detism (placedApply flattenStmt disj detism)
    disjs' <- flattenDisj detism disjs
    return $ disj' : disjs'


-- | Flatten an assignment of the specified expression (`value`) to the
-- specified variable, which is specified both as a name and as an output
-- expression.
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
     (Cond (maybePlace (ProcCall (regularProc "=") SemiDet False [key,val])
                       (place key))
           body
           (translateCases val pos rest deflt)
           Nothing Nothing Nothing)
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
flattenExp expr@(Var "_" flow _) ty castFrom pos = do
    when (flow == ParamInOut)
        $ lift $ errmsg pos $ "A \"don't care\" value (_) cannot be used with "
                              ++ flowPrefix flow ++ " mode prefix"
    dummyName <- tempVar
    return $ typeAndPlace (Var dummyName ParamOut Ordinary) ty castFrom pos
flattenExp expr@(Var name dir flowType) ty castFrom pos = do
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
flattenExp expr@(AnonParamVar mbNum dir) ty castFrom pos = do
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
            lift $ errmsg pos 
                 $ "Mixed use of numbered and un-numbered anonymous parameters"
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
                ++ " outside of anonymous procedure/function expression")
               pos
        flattenExp var ty castFrom pos
    else do
        noteVarIntro name
        expr' <- flattenExp var ty castFrom pos
        logFlatten $ "  Anon param flattened " ++ show var ++ " -> " ++ show expr'
        return expr'
flattenExp expr@(Closure ms es) ty castFrom pos = do
    es' <- mapM flattenPExp es
    return $ typeAndPlace (Closure ms es') ty castFrom pos
flattenExp global@(Global _) _ _ pos = return $ maybePlace global pos
flattenExp (Where stmts pexp) _ _ _ = do
    flattenStmts stmts Det
    flattenPExp pexp
flattenExp (DisjExp thn els) ty castFrom pos = do
    resultName <- tempVar
    flattenStmt (Or
                 [maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content thn) ty castFrom (place thn),
                               Unplaced $ Var resultName ParamOut Ordinary])
                  pos,
                  maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content els) ty castFrom (place els),
                               Unplaced $ Var resultName ParamOut Ordinary])
                  pos]
                Nothing Nothing)
        pos Det
    return $ maybePlace (Var resultName ParamIn Ordinary) pos
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
                Nothing Nothing Nothing)
        pos Det
    return $ maybePlace (Var resultName ParamIn Ordinary) pos
flattenExp (AnonProc mods _ pstmts clsd res) ty castFrom pos =
    let detism = modifierDetism mods
    in flattenAnon mods clsd res ty castFrom pos $ flattenStmts pstmts detism
flattenExp (AnonFunc exp) ty castFrom pos = 
    flattenAnon defaultProcModifiers Nothing Nothing ty castFrom pos
    $ do
        logFlatten $ "Flattening AnonFunc expression: " ++ show exp 
        let outs = expOutputs $ content exp
        unless (Set.null outs)
            $ lift $ errmsg pos 
            $ "Anonymous function cannot contain output variables: " 
            ++ intercalate ", " (Set.toList outs)
        exp' <- flattenPExp exp
        AnonProcState _ _ paramCount params <- gets anonProcState
        let outNum = case paramCount of
                Nothing -> Just $ (+1) . maximum $ (-1) : Map.keys params
                Just _ -> Nothing
        logFlatten $ "Flattened AnonFunc has output num: " ++ show outNum
        out <- flattenPExp (AnonParamVar outNum ParamOut `maybePlace` pos)
        logFlatten $ "Flattened AnonFunc has output var: " ++ show out 
        emit pos $ ForeignCall "llvm" "move" [] [exp', out]
        flushPostponed
flattenExp (CaseExp pexpr cases deflt) ty castFrom pos = do
    resultName <- tempVar
    pexpr' <- flattenPExp pexpr
    flattenStmt (translateExpCases pexpr' resultName cases deflt) pos Det
    return $ maybePlace (Var resultName ParamIn Ordinary) pos
flattenExp (Fncall mod name bang exps) ty castFrom pos = do
    when bang $ lift
        $ errmsg pos "function call cannot have preceding !"
    let stmtBuilder = ProcCall (First mod name Nothing) Det bang
    flattenCall stmtBuilder False ty castFrom pos exps
flattenExp (ForeignFn lang name flags exps) ty castFrom pos = do
    flattenCall (ForeignCall lang name flags) True ty castFrom pos exps
flattenExp (Typed exp AnyType _) ty castFrom pos = do
    flattenExp exp ty castFrom pos
flattenExp (Typed exp ty castFrom) _ _ pos = do
    lift $ explicitTypeSpecificationWarning pos ty
    lift $ forM_ castFrom (explicitTypeSpecificationWarning pos)
    flattenExp exp ty castFrom pos

    
-- | Flatten something, and produce an anonymous procedure from the resultant flattened
-- statements
flattenAnon :: ProcModifiers -> (Maybe VarDict) -> (Maybe (Set ResourceFlowSpec)) 
            -> TypeSpec -> Maybe TypeSpec -> OptPos
            -> Flattener () -> Flattener (Placed Exp)
flattenAnon mods clsd res ty castFrom pos inner = do
    anonState <- gets anonProcState
    let newAnonState = pushAnonProcState anonState
    logFlatten $ "Flattening new anon proc with state " ++ show newAnonState
    modify $ \s -> s{anonProcState=newAnonState}
    let detism = modifierDetism mods
    body <- flattenInner True detism inner
    anonState' <- gets anonProcState
    modify $ \s -> s{anonProcState=popAnonProcState anonState anonState'}
    let anonParams = processAnonProcParams anonState'
    return $ typeAndPlace (AnonProc mods anonParams body clsd res) ty castFrom pos


-- | Emit a warning if a type constraint is the current module.
explicitTypeSpecificationWarning :: OptPos -> TypeSpec -> Compiler ()
explicitTypeSpecificationWarning pos ty@(TypeSpec tmod tname params) = do
    currMod <- getModuleSpec
    isType <- moduleIsType currMod
    when (((tmod ++ [tname]) `isSuffixOf` currMod) && isType) $ do
        logMsg Flatten "here<<<"
        message Warning
            ("Explicit specification of current type " ++ show ty
            ++ ",\n  it is recommended to specify type as " ++ currentModuleAlias)
            pos
    mapM_ (explicitTypeSpecificationWarning pos) params
explicitTypeSpecificationWarning pos ty@(HigherOrderType _ tyflows) = do
    mapM_ (explicitTypeSpecificationWarning pos . typeFlowType) tyflows
explicitTypeSpecificationWarning _ _ = return ()



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
    Cond (maybePlace (ProcCall (regularProc "=") SemiDet False [pat,pexp])
                     (place pat))
        [Unplaced $ ForeignCall "llvm" "move" []
                    [val, Unplaced $ varSet varName]]
        [Unplaced (translateExpCases pexp varName rest deflt)]
        Nothing Nothing Nothing


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
