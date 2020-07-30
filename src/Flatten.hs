--  File     : Flatten.hs
--  Author   : Peter Schachte
--  Purpose  : Flatten function calls (expressions) into procedure calls
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
--  We transform away all expression types except for constants and
--  variables.  Where, let, conditional, and function call
--  expressions are turned into statements that bind a variable, and
--  then the variable is used in place of the expression.  In-out
--  variable uses, like !x, are expanded into separate input and
--  output expressions, like x, ?x.
--
--  An expression that assigns one or more variables is an output
--  expression.  This is turned into an output variable, with
--  following statements generated to do the assignment.  An
--  expression that assigns variables that it also uses is an
--  input-output expression, which is turned into statements to bind a
--  variable placed before the variable use plus statements to use the
--  variable placed after the variable use.  For example, we transform
--  statements of the form p(f(x)) into f(x,?t) p(t).  Similarly, we
--  transform statements like p(f(?x)) into p(?t) f(?x, t).  Finally,
--  we transform p(f(!x)) into f(x, ?t) p(t, ?t) f(?x, t).
--
----------------------------------------------------------------

module Flatten (flattenProcDecl) where

import AST
import Snippets
import Options (LogSelection(Flatten))
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Set as Set
import Data.Maybe
import Text.ParserCombinators.Parsec.Pos
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans (lift,liftIO)


----------------------------------------------------------------
--                        Exported Functions
----------------------------------------------------------------

flattenProcDecl :: Item -> Compiler (Item,Int)
flattenProcDecl (ProcDecl vis detism inline 
                 proto@ProcProto{procProtoParams=params}
                 stmts pos) = do
    logMsg Flatten $ "** Flattening "
           ++ (if inline then "inline " else "")
           ++ show detism ++ " proc "
           ++ show proto ++ ":" ++ showBody 4 stmts
    let proto' = proto {procProtoParams = concatMap flattenParam params}
              -- flattenProto proto detism
    let inParams = Set.fromList $
                   List.map paramName $
                   List.filter (flowsIn . paramFlow) $
                   procProtoParams proto'
    let inResources = Set.map (resourceName . resourceFlowRes) $
                   Set.filter (flowsIn . resourceFlowFlow) $
                   procProtoResources proto'
    (stmts',tmpCtr) <- flattenBody stmts (inParams `Set.union` inResources)
                       detism
    return (ProcDecl vis detism inline proto' stmts' pos,tmpCtr)
flattenProcDecl _ =
    shouldnt "flattening a non-proc item"


flattenBody :: [Placed Stmt] -> Set VarName -> Determinism
            -> Compiler ([Placed Stmt],Int)
flattenBody stmts varSet detism = do
    finalState <- execStateT (flattenStmts stmts detism)
                  $ initFlattenerState varSet
    return (List.reverse (prefixStmts finalState) ++ 
            List.reverse (flattened finalState),
            -- ++ postponed finalState,
            tempCtr finalState)


-- |The Flattener monad is a state transformer monad carrying the 
--  flattener state over the compiler monad.
type Flattener = StateT FlattenerState Compiler


----------------------------------------------------------------
--                       The Flattener Monad
----------------------------------------------------------------

data FlattenerState = Flattener {
    prefixStmts :: [Placed Stmt],   -- ^Code to be generated earlier, reversed
                                    -- (used for loop initialisation)
    flattened   :: [Placed Stmt],   -- ^Flattened code generated, reversed
    -- postponed   :: [Placed Stmt],   -- ^Code to be generated later
    tempCtr     :: Int,             -- ^Temp variable counter
    currPos     :: OptPos,          -- ^Position of current statement
    stmtDefs    :: Set VarName,     -- ^Variables defined by this statement
    defdVars    :: Set VarName      -- ^Variables defined before this stmt,
                                    --  needed to distinguish niladic fns
                                    --  from variables
    }


initFlattenerState :: Set VarName -> FlattenerState
initFlattenerState varSet = 
    Flattener [] [] 0 Nothing Set.empty varSet


emit :: OptPos -> Stmt -> Flattener ()
emit pos stmt = do
    logFlatten $ "-- Emitting:  " ++ showStmt 14 stmt
    stmts <- gets flattened
    modify (\s -> s { flattened = maybePlace stmt pos:stmts })


-- | Add an initialisation statement to the list of initialisations
--   XXX This will be needed for for loops, but is not used yet
saveInit :: OptPos -> Stmt -> Flattener ()
saveInit pos stmt = do
    stmts <- gets prefixStmts
    modify (\s -> s { prefixStmts = maybePlace stmt pos:stmts })


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
                    tempCtr = tempCtr oldState,
                    prefixStmts = if isLoop then [] else prefixStmts oldState})
    logFlatten $ "-- Prefix:\n" ++ showBody 4 (prefixStmts innerState)
    logFlatten $ "-- Flattened:" ++ showBody 4 (List.reverse
                                                $ flattened innerState)
    -- logFlatten $ "-- Postponed:\n" ++ 
    --   showBody 4 (postponed innerState)
    if transparent
      then put $ oldState { tempCtr = tempCtr innerState,
                            defdVars = defdVars innerState }
      else put $ oldState { tempCtr = tempCtr innerState }
    if isLoop
      then flattenStmts (prefixStmts innerState) detism
      else modify (\s -> s { prefixStmts = prefixStmts innerState })
    return $ List.reverse $ flattened innerState


flattenStmtArgs :: [Placed Exp] -> OptPos -> Flattener [Placed Exp]
flattenStmtArgs args pos = do
    modify (\s -> s { stmtDefs = Set.empty, currPos = pos})
    flattenArgs args


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


noteVarMention :: VarName -> FlowDirection -> Flattener ()
noteVarMention name dir = do
    when (flowsOut dir) $ noteVarDef name

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
    modify (\s -> s { defdVars = defdVars s `Set.union` stmtDefs s })

-- |Flatten the specified statement
flattenStmt' :: Stmt -> OptPos -> Determinism -> Flattener ()
-- XXX This doesn't seem to apply
-- flattenStmt' stmt@(ProcCall [] "phantom" _ Det _ [arg]) pos _ = do
--     -- Convert unary call to phantom with output var to move instr
--     let instr = ForeignCall "llvm" "move" []
--                 [Unplaced $ Typed (IntValue 0) (TypeSpec [] "phantom" []) True,
--                  arg]
--     logFlatten $ "   Converting ProcCall " ++ show stmt ++ " to " ++ show instr
--     emit pos instr
flattenStmt' stmt@(ProcCall [] "=" id Det res [arg1,arg2]) pos detism = do
    let arg1content = content arg1
    let arg2content = content arg2
    let arg1Vars = expOutputs arg1content
    let arg2Vars = expOutputs arg2content
    case (content arg1, content arg2) of
      (Var var ParamOut Ordinary, _) | Set.null arg2Vars -> do
        logFlatten $ "Transforming assignment " ++ showStmt 4 stmt
        [arg2'] <- flattenStmtArgs [arg2] pos
        let instr = ForeignCall "llvm" "move" [] [arg2', arg1]
        logFlatten $ "  transformed to " ++ showStmt 4 instr
        noteVarDef var
        emit pos instr
      (_, Var var ParamOut Ordinary) | Set.null arg1Vars -> do
        logFlatten $ "Transforming assignment " ++ showStmt 4 stmt
        [arg1'] <- flattenStmtArgs [arg1] pos
        let instr = ForeignCall "llvm" "move" [] [arg1', arg2]
        logFlatten $ "  transformed to " ++ showStmt 4 instr
        noteVarDef var
        emit pos instr
      (Fncall mod name args, _)
        | not (Set.null arg1Vars) && Set.null arg2Vars -> do
        let stmt' = ProcCall mod name Nothing Det False (args++[arg2])
        flattenStmt' stmt' pos detism
      (_, Fncall mod name args)
        | not (Set.null arg2Vars) && Set.null arg1Vars -> do
        let stmt' = ProcCall mod name Nothing Det False (args++[arg1])
        flattenStmt' stmt' pos detism
      (_,_) | Set.null arg1Vars && Set.null arg2Vars -> do
        logFlatten $ "Leaving equality test alone: " ++ showStmt 4 stmt
        args' <- flattenStmtArgs [arg1,arg2] pos
        emit pos $ ProcCall [] "=" id Det res args'
      _ -> do
        -- Must be a mode error:  both sides want to bind variables
        lift $ message Error "Cannot generate bindings on both sides of '='" pos
flattenStmt' stmt@(ProcCall [] name _ _ _ []) pos _ = do
    defined <- gets defdVars
    -- Convert call to no-arg proc to a bool variable test if there's a
    -- local variable with that name
    if name `elem` defined
        then emit pos $ TestBool $ Var name ParamIn Ordinary
        else emit pos stmt
flattenStmt' (ProcCall maybeMod name procID detism res args) pos _ = do
    logFlatten "   call is Det"
    args' <- flattenStmtArgs args pos
    emit pos $ ProcCall maybeMod name procID detism res args'
flattenStmt' (ForeignCall "llvm" "test" flags args) pos SemiDet = do
    args' <- flattenStmtArgs args pos
    resultName <- tempVar
    let vSet = Unplaced
               $ Typed (Var resultName ParamOut $ Implicit pos) boolType False
    emit pos $ ForeignCall "llvm" "icmp" flags $ args' ++ [vSet]
    emit pos $ TestBool $ varGet resultName
flattenStmt' stmt@(ForeignCall "llvm" "test" _ _) _ Det =
    shouldnt $ "llvm test in Det context: " ++ show stmt
flattenStmt' (ForeignCall lang name flags args) pos _ = do
    args' <- flattenStmtArgs args pos
    emit pos $ ForeignCall lang name flags args'
-- XXX must handle Flattener state more carefully.  Defined variables need
--     to be retained between condition and then branch, but forgotten for
--     the else branch.  Also note that 'transparent' arg to flattenInner is
--     always False
flattenStmt' (Cond tstStmt thn els) pos detism = do
    defined <- gets defdVars
    -- expand tstStmts, allowing defined vars to propagate to then branch
    tstStmt' <- seqToStmt <$> flattenInner False True SemiDet
                (placedApply flattenStmt tstStmt SemiDet)
    thn' <- flattenInner False False detism (flattenStmts thn detism)
    -- for else branch, put defined vars back as they were before condition 
    modify (\s -> s {defdVars = defined})
    els' <- flattenInner False False detism (flattenStmts els detism)
    emit pos $ Cond tstStmt' thn' els'
flattenStmt' stmt@(TestBool _) pos SemiDet = emit pos stmt
flattenStmt' (TestBool expr) _pos Det =
    shouldnt $ "TestBool " ++ show expr ++ " in Det context"
flattenStmt' (And tsts) pos SemiDet = do
    tsts' <- flattenInner False True SemiDet (flattenStmts tsts SemiDet)
    emit pos $ And tsts'
flattenStmt' stmt@And{} _pos Det =
    shouldnt $ "And in a Det context: " ++ showStmt 4 stmt
flattenStmt' (Or tsts) pos SemiDet = do
    tsts' <- flattenInner False True SemiDet (flattenStmts tsts SemiDet)
    emit pos $ Or tsts'
flattenStmt' (Or tstStmts) _pos Det =
    shouldnt $ "Or in a Det context: " ++ showBody 4 tstStmts
flattenStmt' (Not tstStmt) pos SemiDet = do
    tstStmt' <- seqToStmt <$> flattenInner False True SemiDet
                (placedApply flattenStmt tstStmt SemiDet)
    emit pos $ Not tstStmt'
flattenStmt' (Not tstStmt) _pos Det =
    shouldnt $ "negation in a Det context: " ++ show tstStmt
flattenStmt' (Loop body) pos detism = do
    body' <- flattenInner True False detism
             (flattenStmts (body ++ [Unplaced Next]) detism)
    emit pos $ Loop body'
-- flattenStmt' (For loopVar genExp body) pos detism = do
--     tempGen <- tempVar
--     [genExp'] <- flattenPExp genExp -- XXX Should check for input only
--     let instr = ForeignCall "llvm" "move" []
--                 [genExp', Unplaced $ Var tempGen ParamOut Ordinary]
--     emit pos instr
--     let test = ProcCall [] "[|]" Nothing SemiDet False
--                [Unplaced $ Var (content loopVar) ParamOut Ordinary
--                , Unplaced $ Var tempGen ParamOut Ordinary
--                , Unplaced $ Var tempGen ParamIn Ordinary]
--     let terminalCond = Unplaced $
--                        Cond (Unplaced test) body [Unplaced Break]
--     flattenStmt' (Loop [terminalCond]) pos detism
flattenStmt' for@(For generators body) pos detism = do
    tempGens <- mapM (const tempVar) generators
    tempNextGens <- mapM (const tempVar) generators
    tempHasNextGen <- tempVar
    logFlatten $ "Generating for " ++ showStmt 4 for
    -- XXX Should check for input only
    generators' <- mapM ((head <$>) . flattenPExp . genExp) generators
    let instrs = zipWith (\g' g -> ForeignCall "llvm" "move" []
                [g', Unplaced $ varSet g]) generators' tempGens
    mapM_ (emit pos) instrs 
    modify (\s -> s {defdVars = Set.union (Set.fromList tempGens) $ defdVars s})
    let nextVals = concat $ zipWith3 (\generator tempNextGen tempGen ->
                [Unplaced $ ProcCall [] "[|]" Nothing Det False
                             [Unplaced $ Var (loopVar generator) ParamOut Ordinary
                             , Unplaced $ Var tempNextGen ParamOut Ordinary
                             , Unplaced $ Var tempGen ParamIn Ordinary
                             , Unplaced $ Var tempHasNextGen ParamOut Ordinary],
                Unplaced $ Cond (Unplaced $ TestBool $ varGet tempHasNextGen)
                    [Unplaced $ ForeignCall "llvm" "move" []
                    [Unplaced $ varGet tempNextGen, Unplaced $ varSet tempGen]]
                    [Unplaced Break]
                ]) generators tempNextGens tempGens
    -- body' <- flattenInner True False detism
    --          (flattenStmts (body ++ [Unplaced Next]) detism)
    let generated = Loop (nextVals ++ body)
    logFlatten $ "Generated for: " ++ showStmt 4 generated
    emit pos generated
    flattenStmt' generated pos detism
flattenStmt' (UseResources res body) pos detism = do
    defined <- gets defdVars
    body' <- flattenInner False True detism (flattenStmts body detism)
    defined' <- gets defdVars
    modify (\s -> s {defdVars = defined'
                      Set.\\ (Set.fromList $ resourceName <$> res)
                      `Set.union` defined })
    emit pos $ UseResources res body'
-- flattenStmt' (For itr gen) pos detism = do
--     vars <- flattenPExp gen
--     logFlatten $ "Flattening For " ++ show itr ++ " in " ++ show gen
--     logFlatten $ "  For vars = " ++ show vars
--     case vars of
--         [] -> lift $
--               message Error "'for' generator does not produce a value"
--               (place gen)
--         (_:_:_) -> lift $
--                    message Error "'for' generator has invalid flow" (place gen)
--         [genVar@(Unplaced (Var genVarName direction flowType))] -> do
--             -- XXX not generating the right code until we have polymorphism
--             flattenStmt
--               (Cond (maybePlace (ProcCall [] "[|]" Nothing SemiDet False
--                                  [itr,
--                                   Unplaced $
--                                   Var genVarName ParamOut flowType,
--                                   Unplaced $
--                                   Var genVarName ParamIn flowType])
--                      pos)
--                   []
--                   [maybePlace (ProcCall [] "[]" Nothing SemiDet False
--                                [Unplaced $ Var genVarName ParamIn flowType])
--                     pos,
--                    Unplaced Break]
--               ) pos detism
--         _ -> shouldnt "Generator expression producing unexpected vars"
flattenStmt' Nop pos detism = emit pos Nop
flattenStmt' Break pos detism = emit pos Break
flattenStmt' Next pos detism = emit pos Next


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
    logFlatten $ "  Flattened =   " ++ show (concat argListList)
    return $ concat argListList


flattenPExp :: Placed Exp -> Flattener [Placed Exp]
flattenPExp pexp = do
    vs <- gets defdVars
    logFlatten $ "  Flattening exp " ++ show pexp ++ ", with vars " ++
           show vs
    result <- flattenExp (content pexp) AnyType False (place pexp)
    logFlatten $ "  Result =   " ++ show result
    return result


-- |Flatten a single expressions with specified flow direction to
--  primitive argument(s), a list of statements to execute
--  to bind it, and a list of statements to execute 
--  after the call to store the result appropriately.
--  The first part of the output (a Placed Exp) will always be a list
--  of only atomic Exps and Var references (in any direction).
flattenExp :: Exp -> TypeSpec -> Bool -> OptPos -> Flattener [Placed Exp]
flattenExp expr@(IntValue _) ty cast pos =
    return [typeAndPlace expr ty cast pos]
flattenExp expr@(FloatValue _) ty cast pos =
    return [typeAndPlace expr ty cast pos]
flattenExp expr@(StringValue _) ty cast pos =
    return [typeAndPlace expr ty cast pos]
flattenExp expr@(CharValue _) ty cast pos =
    return [typeAndPlace expr ty cast pos]
flattenExp (Var "phantom" ParamIn _ ) _ _ pos =
    return [typeAndPlace (IntValue 0) (TypeSpec [] "phantom" []) True pos]
flattenExp expr@(Var name dir flowType) ty cast pos = do
    logFlatten $ "  Flattening arg " ++ show expr
    let isIn  = flowsIn dir
    let isOut = flowsOut dir
    logFlatten $ "  isIn = " ++ show isIn ++ " isOut = " ++ show isOut
    let flowType' = if isIn && isOut then HalfUpdate else flowType
    logFlatten $ "  flowType' = " ++ show flowType'
    defd <- gets (Set.member name . defdVars)
    if (dir == ParamIn && (not defd))
      then do -- Reference to an undefined variable: assume it's meant to be
              -- a niladic function instead of a variable reference
        logFlatten $ "  Unknown variable '" ++ show name
          ++ "' flattened to niladic function call"
        flattenCall (ProcCall [] name Nothing Det False) False ty cast pos []
      else do
        noteVarMention name dir
        let inPart = if isIn
                     then [typeAndPlace (Var name ParamIn flowType')
                           ty cast pos]
                     else []
        let outPart = if isOut
                      then [typeAndPlace (Var name ParamOut flowType')
                           ty cast pos]
                      else []
        logFlatten $ "  Arg flattened to " ++ show (inPart ++ outPart)
        return $ inPart ++ outPart
flattenExp (Where stmts pexp) _ _ _ = do
    flattenStmts stmts Det
    flattenPExp pexp
flattenExp (CondExp cond thn els) ty cast pos = do
    resultName <- tempVar
    let flowType = Implicit pos
    flattenStmt (Cond cond
                 [maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content thn) ty cast (place thn),
                               Unplaced $ Var resultName ParamOut flowType])
                  pos]
                 [maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content els) ty cast (place els),
                               Unplaced $ Var resultName ParamOut flowType])
                  pos])
        pos Det
    return $ [maybePlace (Var resultName ParamIn flowType) pos]
flattenExp (Fncall maybeMod name exps) ty cast pos = do
    flattenCall (ProcCall maybeMod name Nothing Det False) False ty cast pos
      exps
flattenExp (ForeignFn lang name flags exps) ty cast pos = do
    flattenCall (ForeignCall lang name flags) True ty cast pos exps
flattenExp (Typed exp AnyType _) ty cast pos = do
    flattenExp exp ty cast pos
flattenExp (Typed exp ty cast) _ _ pos = do
    flattenExp exp ty cast pos


flattenCall :: ([Placed Exp] -> Stmt) -> Bool -> TypeSpec -> Bool -> OptPos
            -> [Placed Exp] -> Flattener [Placed Exp]
flattenCall stmtBuilder isForeign ty cast pos exps = do
    logFlatten $ "-- flattening args:  " ++ show exps
    resultName <- tempVar
    oldPos <- gets currPos
    defs <- gets stmtDefs
    modify (\s -> s { stmtDefs = Set.empty, currPos = pos})
    exps' <- flattenArgs exps
    -- let exps'' = List.filter (isInExp . content) exps'
    defs' <- gets stmtDefs
    modify (\s -> s { stmtDefs = defs `Set.union` defs', 
                      currPos = oldPos})
    -- let isOut = not $ Set.null defs'
    logFlatten $ "-- defines:  " ++ show defs'
    -- logFlatten $ "-- in = " ++ show isIn ++ "; out = " ++ show isOut
    -- let flowType = if isIn && isOut then HalfUpdate else Implicit pos
    -- when isIn $ 
    --   emit pos $ stmtBuilder $ 
    --   exps'' ++ [typeAndPlace (Var resultName ParamOut flowType) ty cast pos]
    -- when isOut $ 
    --   postpone pos $ stmtBuilder $ 
    --   exps' ++ [typeAndPlace (Var resultName ParamIn flowType) ty cast pos]
    -- return $
    --   (if isIn
    --    then [Unplaced $ maybeType (Var resultName ParamIn flowType) ty cast]
    --    else []) ++
    --   (if isOut
    --    then [Unplaced $ maybeType (Var resultName ParamOut flowType) ty cast]
    --    else [])
    let (argflow,varflow) =
          if isForeign -- implicit arg of foreign function calls is always out
          then (ParamOut,ParamIn)
          else (FlowUnknown,FlowUnknown)
    emit pos $ stmtBuilder $ 
        exps' ++ [typeAndPlace (Var resultName argflow $ Implicit pos)
                  ty cast pos]
    return [Unplaced $ maybeType (Var resultName varflow $ Implicit pos)
            ty cast]

typeAndPlace :: Exp -> TypeSpec -> Bool -> OptPos -> Placed Exp
typeAndPlace exp ty cast pos = maybePlace (maybeType exp ty cast) pos

maybeType :: Exp -> TypeSpec -> Bool -> Exp
maybeType exp AnyType _ = exp
maybeType exp ty cast = Typed exp ty cast

isInExp :: Exp -> Bool
isInExp (Var _ dir _) = flowsIn dir
isInExp _ = True

flattenParam :: Param -> [Param]
flattenParam (Param name typ dir flowType) =
    let isIn  = flowsIn dir
        isOut = flowsOut dir
        flowType' = if isIn && isOut then HalfUpdate else flowType
    in  (if isIn then [Param name typ ParamIn flowType'] else []) ++
        (if isOut then [Param name typ ParamOut flowType'] else [])
    

-- |Log a message, if we are logging flattening activity.
logFlatten :: String -> Flattener ()
logFlatten s = lift $ logMsg Flatten s
