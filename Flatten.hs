--  File     : Flatten.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Flatten function calls (expressions) into procedure calls
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--
--  We transform away all expression types except for constants and
--  variables.  Where, let, and conditional, and function call
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
                 proto@(ProcProto name params resources) 
                 stmts pos) = do
    proto' <- flattenProto proto detism
    let inParams = Set.fromList $
                   List.map paramName $ 
                   List.filter (flowsIn . paramFlow) $
                   procProtoParams proto'
    (stmts',tmpCtr) <- flattenBody stmts inParams
    return (ProcDecl vis detism inline proto' stmts' pos,tmpCtr)
flattenProcDecl _ =
    shouldnt "flattening a non-proc or non-Det proc"


flattenProto :: ProcProto -> Determinism -> Compiler ProcProto
flattenProto (ProcProto name params resources) detism = do
    let params' = concatMap flattenParam params
    let params'' = case detism of
          Det     -> params'
          SemiDet -> params' ++ [Param "$$" boolType ParamOut
                                 $ Implicit Nothing]
    return $ ProcProto name params'' resources


flattenBody :: [Placed Stmt] -> Set VarName -> Compiler ([Placed Stmt],Int)
flattenBody stmts varSet = do
    finalState <- execStateT (flattenStmts stmts) $ initFlattenerState varSet
    return (List.reverse (prefixStmts finalState) ++ 
            List.reverse (flattened finalState) ++ 
            postponed finalState,
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
    postponed   :: [Placed Stmt],   -- ^Code to be generated later
    tempCtr     :: Int,             -- ^Temp variable counter
    currPos     :: OptPos,          -- ^Position of current statement
    stmtDefs    :: Set VarName,     -- ^Variables defined by this statement
    stmtUses    :: Set VarName,     -- ^Variables used by this statement
    defdVars    :: Set VarName      -- ^Variables defined before this stmt
    }


initFlattenerState :: Set VarName -> FlattenerState
initFlattenerState varSet = 
    Flattener [] [] [] 0 Nothing Set.empty Set.empty varSet


emit :: OptPos -> Stmt -> Flattener ()
emit pos stmt = do
    -- logFlatten $ "** Emitting:  " ++ showStmt 14 stmt
    stmts <- gets flattened
    modify (\s -> s { flattened = maybePlace stmt pos:stmts })


postpone :: OptPos -> Stmt -> Flattener ()
postpone pos stmt = do
    stmts <- gets postponed
    modify (\s -> s { postponed = maybePlace stmt pos:stmts })


-- | Add an initialisation statement to the list of initialisations
--   XXX This will be needed for for loops, but is not used yet
saveInit :: OptPos -> Stmt -> Flattener ()
saveInit pos stmt = do
    stmts <- gets prefixStmts
    modify (\s -> s { prefixStmts = maybePlace stmt pos:stmts })


emitPostponed :: Flattener ()
emitPostponed = do
    stmts <- gets flattened
    stmts' <- gets postponed
    modify (\s -> s { flattened = (List.reverse stmts') ++ stmts, 
                      postponed = [] })


-- |Return a fresh variable name.
tempVar :: Flattener VarName
tempVar = do
    ctr <- gets tempCtr
    modify (\s -> s { tempCtr = ctr + 1 })
    return $ mkTempName ctr


flattenInner :: Bool -> Bool -> Flattener t -> Flattener (t,[Placed Stmt])
flattenInner isLoop transparent inner = do
    oldState <- get
    (val,innerState) <-
        lift (runStateT inner
              ((initFlattenerState (defdVars oldState)) {
                    tempCtr = (tempCtr oldState),
                    prefixStmts = if isLoop then [] else prefixStmts oldState}))
    logFlatten $ "** Prefix:\n" ++ 
      showBody 4 (prefixStmts innerState)
    logFlatten $ "** Flattened:\n" ++ 
      showBody 4 (flattened innerState)
    logFlatten $ "** Postponed:\n" ++ 
      showBody 4 (postponed innerState)
    if transparent
       then put $ oldState { tempCtr = tempCtr innerState,
                             defdVars = defdVars innerState }
        else put $ oldState { tempCtr = tempCtr innerState }
    if isLoop
      then flattenStmts $ prefixStmts innerState
      else modify (\s -> s { prefixStmts = prefixStmts innerState })
    return (val,List.reverse $ flattened innerState)


flattenStmtArgs :: [Placed Exp] -> OptPos -> Flattener [Placed Exp]
flattenStmtArgs args pos = do
    modify (\s -> s { stmtUses = Set.empty, stmtDefs = Set.empty, currPos = pos})
    flattenArgs args


noteVarUse :: VarName -> Flattener ()
noteVarUse var =
    modify (\s -> s { stmtUses = Set.insert var $ stmtUses s })


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
    when (flowsIn dir) $ noteVarUse name
    when (flowsOut dir) $ noteVarDef name

----------------------------------------------------------------
--                      Flattening Statements
----------------------------------------------------------------

-- |Flatten the specified statements to primitive statements.
flattenStmts :: [Placed Stmt] -> Flattener ()
flattenStmts stmts = 
    mapM_ (\pstmt -> flattenStmt (content pstmt) (place pstmt)) stmts


flattenStmt :: Stmt -> OptPos -> Flattener ()
flattenStmt stmt pos = do
    modify (\s -> s { stmtUses = Set.empty,
                      stmtDefs = Set.empty,
                      currPos = pos})
    defd <- gets defdVars
    logFlatten $ "flattening stmt " ++ showStmt 4 stmt ++
      " with defined vars " ++ show defd
    flattenStmt' stmt pos
    modify (\s -> s { defdVars = defdVars s `Set.union` stmtDefs s })

-- |Flatten the specified statement
flattenStmt' :: Stmt -> OptPos -> Flattener ()
flattenStmt' (ProcCall maybeMod name procID args) pos = do
    args' <- flattenStmtArgs args pos
    emit pos $ ProcCall maybeMod name procID args'
    emitPostponed
flattenStmt' (ForeignCall lang name flags args) pos = do
    args' <- flattenStmtArgs args pos
    emit pos $ ForeignCall lang name flags args'
    emitPostponed
flattenStmt' tststmt@(Test stmts tst) pos = do
    logFlatten $ "** Flattening test:" ++ showStmt 4 tststmt
    (_,stmts') <- flattenInner False True (flattenStmts stmts)
    (vars,tst') <- flattenInner False False (do
      vars <- flattenPExp tst
      emitPostponed
      return vars)
    let errPos = betterPlace pos tst
    case vars of
      [] -> lift $ message Error "Test with no flow" errPos
      [var] -> do
        logFlatten $ "** Result:\n" ++ (showStmt 4 $ Test (stmts'++tst') var)
        emit pos $ Test (stmts'++tst') var
      [_,_] -> lift $ message Error
              ("Test with in-out flow: " ++ show vars) errPos
      _ -> shouldnt "Single expression expanded to more than 2 args"
flattenStmt' (Cond tstStmts tst thn els) pos = do
    logFlatten $ "** Flattening conditional:" ++ show tst
    (vars,tst') <- flattenInner False False (do
      vars <- flattenPExp tst
      emitPostponed
      return vars)
    logFlatten $ "** Result:\n" ++ showBody 4 tst'
    (_,thn') <- flattenInner False False (flattenStmts thn)
    (_,els') <- flattenInner False False (flattenStmts els)
    let errPos = betterPlace pos tst
    case vars of
      [] -> lift $ message Error "Condition with no flow" errPos
      [var] -> emit pos $ Cond (tstStmts++tst') var thn' els'
      [_,_] -> lift $ message Error
              ("Condition with in-out flow: " ++ show vars) errPos
      _ -> shouldnt "Single expression expanded to more than 2 args"
flattenStmt' (Loop body) pos = do
    (_,body') <- flattenInner True False
             (flattenStmts $ body ++ [Unplaced $ Next])
    emit pos $ Loop body'
flattenStmt' (For itr gen) pos = do
    vars <- flattenPExp gen
    case vars of
        [] -> lift $
              message Error "'for' generator does not produce a value" 
              (place gen)
        (_:_:_) -> lift $
                   message Error "'for' generator has invalid flow" (place gen)
        [genVar@(Unplaced (Var genVarName ParamIn flowType))] -> do
            -- XXX not generating the right code until we have polymorphism
            flattenStmt 
              (Cond [] (maybePlace (Fncall [] "empty" [genVar]) pos)
               [Unplaced $ Break]
               [maybePlace
                  (ProcCall [] "[|]" Nothing
                   [itr,
                    Unplaced $ 
                    Var genVarName ParamOut flowType,
                    genVar])
                  pos]) pos
        _ -> shouldnt "Generator expression producing unexpected vars"
flattenStmt' Nop pos = emit pos Nop
flattenStmt' Break pos = emit pos Break
flattenStmt' Next pos = emit pos Next


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
    result <- flattenExp (content pexp) Unspecified False (place pexp)
    logFlatten $ "  Result =   " ++ show result
    return result


-- |Flatten a single expressions with specified flow direction to
--  primitive argument(s), a list of statements to execute
--  to bind it, and a list of statements to execute 
--  after the call to store the result appropriately.
--  The first part of the output (a Placed Exp) will always be a list
--  of only atomic Exps and Var references (in any direction).
flattenExp :: Exp -> TypeSpec -> Bool -> OptPos -> Flattener [Placed Exp]
flattenExp exp@(IntValue a) ty cast pos =
    return $ [typeAndPlace exp ty cast pos]
flattenExp exp@(FloatValue a) ty cast pos =
    return $ [typeAndPlace exp ty cast pos]
flattenExp exp@(StringValue a) ty cast pos =
    return $ [typeAndPlace exp ty cast pos]
flattenExp exp@(CharValue a) ty cast pos =
    return $ [typeAndPlace exp ty cast pos]
flattenExp exp@(Var name dir flowType) ty cast pos = do
    logFlatten $ "  Flattening arg " ++ show exp
    let isIn  = flowsIn dir
    let isOut = flowsOut dir
    logFlatten $ "  isIn = " ++ show isIn ++ " isOut = " ++ show isOut
    let flowType' = if isIn && isOut then HalfUpdate else flowType
    logFlatten $ "  flowType' = " ++ show flowType'
    defd <- gets (Set.member name . defdVars)
    if (dir == ParamIn && (not defd))
      then -- Reference to an undefined variable: assume it's meant to be
           -- a niladic function instead of a variable reference
        flattenCall (ProcCall [] name Nothing) ty cast pos []
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
    flattenStmts stmts
    flattenPExp pexp
flattenExp (CondExp cond thn els) ty cast pos = do
    resultName <- tempVar
    let flowType = Implicit pos
    flattenStmt (Cond [] cond
                 [maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content thn) ty cast (place thn),
                               Unplaced $ Var resultName ParamOut flowType])
                  pos]
                 [maybePlace (ForeignCall "llvm" "move" []
                              [typeAndPlace (content els) ty cast (place els),
                               Unplaced $ Var resultName ParamOut flowType])
                  pos])
        pos
    return $ [maybePlace (Var resultName ParamIn flowType) pos]
flattenExp (Fncall maybeMod name exps) ty cast pos = do
    flattenCall (ProcCall maybeMod name Nothing) ty cast pos exps
flattenExp (ForeignFn lang name flags exps) ty cast pos = do
    flattenCall (ForeignCall lang name flags) ty cast pos exps
flattenExp (Typed exp Unspecified _) ty cast pos = do
    flattenExp exp ty cast pos
flattenExp (Typed exp ty cast) _ _ pos = do
    flattenExp exp ty cast pos


flattenCall :: ([Placed Exp] -> Stmt) -> TypeSpec -> Bool -> OptPos
            -> [Placed Exp] -> Flattener [Placed Exp]
flattenCall stmtBuilder ty cast pos exps = do
    logFlatten $ "** flattening args:  " ++ show exps
    resultName <- tempVar
    oldPos <- gets currPos
    uses <- gets stmtUses
    defs <- gets stmtDefs
    modify (\s -> s { stmtUses = Set.empty, stmtDefs = Set.empty, 
                      currPos = pos})
    exps' <- flattenArgs exps
    let exps'' = List.filter (isInExp . content) exps'
    uses' <- gets stmtUses
    defs' <- gets stmtDefs
    modify (\s -> s { stmtUses = uses `Set.union` uses', 
                      stmtDefs = defs `Set.union` defs', 
                      currPos = oldPos})
    let isOut = not $ Set.null defs'
    let isIn = not (isOut && Set.null (defs' `Set.intersection` uses'))
    logFlatten $ "** defines:  " ++ show defs'
    logFlatten $ "** uses   :  " ++ show uses'
    logFlatten $ "** in = " ++ show isIn ++ "; out = " ++ show isOut
    let flowType = if isIn && isOut then HalfUpdate else Implicit pos
    when isIn $ 
      emit pos $ stmtBuilder $ 
      exps'' ++ [typeAndPlace (Var resultName ParamOut flowType) ty cast pos]
    when isOut $ 
      postpone pos $ stmtBuilder $ 
      exps' ++ [typeAndPlace (Var resultName ParamIn flowType) ty cast pos]
    return $
      (if isIn
       then [Unplaced $ maybeType (Var resultName ParamIn flowType) ty cast]
       else []) ++
      (if isOut
       then [Unplaced $ maybeType (Var resultName ParamOut flowType) ty cast]
       else [])


typeAndPlace :: Exp -> TypeSpec -> Bool -> OptPos -> Placed Exp
typeAndPlace exp ty cast pos = maybePlace (maybeType exp ty cast) pos

maybeType :: Exp -> TypeSpec -> Bool -> Exp
maybeType exp Unspecified _ = exp
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
