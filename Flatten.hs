--  File     : Flatten.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Flatten function calls (expressions) into procedure calls
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
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

module Flatten (flattenProto, flattenBody) where

import AST
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

flattenProto :: ProcProto -> Compiler ProcProto
flattenProto (ProcProto name params) = do
    return $ ProcProto name $ concatMap flattenParam params


flattenBody :: [Placed Stmt] -> Compiler ([Placed Stmt],Int)
flattenBody stmts = do
    finalState <- execStateT (flattenStmts stmts) $ initFlattenerState
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
    flattened   :: [Placed Stmt],   -- ^Flattened code generated, reversed
    postponed   :: [Placed Stmt],   -- ^Code to be generated later
    tempCtr     :: Int,             -- ^Temp variable counter
    currPos     :: OptPos,          -- ^Position of current statement
    stmtDefs    :: Set VarName,     -- ^Variables defined by this statement
    stmtUses    :: Set VarName      -- ^Variables used by this statement
    }


initFlattenerState :: FlattenerState
initFlattenerState = Flattener [] [] [] 0 Nothing Set.empty Set.empty


emit :: OptPos -> Stmt -> Flattener ()
emit pos stmt = do
    -- liftIO $ putStrLn $ "** Emitting:  " ++ showStmt 14 stmt
    stmts <- gets flattened
    modify (\s -> s { flattened = maybePlace stmt pos:stmts })


postpone :: OptPos -> Stmt -> Flattener ()
postpone pos stmt = do
    stmts <- gets postponed
    modify (\s -> s { postponed = maybePlace stmt pos:stmts })


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
    return $ "tmp$" ++ show ctr


flattenInner :: Bool -> Flattener () -> Flattener [Placed Stmt]
flattenInner isLoop inner = do
    oldState <- get
    innerState <-
        lift (execStateT inner
              (initFlattenerState {
                    tempCtr = (tempCtr oldState),
                    prefixStmts = if isLoop then [] else prefixStmts oldState}))
    -- liftIO $ putStrLn $ "** Prefix:\n" ++ 
    --   showBody 4 (prefixStmts innerState)
    -- liftIO $ putStrLn $ "** Flattened:\n" ++ 
    --   showBody 4 (flattened innerState)
    -- liftIO $ putStrLn $ "** Postponed:\n" ++ 
    --   showBody 4 (postponed innerState)
    put $ oldState { tempCtr = tempCtr innerState }
    if isLoop
      then flattenStmts $ prefixStmts innerState
      else modify (\s -> s { prefixStmts = prefixStmts innerState })
    return $ List.reverse $ flattened innerState


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


-- |Flatten the specified statement
flattenStmt :: Stmt -> OptPos -> Flattener ()
flattenStmt (ProcCall maybeMod name args) pos = do
    args' <- flattenStmtArgs args pos
    emit pos $ ProcCall maybeMod name args'
    emitPostponed
flattenStmt (ForeignCall lang name flags args) pos = do
    args' <- flattenStmtArgs args pos
    emit pos $ ForeignCall lang name flags args'
    emitPostponed
flattenStmt (Cond tst thn els) pos = do
    -- liftIO $ putStrLn $ "** Flattening test:\n" ++ showBody 4 tst
    tst' <- flattenInner False (flattenStmts tst)
    -- liftIO $ putStrLn $ "** Result:\n" ++ showBody 4 tst'
    thn' <- flattenInner False (flattenStmts thn)
    els' <- flattenInner False (flattenStmts els)
    emit pos $ Cond tst' thn' els'
flattenStmt (Loop body) pos = do
    body' <- flattenInner True 
             (flattenStmts $ body ++ [Unplaced $ Next])
    emit pos $ Loop body'
flattenStmt (For itr gen) pos = do
    genVar <- tempVar
    saveInit pos $ 
      ProcCall [] "init_seq" [gen, Unplaced $ Var genVar ParamOut]
    flattenStmt (Cond [maybePlace 
                       (ProcCall [] "in" [itr,
                                               Unplaced $ Var genVar ParamIn,
                                               Unplaced $ Var genVar ParamOut])
                       pos]
                 [Unplaced $ Nop]
                 [Unplaced $ Break])
      pos
-- other kinds of statements (Nop, Break, Next) are left as is.
flattenStmt stmt pos =
    emit pos stmt


----------------------------------------------------------------
--                      Flattening Expressions
----------------------------------------------------------------

-- |Compile a list of expressions as proc call arguments to a list of 
--  primitive arguments, a list of statements to execute before the 
--  call to bind those arguments, and a list of statements to execute 
--  after the call to store the results appropriately.
flattenArgs :: [Placed Exp] -> Flattener [Placed Exp]
flattenArgs args = do
    argListList <- mapM flattenPExp args
    return $ concat argListList

flattenPExp :: Placed Exp -> Flattener [Placed Exp]
flattenPExp pexp = flattenExp (content pexp) (place pexp)


-- |Flatten a single expressions with specified flow direction to
--  primitive argument(s), a list of statements to execute
--  to bind it, and a list of statements to execute 
--  after the call to store the result appropriately.
--  The first part of the output (a Placed Exp) will always be a list
--  of only atomic Exps and Var references (in any direction).
flattenExp :: Exp -> OptPos -> Flattener [Placed Exp]
flattenExp exp@(IntValue a) pos =
    return $ [maybePlace exp pos]
flattenExp exp@(FloatValue a) pos =
    return $ [maybePlace exp pos]
flattenExp exp@(StringValue a) pos =
    return $ [maybePlace exp pos]
flattenExp exp@(CharValue a) pos =
    return $ [maybePlace exp pos]
flattenExp exp@(Var name dir) pos = do
    noteVarMention name dir
    return $ 
      (if flowsIn dir then [maybePlace (Var name ParamIn) pos] else []) ++
      (if flowsOut dir then [maybePlace (Var name ParamOut) pos] else [])
flattenExp (Where stmts pexp) _ = do
    flattenStmts stmts
    flattenPExp pexp
flattenExp (CondExp cond thn els) pos = do
    resultName <- tempVar
    flattenStmt (Cond cond
                 [Unplaced $ ProcCall [] "=" 
                  [Unplaced $ Var resultName ParamOut,thn]]
                 [Unplaced $ ProcCall [] "=" 
                  [Unplaced $ Var resultName ParamOut,els]]) pos
    return $ [Unplaced $ Var resultName ParamIn]
flattenExp (Fncall maybeMod name exps) pos = do
    flattenCall (ProcCall maybeMod name) pos exps
flattenExp (ForeignFn lang name flags exps) pos = do
    flattenCall (ForeignCall lang name flags) pos exps
flattenExp (Typed exp Unspecified) pos = do
    flattenExp exp pos
flattenExp (Typed exp typ) pos = do
    exps <- flattenExp exp pos
    return $ List.map (fmap $ flip Typed typ) exps


flattenCall :: ([Placed Exp] -> Stmt) -> OptPos -> [Placed Exp] ->
               Flattener [Placed Exp]
flattenCall stmtBuilder pos exps = do
    -- liftIO $ putStrLn $ "** flattening args:  " ++ show exps
    resultName <- tempVar
    oldPos <- gets currPos
    uses <- gets stmtUses
    defs <- gets stmtDefs
    modify (\s -> s { stmtUses = Set.empty, stmtDefs = Set.empty, currPos = pos})
    exps' <- flattenArgs exps
    let exps'' = List.filter (isInExp . content) exps'
    uses' <- gets stmtUses
    defs' <- gets stmtDefs
    modify (\s -> s { stmtUses = uses `Set.union` uses', 
                      stmtDefs = defs `Set.union` defs', 
                      currPos = oldPos})
    let isOut = not $ Set.null defs'
    let isIn = not (isOut && Set.null (defs' `Set.intersection` uses'))
    -- liftIO $ putStrLn $ "** defines:  " ++ show defs'
    -- liftIO $ putStrLn $ "** uses   :  " ++ show uses'
    -- liftIO $ putStrLn $ "** in = " ++ show isIn ++ "; out = " ++ show isOut
    when isIn $ 
      emit pos $ stmtBuilder $ exps'' ++ [Unplaced $ Var resultName ParamOut]
    when isOut $ 
      postpone pos $ stmtBuilder $ exps' ++ [Unplaced $ Var resultName ParamIn]
    return $
      (if isIn then [Unplaced $ Var resultName ParamIn] else []) ++
      (if isOut then [Unplaced $ Var resultName ParamOut] else [])


isInExp :: Exp -> Bool
isInExp (Var _ dir) = flowsIn dir
isInExp _ = True

flattenParam :: Param -> [Param]
flattenParam (Param name typ dir) =
    (if flowsIn dir then [Param name typ ParamIn] else []) ++
    (if flowsOut dir then [Param name typ ParamOut] else [])
    
