--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Convert parse tree into AST
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

-- |Support for normalising wybe code as parsed to a simpler form
--  to make compiling easier.
module Flatten (flattenBody) where

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


flattenBody :: [Placed Stmt] -> ([Placed Stmt],Int)
flattenBody stmts =
    let (revStmts,postponed,tempCtr) = 
            execState (flattenStmts stmts) ([], [], 0)
    in  (List.reverse revStmts ++ postponed, tempCtr)


-- |The clause compiler monad is a state transformer monad carrying the 
--  clause compiler state over the compiler monad.
type Flattener = State ([Placed Stmt],[Placed Stmt],Int)


emit :: OptPos -> Stmt -> Flattener ()
emit pos stmt = do
    (stmts,postponed,ctr) <- get
    put (maybePlace stmt pos:stmts,postponed,ctr)


emitNoVars :: OptPos -> (VarVers -> VarVers -> Stmt) -> Flattener ()
emitNoVars pos stmt = emit pos (stmt noVars noVars)


postpone :: OptPos -> Stmt -> Flattener ()
postpone pos stmt = do
    (stmts,postponed,ctr) <- get
    put (stmts,maybePlace stmt pos:postponed,ctr)


emitPostponed :: Flattener ()
emitPostponed = do
    (stmts,postponed,ctr) <- get
    put (postponed++stmts,[],ctr)


-- |Return a fresh variable name.
tempVar :: Flattener VarName
tempVar = do
    (stmts,postponed,ctr) <- get
    put (stmts,postponed,ctr+1)
    return $ "$tmp" ++ (show ctr)


flattenInner :: [Placed Stmt] -> Flattener [Placed Stmt]
flattenInner stmts = do
    (oldStmts,oldPostponed,oldCtr) <- get
    let (innerStmts,innerPostponed,newCtr) = 
            execState (flattenStmts stmts) ([],[],oldCtr)
    put (oldStmts,oldPostponed,newCtr)
    return $ reverse innerStmts ++ innerPostponed


-- |Flatten the specified statements to primitive statements.
flattenStmts :: [Placed Stmt] -> Flattener ()
flattenStmts stmts = 
    mapM_ (\pstmt -> flattenStmt (content pstmt) (place pstmt)) stmts


-- |Flatten the specified statement
flattenStmt :: Stmt -> OptPos -> Flattener ()
flattenStmt (ProcCall name args _ _) pos = do
    args' <- flattenArgs args
    emitNoVars pos $ ProcCall name args'
    emitPostponed
flattenStmt (ForeignCall lang name args initVars finalVars) pos = do
    args' <- flattenArgs args
    emitNoVars pos $ ForeignCall lang name args'
    emitPostponed
flattenStmt (Cond exp thn els initVars finalVars) pos = do
    exp' <- flattenPExp exp
    thn' <- flattenInner thn
    els' <- flattenInner els
    emitNoVars pos $ Cond exp thn' els'
flattenStmt (Loop body initVars finalVars) pos = do
    body' <- flattenInner body
    emitNoVars pos $ Loop body
flattenStmt (Guard exp val initVars finalVars) pos = do
    exp' <- flattenPExp exp
    emitNoVars pos $ Guard exp' val
flattenStmt Nop pos =
    emit pos Nop
flattenStmt (For gen initVars finalVars) pos = do
    emitNoVars pos $ For gen
flattenStmt Break pos = do
    emit pos Break
flattenStmt Next pos = do
    emit pos Next


-- |Compile a list of expressions as proc call arguments to a list of 
--  primitive arguments, a list of statements to execute before the 
--  call to bind those arguments, and a list of statements to execute 
--  after the call to store the results appropriately.
flattenArgs :: [Placed Exp] -> Flattener [Placed Exp]
flattenArgs = mapM flattenPExp


flattenPExp :: Placed Exp -> Flattener (Placed Exp)
flattenPExp pexp = flattenExp (content pexp) (place pexp)


-- |Flatten a single expressions with specified flow direction to
--  primitive argument(s), a list of statements to execute
--  to bind it, and a list of statements to execute 
--  after the call to store the result appropriately.
--  The first part of the output (a Placed Exp) will always be a list
--  of only atomic Exps and Var references (in any direction).
flattenExp :: Exp -> OptPos -> Flattener (Placed Exp)
flattenExp exp@(IntValue a) pos =
    return $ maybePlace exp pos
flattenExp exp@(FloatValue a) pos =
    return $ maybePlace exp pos
flattenExp exp@(StringValue a) pos =
    return $ maybePlace exp pos
flattenExp exp@(CharValue a) pos =
    return $ maybePlace exp pos
flattenExp exp@(Var name dir) pos =
    return $ maybePlace exp pos
flattenExp (Where stmts pexp) _ = do
    flattenStmts stmts
    flattenPExp pexp
flattenExp (CondExp cond thn els) pos = do
    cond' <- flattenPExp cond
    resultName <- tempVar
    flattenStmt (Cond cond'
                 [Unplaced $ ProcCall "=" 
                  [Unplaced $ Var resultName ParamOut,thn] noVars noVars]
                 [Unplaced $ ProcCall "=" 
                  [Unplaced $ Var resultName ParamOut,els] noVars noVars]
                 noVars noVars) pos
    return $ Unplaced $ Var resultName ParamIn
flattenExp (Fncall name exps) pos = do
    resultName <- tempVar
    exps' <- flattenArgs exps
    emitNoVars pos $ ProcCall name $
      exps' ++ [Unplaced $ Var resultName ParamOut]
    return $ Unplaced $ Var resultName ParamIn
flattenExp (ForeignFn lang name exps) pos = do
    resultName <- tempVar
    exps' <- flattenArgs exps
    emitNoVars pos $ ForeignCall lang name $
      exps' ++ [Unplaced $ Var resultName ParamOut]
    return $ Unplaced $ Var resultName ParamIn
