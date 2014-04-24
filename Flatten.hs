--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Flatten function calls (expressions) into procedure calls
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--
--  Here we transform in-out arguments, like p(!x), into separate
--  input and output arguments, like p(x, ?x).  We also transform
--  calls of the form p(f(x)) into calls of the form f(x,?t) p(t).  We
--  transform calls with outputs like p(f(?x)) into calls like p(?t)
--  f(?x, t).  Finally, we transform calls like p(f(!x)) into calls
--  like f(x, ?t) p(t, ?t) f(?x, t).
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


flattenProto :: ProcProto -> Compiler ProcProto
flattenProto (ProcProto name params) = do
    return $ ProcProto name $ concatMap flattenParam params


flattenBody :: [Placed Stmt] -> Compiler [Placed Stmt]
flattenBody stmts = do
    finalState <- execStateT (flattenStmts stmts) $ initFlattenerState
    return $
      List.reverse (prefixStmts finalState) ++ 
      List.reverse (flattened finalState) ++ 
      postponed finalState


-- |The Flattener monad is a state transformer monad carrying the 
--  flattener state over the compiler monad.
type Flattener = StateT FlattenerState Compiler


data FlattenerState = Flattener {
    prefixStmts :: [Placed Stmt],   -- ^Init stmts for current loop, reversed
    flattened   :: [Placed Stmt],   -- ^Flattened code generated, reversed
    postponed   :: [Placed Stmt],   -- ^Code to be generated later
    tempCtr     :: Int              -- ^Temp variable counter
    }


initFlattenerState :: FlattenerState
initFlattenerState = Flattener [] [] [] 0


emit :: OptPos -> Stmt -> Flattener ()
emit pos stmt = do
    -- liftIO $ putStrLn $ "** Emitting:  " ++ showStmt 14 stmt
    stmts <- gets flattened
    modify (\s -> s { flattened = maybePlace stmt pos:stmts })


emitNoVars :: OptPos -> (VarVers -> VarVers -> Stmt) -> Flattener ()
emitNoVars pos stmt = emit pos (stmt noVars noVars)


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
    modify (\s -> s { flattened = stmts ++ stmts', postponed = [] })


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
flattenStmt (Cond tst thn els initVars finalVars) pos = do
    -- liftIO $ putStrLn $ "** Flattening test:\n" ++ showBody 4 tst
    tst' <- flattenInner False (flattenStmts tst)
    -- liftIO $ putStrLn $ "** Result:\n" ++ showBody 4 tst'
    thn' <- flattenInner False (flattenStmts thn)
    els' <- flattenInner False (flattenStmts els)
    emitNoVars pos $ Cond tst' thn' els'
flattenStmt (Loop body initVars finalVars) pos = do
    body' <- flattenInner True 
             (flattenStmts $ body ++ [Unplaced $ Next noVars])
    emitNoVars pos $ Loop body'
flattenStmt (For itr gen initVars finalVars) pos = do
    genVar <- tempVar
    saveInit pos $ 
      ProcCall "init_seq" [gen, Unplaced $ Var genVar ParamOut] noVars noVars
    flattenStmt (Cond [maybePlace 
                       (ProcCall "in" [itr,Unplaced $ Var genVar ParamIn,
                                       Unplaced $ Var genVar ParamOut]
                        noVars noVars)
                       pos]
                 [Unplaced $ Nop noVars]
                 [Unplaced $ Break noVars]
                 initVars finalVars)
      pos
flattenStmt stmt@(Nop _) pos =
    emit pos stmt
flattenStmt stmt@(Break _) pos =
    emit pos stmt
flattenStmt stmt@(Next _) pos =
    emit pos stmt


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
    return $ 
      (if flowsIn dir then [maybePlace (Var name ParamIn) pos] else []) ++
      (if flowsOut dir then [maybePlace (Var name ParamOut) pos] else [])
flattenExp (Where stmts pexp) _ = do
    flattenStmts stmts
    flattenPExp pexp
flattenExp (CondExp cond thn els) pos = do
    resultName <- tempVar
    flattenStmt (Cond cond
                 [Unplaced $ ProcCall "=" 
                  [Unplaced $ Var resultName ParamOut,thn] noVars noVars]
                 [Unplaced $ ProcCall "=" 
                  [Unplaced $ Var resultName ParamOut,els] noVars noVars]
                 noVars noVars) pos
    return $ [Unplaced $ Var resultName ParamIn]
flattenExp (Fncall name exps) pos = do
    resultName <- tempVar
    exps' <- flattenArgs exps
    emitNoVars pos $ ProcCall name $
      exps' ++ [Unplaced $ Var resultName ParamOut]
    return $ [Unplaced $ Var resultName ParamIn]
flattenExp (ForeignFn lang name exps) pos = do
    resultName <- tempVar
    exps' <- flattenArgs exps
    emitNoVars pos $ ForeignCall lang name $
      exps' ++ [Unplaced $ Var resultName ParamOut]
    return $ [Unplaced $ Var resultName ParamIn]


flattenParam :: Param -> [Param]
flattenParam (Param name typ dir) =
    (if flowsIn dir then [Param name typ ParamIn] else []) ++
    (if flowsOut dir then [Param name typ ParamOut] else [])
    