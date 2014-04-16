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
import Data.Set as Set
import Data.Maybe
import Text.ParserCombinators.Parsec.Pos
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans (lift,liftIO)


----------------------------------------------------------------
--         Turning function calls into procedure calls
--
--  Here we transform in-out arguments, like p(!x), into separate
--  input and output arguments, like p(x, ?x).  We also transform
--  calls of the form p(f(x)) into calls of the form f(x,?t) p(t).  We
--  transform calls with outputs like p(f(?x)) into calls like p(?t)
--  f(?x, t).  Finally, we transform calls like p(f(!x)) into calls
--  like f(x, ?t) p(t, ?t) f(?x, t).
----------------------------------------------------------------

flattenBody :: [Param] -> [Placed Stmt] -> 
               Compiler ([Placed Stmt],[(ProcProto,[Placed Stmt])])
flattenBody params stmts = do
    let vars = List.foldr 
               (\(Param v _ dir) set ->
                 if flowIn dir then Set.insert v set else set)
               Set.empty
               params
    finalState <- execStateT (flattenStmts stmts) $ initFlattenerState vars
    return (
        List.reverse (prefixStmts finalState) ++ 
        List.reverse (flattened finalState) ++ 
        postponed finalState, [])


-- |The Flattener monad is a state transformer monad carrying the 
--  flattener state over the compiler monad.
type Flattener = StateT FlattenerState Compiler


data FlattenerState = Flattener {
    prefixStmts :: [Placed Stmt],   -- ^Init stmts for current loop, reversed
    flattened   :: [Placed Stmt],   -- ^Flattened code generated, reversed
    postponed   :: [Placed Stmt],   -- ^Code to be generated later
    tempCtr     :: Int,             -- ^Temp variable counter
    knownVars   :: Set VarName      -- ^Variables defined up to here
    }


initFlattenerState :: Set VarName -> FlattenerState
initFlattenerState vars = Flattener [] [] [] 0 vars


emit :: OptPos -> Stmt -> Flattener ()
emit pos stmt = do
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


registerVar :: VarName -> Flattener ()
registerVar var =
    modify (\s -> s { knownVars = Set.insert var $ knownVars s })


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
        execStateT (lift inner)
        ((initFlattenerState Set.empty) {
              tempCtr = (tempCtr oldState),
              prefixStmts = if isLoop then [] else prefixStmts oldState})
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
    tst' <- flattenInner False (flattenStmts tst)
    thn' <- flattenInner False (flattenStmts thn)
    els' <- flattenInner False (flattenStmts els)
    emitNoVars pos $ Cond tst' thn' els'
flattenStmt (Loop body initVars finalVars) pos = do
    body' <- flattenInner True 
             (flattenStmts $ body ++ [Unplaced $ Next noVars])
    emitNoVars pos $ Loop body'
flattenStmt (Guard tests val initVars finalVars) pos = do
    tests' <- flattenInner False (flattenStmts tests)
    emitNoVars pos $ Guard tests' val
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
flattenExp exp@(Var name dir) pos = do
    when (flowOut dir) $ registerVar name
    return $ maybePlace exp pos
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


----------------------------------------------------------------
--   turning loops and conditionals into separate procedures
--
--  This code transforms conditionals and loops into calls to freshly
--  generated procedures.  For example, if a: b else: c end would be
--  transformed to a call to gen with gen defined as two separate
--  clauses with guards: def gen: guard a 1 b guard a 0 c end.  This
--  syntax is not valid wybe, but is used as an intermediate step, as
--  it is similar to the AST we will ultimately generate.
--
--  Loops are a little more complicated.  do a b end c d would be
--  transformed into next1, where next1 is defined as def next1: a b
--  next1 end, and break1 is defined as def break1 c d end.  Then Next
--  and Break are handled so that they cancel all the following code
--  in their clause body.  For example, Next a b would be transformed
--  to just next1, where next1 is the next procedure for that loop.
--  Similarly Break a b would be transformed to just break1, where
--  break1 is the break procedure for that loop.  Inside a loop, a
--  conditional must be handled specially, to support breaking out of
--  the loop.  Inside a loop, if a: b else: c end d would be
--  transformed to a call to gen1, where gen2 is defined as def gen2:
--  d end, and gen1 is defined as def gen1: guard a 1 b gen2 guard a 0
--  c gen2 end.  So for example do a if b: Break end c end d would be 
--  transformed into next1, which is defined as def next1 a gen1 end,
--  gen1 is defined as def gen1 guard b 1 break1  guard b 0 gen2 end, 
--  gen2 is defined as def gen2 c next1, and break1 is defined as def 
--  break1 d end.
--
--  The tricky part of all this is handling the arguments to these
--  generated procedures.  For each generated procedure, the input
--  parameters must be a superset of the variables used in the body of
--  the procedure, and must be a subset of the variables defined prior
--  to the generated call.  Similarly, the output parameters must be a
--  a subset of the variables defined in the generated procedure, and
--  must be superset of the variables that will be used following the 
--  generated call.
----------------------------------------------------------------

