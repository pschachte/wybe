--  File     : NumberVars.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Wed Apr  2 11:08:18 2014
--  Purpose  : 
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--

module NumberVars (numberVars) where

import AST
import Data.Map as Map
import Data.List as List
import Control.Monad
import Control.Monad.Trans (lift,liftIO)

import System.IO.Unsafe

-- |Number the versions of variables appearing in a procedure body.
--  This updates (replaces) the VarVers values attached to each 
--  statement to show the version number of each variable in and 
--  after each statement.  Report errors as necessary.
numberVars :: [Param] -> [Placed Stmt] -> OptPos -> 
              Compiler (VarVers, [Placed Stmt], VarVers)
numberVars params stmts pos = do
    initVarVers <- foldM (addParamVers pos) noVars params
    (stmts,finalVarVers) <- numberPStmtsVars initVarVers stmts pos
    return (initVarVers,stmts,finalVarVers)


-- |Gives a VarVers value assigning an initial variable number to 
--  each of the formal parameters of a proc.
addParamVers :: OptPos -> VarVers -> Param -> Compiler VarVers
addParamVers pos vars (Param name _ flow) =
    if flow == ParamIn || flow == ParamInOut
    then if Map.member name vars 
         then do 
             message Error ("repeated input parameter " ++ name) pos
             return vars
         else return $  Map.insert name 0 vars
    else return vars


numberPStmtsVars :: VarVers -> [Placed Stmt] -> OptPos -> 
               Compiler ([Placed Stmt],VarVers)
numberPStmtsVars vars [] _ = return ([],vars)
numberPStmtsVars vars (stmt:stmts) pos = do
    (stmt',vars') <- numberPStmtVars vars stmt pos
    (stmts',vars'') <- numberPStmtsVars vars' stmts pos
    return (stmt':stmts',vars'')

numberPStmtVars :: VarVers -> Placed Stmt -> OptPos -> 
                  Compiler (Placed Stmt,VarVers)
numberPStmtVars vars placed pos = do
    (stmt,vars') <- 
        numberStmtVars vars (content placed) (betterPlace pos placed)
    return (rePlace stmt placed,vars')

numberStmtVars :: VarVers -> Stmt -> OptPos -> Compiler (Stmt,VarVers)
numberStmtVars vars (ProcCall name args _ _) pos = do
    (args',defs) <- numberPExpsVars vars args pos
    vars' <- defineVars vars defs
    return (ProcCall name args' vars vars', vars')
numberStmtVars vars (ForeignCall lang name args _ _) pos = do
    (args',defs) <- numberPExpsVars vars args pos
    vars' <- defineVars vars defs
    return (ForeignCall lang name args' vars vars', vars')
numberStmtVars vars (Cond test thn els _ _) pos = do
    -- liftIO $ putStrLn $ "Handling if-then-else"
    -- liftIO $ putStrLn $ "Incoming vars = " ++ show vars
    (test',testVars) <- numberPStmtsVars vars test pos
    -- liftIO $ putStrLn $ "Vars after condition = " ++ show vars'
    (thn',thnVars) <- numberPStmtsVars testVars thn pos
    -- liftIO $ putStrLn $ "Numbered then = " ++ show thn'
    -- liftIO $ putStrLn $ "then vars = " ++ show thnVars
    -- NB:  thn can use vars defined in test, but els can't
    (els',elsVars) <- numberPStmtsVars vars els pos 
    -- liftIO $ putStrLn $ "Numbered else = " ++ show els'
    -- liftIO $ putStrLn $ "else vars = " ++ show elsVars
    let jointVars = joinVars thnVars elsVars
    -- liftIO $ putStrLn $ "joined    = " ++ show jointVars
    let thn'' = thn' ++ reconcilingAssignments thnVars jointVars
    let els'' = els' ++ reconcilingAssignments elsVars jointVars
    return (Cond test' thn'' els'' vars jointVars,jointVars)
numberStmtVars vars (Loop body _ _) pos = do
    (body',vars') <- numberPStmtsVars vars body pos
    -- XXX bug: only include variables in scope for every loop exit
    return (Loop body' vars vars',vars')
numberStmtVars vars (Guard tests val _ _) pos = do
    (tests',vars') <- numberPStmtsVars vars tests pos
    return (Guard tests' val vars vars',vars')
numberStmtVars vars (Nop) pos = return (Nop,vars)
-- numberStmtVars vars (For name args_ _) pos = do
--     (gen',vars') <- numberGeneratorVars vars gen pos
--     return (For name args vars vars, vars)
numberStmtVars vars (Break) pos = return (Break,vars)
numberStmtVars vars (Next) pos = return (Next,vars)
numberStmtVars vars stmt pos = do
    error $ "flattening error:  " ++ showStmt 4 stmt


numberGeneratorVars :: VarVers -> Generator -> OptPos -> 
                       Compiler (Generator,VarVers)
-- numberGeneratorVars vars (In var pexp) pos = do
--     let vars' = addVarDef vars var [pos]
    
-- numberGeneratorVars vars (InRange var start update step end) pos = do
    
numberGeneratorVars vars gen pos = do
    return (gen,vars)

defineVars :: VarVers -> VarDefs -> Compiler VarVers
defineVars vars defs = do
    reportMultiDefinitions defs
    return $ Map.foldlWithKey addVarDef vars defs

addVarDef :: VarVers -> VarName -> [OptPos] -> VarVers
addVarDef vars v [] = 
    error $ "Internal error: variable with no definitions: " ++ v
addVarDef vars v (pos:_) =
    Map.alter (\old -> case old of
                    Just n -> Just $ n+1
                    Nothing -> Just 0) v vars


type VarDefs = Map VarName [OptPos]

noVarDefs :: VarDefs
noVarDefs = Map.empty


numberPExpsVars :: VarVers -> [Placed Exp] -> OptPos ->
                  Compiler ([Placed Exp],VarDefs)
numberPExpsVars vars exps pos = do
    (revArgs,defs) <- foldM (numberOneExp vars pos) ([],noVarDefs) exps
    return (reverse revArgs, defs)


numberOneExp :: VarVers -> OptPos -> ([Placed Exp],VarDefs) -> Placed Exp ->
              Compiler ([Placed Exp],VarDefs)
numberOneExp vars pos (exps,defs) placed = do
    (exp',defs') <- numberPExpVars vars placed pos
    return ((exp':exps),Map.unionWith (++) defs defs')


numberPExpVars :: VarVers -> Placed Exp -> OptPos ->
                  Compiler (Placed Exp,VarDefs)
numberPExpVars vars placed pos = do
    (exp,defs) <- 
        numberExpVars vars (content placed) (betterPlace pos placed)
    return (rePlace exp placed,defs)

numberExpVars :: VarVers -> Exp -> OptPos -> Compiler (Exp,VarDefs)
numberExpVars vars exp@(IntValue a) _ = return (exp,noVarDefs)
numberExpVars vars exp@(FloatValue a) _ = return (exp,noVarDefs)
numberExpVars vars exp@(StringValue a) _ = return (exp,noVarDefs)
numberExpVars vars exp@(CharValue a) _ = return (exp,noVarDefs)
numberExpVars vars exp@(Var name dir) pos =
    return (exp,if flowOut dir then Map.singleton name [pos] else noVarDefs)
numberExpVars vars exp _ =
    error $ "flattening error:  " ++ show exp
-- numberExpVars vars (Where stmts exp) pos = do
--     -- bindings made by the statements are scoped to the statements
--     (stmts',vars') <- numberPStmtsVars vars stmts pos
--     (exp',defs) <- numberPExpVars vars' exp pos
--     -- XXX Bug: must keep track of highest number used for each var, not
--     -- just the current number.  Here we forget if we've used higher
--     -- numbers for some vars.  Or should that be forbidden?
--     return (Where stmts' exp',defs)
-- numberExpVars vars exp@(CondExp cond thn els) pos = do
--     (cond',condDefs) <- numberPExpVars vars cond pos
--     vars' <- defineVars vars condDefs
--     -- XXX Either report error if then or else branch define vars, or else
--     -- allow it.
--     (thn',thndefs) <- numberPExpVars vars' thn pos
--     (els',elsdefs) <- numberPExpVars vars els pos
--     return (CondExp cond' thn' els',noVarDefs)
-- numberExpVars vars exp@(Fncall fn exps) pos = do
--     (exps',defs) <- numberPExpsVars vars exps pos
--     return (Fncall fn (List.reverse exps'),defs)
-- numberExpVars vars exp@(ForeignFn lang fn exps) pos = do
--     (exps',defs) <- numberPExpsVars vars exps pos
--     return (ForeignFn lang fn (List.reverse exps'),defs)


joinVars :: VarVers -> VarVers -> VarVers
joinVars = Map.intersectionWith max


reportMultiDefinitions :: VarDefs -> Compiler ()
reportMultiDefinitions defs = do
    mapM reportMultiDefn $ assocs defs
    return ()

reportMultiDefn :: (VarName,[OptPos]) -> Compiler ()
reportMultiDefn (name,defs) =
    if List.null (tail defs)
    then return ()
    else message Error 
         ("Variable '" ++ name ++ "' multiply defined") $ head defs


reconcilingAssignments :: VarVers -> VarVers -> [Placed Stmt]
reconcilingAssignments caseVars jointVars =
    let vars = List.filter (\v -> caseVars ! v /= jointVars ! v) $ keys jointVars
    in  snd $ mapAccumL (reconcileOne jointVars) caseVars vars


reconcileOne :: VarVers -> VarVers -> VarName -> (VarVers,Placed Stmt)        
reconcileOne targetVars vars var =
    let varVer = targetVars ! var
        vars'  = Map.insert var varVer vars
    in (vars',
        Unplaced $
        ProcCall "=" [Unplaced $ Var var ParamOut, Unplaced $ Var var ParamIn]
        vars vars')
