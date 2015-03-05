--  File     : Unbranch.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Apr 17 13:48:52 2014
--  Purpose  : Turn loops and conditionals into separate procedures
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--
--  This code transforms loops into fresh recursive procs, and ensures
--  that all conditionals are the last statements in their respective
--  bodies.  Note that conditionals can be nested, but at the end of
--  the conditional, they must return to the caller.  This is handled
--  by introducing a fresh proc for any code that follows the
--  conditional.  The reason for this transformation is that a later
--  pass will convert to a logic programming form which implements
--  conditionals with separate clauses, each of which returns on
--  completion.
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

module Unbranch (unbranchProc, unbranchBody) where

import AST
import Data.Map as Map
import Data.List as List
import Data.Maybe
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans (lift,liftIO)

-- |Transform away all loops, and conditionals other than as the only
-- statement in their block.
unbranchProc :: ProcDef -> Compiler ProcDef
unbranchProc proc = do
    let ProcDefSrc body = procImpln proc
    let params = procProtoParams $ procProto proc
    (body',newProcs) <- unbranchBody params body
    let proc' = proc { procImpln = ProcDefSrc body' }
    let tmpCount = procTmpCount proc
    mapM_ (addProc tmpCount) newProcs
    return proc'


unbranchBody :: [Param] -> [Placed Stmt] -> Compiler ([Placed Stmt],[Item])
unbranchBody params stmts = do
    let vars = inputParamNames params
    (stmts',st) <- runStateT (unbranchStmts stmts) $ 
                   initUnbrancherState vars
    return (stmts',brNewDefs st)


----------------------------------------------------------------
--                  Handling the Unbrancher monad
----------------------------------------------------------------

-- |The Unbrancher monad is a state transformer monad carrying the 
--  flattener state over the compiler monad.
type Unbrancher = StateT UnbrancherState Compiler

type VarDict = Map VarName TypeSpec


data UnbrancherState = Unbrancher {
    brLoopInfo   :: LoopInfo,     -- ^If in a loop, the break and continue stmts
    brVars       :: VarDict,      -- ^Variables defined up to here
    -- brExitVars   :: VarDict,  -- ^Variables defined up to loop exit
    brTerminated :: Bool,         -- ^Whether code so far included a Break or
                                  --  Next, which terminate execution
    brNewDefs    :: [Item]        -- ^Generated auxilliary procedures
    }


data LoopInfo = LoopInfo {
    loopNext :: Placed Stmt,      -- ^stmt to go to the next loop iteration
    loopBreak    :: Placed Stmt,      -- ^stmt to break out of the loop
    loopInit :: [Placed Stmt],    -- ^code to initialise before entering loop
    loopTerm :: [Placed Stmt]}    -- ^code to wrap up after leaving loop
    | NoLoop
    deriving (Eq)


initUnbrancherState :: VarDict -> UnbrancherState
initUnbrancherState vars =
    Unbrancher NoLoop vars False []


setLoopInfo :: Placed Stmt -> Placed Stmt -> Unbrancher ()
setLoopInfo next break = do
    dbgPrintLn $ "** next call: " ++ showStmt 14 (content next)
    dbgPrintLn $ "** break call: " ++ showStmt 15 (content break)
    modify (\s -> s { brLoopInfo = LoopInfo next break [] [] })


setNoLoop :: Unbrancher ()
setNoLoop = modify (\s -> s { brLoopInfo = NoLoop })


defVar :: VarName -> TypeSpec -> Unbrancher ()
defVar var ty =
    modify (\s -> s { brVars = Map.insert var ty $ brVars s })


setVars :: VarDict -> Unbrancher ()
setVars vs =
    modify (\s -> s { brVars = vs })


ifTerminated :: Unbrancher a -> Unbrancher a -> Unbrancher a
ifTerminated thn els = do
    term <- gets brTerminated
    if term then thn else els


setTerminated :: Bool -> Unbrancher ()
setTerminated term = modify (\s -> s { brTerminated = term })


newProcName :: Unbrancher String
newProcName = do
    lift genProcName


genProc :: ProcProto -> [Placed Stmt] -> Unbrancher ()
genProc proto stmts = do
    dbgPrintLn $ "** Generating proc:\n"
      ++ show (ProcDecl Private proto stmts Nothing)
    let item = ProcDecl Private proto stmts Nothing
    modify (\s -> s { brNewDefs = item:brNewDefs s })


dbgPrintLn :: String -> Unbrancher ()
dbgPrintLn s = do
    -- liftIO $ putStrLn s
    return ()

----------------------------------------------------------------
--                 Unbranching statement sequences
----------------------------------------------------------------

unbranchStmts :: [Placed Stmt] -> Unbrancher [Placed Stmt]
unbranchStmts [] = return []
unbranchStmts (stmt:stmts) = do
    vars <- gets brVars
    dbgPrintLn $ "unbranching stmt\n    " ++ showStmt 4 (content stmt) ++
      "\n  with vars " ++ show vars
    ifTerminated (return []) (unbranchStmt (content stmt) (place stmt) stmts)


unbranchStmt :: Stmt -> OptPos -> [Placed Stmt] -> Unbrancher [Placed Stmt]
unbranchStmt stmt@(ProcCall _ _ _ args) pos stmts = do
    defArgs args
    stmts' <- unbranchStmts stmts
    return $ (maybePlace stmt pos):stmts'
unbranchStmt stmt@(ForeignCall _ _ _ args) pos stmts = do
    defArgs args
    stmts' <- unbranchStmts stmts
    return $ (maybePlace stmt pos):stmts'
unbranchStmt (Cond tstStmts tstVar thn els) pos stmts = do
    beforeVars <- gets brVars
    dbgPrintLn $ "* test (" ++ show tstVar ++ "): " ++ showBody 8 tstStmts
    dbgPrintLn $ "* Vars before test: " ++ show beforeVars
    tstStmts' <- unbranchStmts tstStmts
    (thn',thnVars,thnTerm) <- unbranchBranch thn
    setVars beforeVars
    (els',elsVars,elsTerm) <- unbranchBranch els
    let afterVars = varsAfterITE thnVars thnTerm elsVars elsTerm
    dbgPrintLn $ "* Vars after conditional: " ++ show afterVars
    switchName <- newProcName
    lp <- gets brLoopInfo
    if lp == NoLoop || stmts == []
      then do
        switch <- factorFreshProc switchName beforeVars afterVars pos
                  [maybePlace (Cond tstStmts' tstVar thn' els') pos]
        dbgPrintLn $ "* Generated switch " ++ showStmt 4 (content switch)
        setVars beforeVars
        unbranchStmts (switch:stmts)
      else do
        setVars afterVars
        stmts' <- unbranchStmts stmts
        finalVars <- if thnTerm || elsTerm 
                     then return afterVars
                     else gets brVars
        dbgPrintLn $ "* Loop body:\n" ++ showBody 4 stmts
        dbgPrintLn $ "* Loop body inputs = " ++ show afterVars
        dbgPrintLn $ "* Loop body outputs = " ++ show finalVars
        contName <- newProcName
        let exitVs = Map.intersection thnVars elsVars
        cont <- factorFreshProc contName exitVs finalVars Nothing stmts'
        dbgPrintLn $ "* Generated continuation " ++ showStmt 4 (content cont)
        switch <- factorFreshProc switchName beforeVars finalVars {- afterVars -} pos
                  [maybePlace 
                   (Cond tstStmts' tstVar
                    (if thnTerm then thn' else thn' ++ [cont]) 
                    (if elsTerm then els' else els' ++ [cont])) pos]
        dbgPrintLn $ "* Generated loop switch " ++ showStmt 4 (content switch)
        return [switch]
-- Determining the set of variables (certain to be) defined after a
-- loop is a bit tricky, because we transform a loop together with the
-- following statements.  The variables available at the start of the
-- code following the loop is the the intersection of the sets of
-- variables defined after 0, 1, 2, etc iterations, which is the 
-- intersection of the sets of variables defined at each (usually 
-- conditional) loop break.
unbranchStmt (Loop body) pos stmts = do
    dbgPrintLn $ "* Handling loop:\n" ++ showBody 4 body
    beforeVars <- gets brVars
    dbgPrintLn $ "* Vars before loop: " ++ show beforeVars
    let afterVars = fromMaybe Map.empty $ snd $ loopExitVars beforeVars body
    dbgPrintLn $ "* Vars after loop: " ++ show afterVars
    setVars afterVars
    stmts' <- unbranchStmts stmts
    finalVars <- gets brVars
    dbgPrintLn $ "* Vars after body: " ++ show finalVars
    breakName <- newProcName
    brk <- factorFreshProc breakName afterVars finalVars Nothing stmts'
    dbgPrintLn $ "* Generated break " ++ showStmt 4 (content brk)
    loopName <- newProcName
    next <- newProcCall loopName beforeVars afterVars pos
    setLoopInfo next brk
    setVars beforeVars
    body' <- unbranchStmts $ body ++ [next]
    _ <- factorFreshProc loopName beforeVars afterVars pos body'
    dbgPrintLn $ "* Generated loop " ++ showStmt 4 (content next)
    setNoLoop
    setVars finalVars
    -- dbgPrintLn $ "* Finished handling loop"
    return [next]
unbranchStmt (For _ _) _ _ =
    shouldnt "flattening should have removed For statements"
unbranchStmt (Nop) _ stmts =
    unbranchStmts stmts         -- might as well filter out Nops
unbranchStmt (Break) pos _ = do
    inLoop <- gets ((/= NoLoop) . brLoopInfo)
    if inLoop 
      then do
        brk <- gets (Unbranch.loopBreak . brLoopInfo)
        setTerminated True
        return [brk]
      else do
        lift $ message Error "Break outside a loop" pos
        return []
unbranchStmt (Next) pos _ = do
    inLoop <- gets ((/= NoLoop) . brLoopInfo)
    if inLoop 
      then do
        next <- gets (loopNext . brLoopInfo)
        setTerminated True
        return [next]
      else do
        lift $ message Error "Next outside a loop" pos
        return []


unbranchBranch ::  [Placed Stmt] -> Unbrancher ([Placed Stmt],VarDict,Bool)
unbranchBranch branch = do
    branch' <- unbranchStmts branch
    branchVars <- gets brVars
    dbgPrintLn $ "* Vars after then branch: " ++ show branchVars
    branchTerm <- gets brTerminated
    dbgPrintLn $
      "* Then branch is" ++ (if branchTerm then "" else " NOT") ++ " terminal"
    setTerminated False
    return (branch', branchVars,branchTerm)


varsAfterITE :: VarDict -> Bool -> VarDict -> Bool -> VarDict
varsAfterITE thnVars True elsVars True   = Map.intersection thnVars elsVars
varsAfterITE thnVars True elsVars False  = thnVars
varsAfterITE thnVars False elsVars True  = elsVars
varsAfterITE thnVars False elsVars False = Map.intersection thnVars elsVars


-- |The set of names of the input parameters
inputParamNames :: [Param] -> VarDict
inputParamNames params =
    List.foldr 
    (\(Param v ty dir _) vdict -> 
         if flowsIn dir then Map.insert v ty vdict else vdict)
    Map.empty params    


-- |The set of variables defined by the list of expressions.
defArgs :: [Placed Exp] -> Unbrancher ()
defArgs = mapM_ (defArg . content)


-- |The set of variables defined by the expression.  Since the
--  expression is already flattened, it will only be a constant, in
--  which case it doesn't define any variables, or a variable, in
--  which case it might.
defArg :: Exp -> Unbrancher ()
defArg = ifIsVarDef defVar (return ())


-- |Apply the function if the expression as a variable assignment,
--  otherwise just take the second argument.
ifIsVarDef :: (VarName -> TypeSpec -> t) -> t -> Exp -> t
ifIsVarDef f v expr = ifIsVarDef' f v expr Unspecified

ifIsVarDef' :: (VarName -> TypeSpec -> t) -> t -> Exp -> TypeSpec -> t
ifIsVarDef' f v (Typed expr ty) _ = ifIsVarDef' f v expr ty
ifIsVarDef' f v (Var name dir _) ty =
    if flowsOut dir then f name ty else v
ifIsVarDef' _ v _ _ = v


outputVars :: VarDict -> [Placed Exp] -> VarDict
outputVars = 
    List.foldr ((ifIsVarDef Map.insert id)  . content)


-- |Generate a fresh proc 
factorFreshProc :: ProcName -> (VarDict) -> (VarDict) ->
                   OptPos -> [Placed Stmt] -> Unbrancher (Placed Stmt)
factorFreshProc pname inVars outVars pos body = do
    proto <- newProcProto pname inVars outVars
    genProc proto body
    newProcCall pname inVars outVars pos


varExp :: FlowDirection -> VarName -> TypeSpec -> Placed Exp
varExp flow var ty = Unplaced $ Typed (Var var flow Ordinary) ty


newProcCall :: ProcName -> VarDict -> VarDict -> OptPos -> 
               Unbrancher (Placed Stmt)
newProcCall name inVars outVars pos = do
    let inArgs  = List.map (uncurry $ varExp ParamIn) $ Map.toList inVars
    let outArgs = List.map (uncurry $ varExp ParamOut) $ Map.toList outVars
    currMod <- lift getModuleSpec
    return $ maybePlace (ProcCall currMod name (Just 0) (inArgs ++ outArgs)) pos


newProcProto :: ProcName -> VarDict -> VarDict -> Unbrancher ProcProto
newProcProto name inVars outVars = do
    let inParams  = [Param v ty ParamIn Ordinary
                    | (v,ty) <- Map.toList inVars]
    let outParams = [Param v ty ParamOut Ordinary
                    | (v,ty) <- Map.toList outVars]
    return $ ProcProto name (inParams ++ outParams) []

-- Given the specified environment and a statement sequence, returns the
-- environment following the statements and the loop exit environment.
-- The loop exit environment is Just the intersection of the environments
-- at all the breaks in the scope of the loop, or Nothing if there are no
-- such breaks.
loopExitVars :: VarDict -> [Placed Stmt] -> (VarDict, Maybe VarDict)
loopExitVars vars pstmts =
  List.foldl stmtExitVars (vars,Nothing) $ List.map content pstmts


stmtExitVars :: (VarDict, Maybe VarDict) -> Stmt -> (VarDict, Maybe VarDict)
stmtExitVars  (vars,exits) (ProcCall _ _ _ args) =
    (outputVars vars args, exits)
stmtExitVars (vars,exits) (ForeignCall _ _ _ args) =
    (outputVars vars args, exits)
stmtExitVars (vars,_) (Cond tstStmts _ thn els) =
    let (tstVars,tstExit) = loopExitVars vars tstStmts
        (thnVars,thnExit) = loopExitVars tstVars thn
        (elsVars,elsExit) = loopExitVars vars els
    in  (Map.intersection thnVars elsVars, intersectExit thnExit elsExit)
stmtExitVars (vars,exits) (Loop body) =
    let (bodyVars,bodyExit) = loopExitVars vars body
    in  case bodyExit of 
      Nothing -> (Map.empty, exits)
      Just exits' -> (exits', exits)
stmtExitVars (vars,exits)  (Nop) = (vars,exits)
stmtExitVars _ (For _ _) =
    shouldnt "flattening should have removed For statements"
stmtExitVars (vars,exits)  (Break) = 
  (Map.empty, intersectExit (Just vars) exits)
stmtExitVars (vars,exits) (Next) = (Map.empty, exits)


intersectExit (Just v1) (Just v2) = Just $ Map.intersection v1 v2
intersectExit Nothing x = x
intersectExit x Nothing = x
