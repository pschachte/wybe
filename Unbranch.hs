{-# LANGUAGE OverloadedStrings #-}
--  File     : Unbranch.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu Apr 17 13:48:52 2014
--  Purpose  : Turn loops and conditionals into separate procedures
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
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
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.List as List
import Data.Map as Map
import Data.Maybe
import Options (LogSelection(Unbranch))

-- |Transform away all loops, and conditionals other than as the only
-- statement in their block.
unbranchProc :: ProcDef -> Compiler ProcDef
unbranchProc proc = do
    logMsg Unbranch $ "** Unbranching proc " ++ procName proc
    let ProcDefSrc body = procImpln proc
    let setup = if procDetism proc == SemiDet
                then [Unplaced $ ForeignCall "lpvm" "cast" []
                      [Unplaced $ Typed (IntValue 1)
                       (TypeSpec ["wybe"] "int" []) True,
                       Unplaced $ Typed (Var "$$" ParamOut Ordinary)
                       (TypeSpec ["wybe"] "bool" []) True]]
                else []
    let params = procProtoParams $ procProto proc
    (body',newProcs) <- unbranchBody params (setup++body)
    let proto = procProto proc
    let proto' = if procDetism proc == SemiDet
                 then proto {procProtoParams =
                                 procProtoParams proto ++
                                 [Param "$$" (TypeSpec ["wybe"] "bool" [])
                                  ParamOut Ordinary]}
                 else proto
    let proc' = proc { procImpln = ProcDefSrc body', procProto = proto' }
    let tmpCount = procTmpCount proc
    mapM_ (addProc tmpCount) newProcs
    logMsg Unbranch $ "** Unbranched defn:" ++ showProcDef 0 proc' ++ "\n"
    return proc'


unbranchBody :: [Param] -> [Placed Stmt] -> Compiler ([Placed Stmt],[Item])
unbranchBody params stmts = do
    let unbrancher = initUnbrancherState params
    let outparams =  brOutParams unbrancher
    let outvars = brOutArgs unbrancher
    logMsg Unbranch $ "** Unbranching with output params:" ++ show outparams
    logMsg Unbranch $ "** Unbranching with output args:" ++ show outvars
    (stmts',st) <- runStateT (unbranchStmts stmts) unbrancher
                   
    return (stmts',brNewDefs st)


----------------------------------------------------------------
--                  Handling the Unbrancher monad
----------------------------------------------------------------

-- |The Unbrancher monad is a state transformer monad carrying the 
--  unbrancher state over the compiler monad.
type Unbrancher = StateT UnbrancherState Compiler

type VarDict = Map VarName TypeSpec


data UnbrancherState = Unbrancher {
    brLoopInfo   :: LoopInfo,     -- ^If in a loop, the break and continue stmts
    brVars       :: VarDict,      -- ^Variables defined up to here
    brDryRun     :: Bool,         -- ^Whether to suppress code generation
    brOutParams  :: [Param],      -- ^Output arguments for generated procs
    brOutArgs    :: [Placed Exp], -- ^Output arguments for generated procs
    brNewDefs    :: [Item]        -- ^Generated auxilliary procedures
    }


data LoopInfo = LoopInfo {
    loopExitVars :: Maybe VarDict, -- ^Variables available at all breaks seen,
                                  --  or Nothing if no breaks seen yet
    loopTerminated :: Bool,       -- ^Whether code so far included a Break or
                                  --  Next, which terminate execution
    loopNext :: Placed Stmt,      -- ^Call to make for a Next
    loopBreak :: Placed Stmt,     -- ^Call to make for a Break
    loopInit :: [Placed Stmt],    -- ^code to initialise before entering loop
    loopTerm :: [Placed Stmt]}    -- ^code to wrap up after leaving loop
                                  --  currently loopInit, loopTerm are unused
    | NoLoop
    deriving (Eq)


initUnbrancherState :: [Param] -> UnbrancherState
initUnbrancherState params =
    let defined = inputParams params
        outParams = [Param nm ty ParamOut Ordinary
                    | Param nm ty fl _ <- params
                    , flowsOut fl]
        outArgs   = [Unplaced $ Typed (Var nm ParamOut Ordinary) ty False
                    | Param nm ty fl _ <- params
                    , flowsOut fl]
    in Unbrancher NoLoop defined False outParams outArgs []


-- |Start unbranching a loop, returing the previous loop info
startLoop :: Unbrancher LoopInfo
startLoop = do
    old <- gets brLoopInfo
    let noStmt = Unplaced Nop
    modify (\s -> s { brLoopInfo = LoopInfo Nothing False noStmt noStmt [] [] })
    return old


-- |Complete unbranching a loop by restoring the previous loop info
endLoop :: LoopInfo -> Unbrancher ()
endLoop old = modify (\s -> s { brLoopInfo = old })


setDryRun :: Bool -> Unbrancher Bool
setDryRun newDryRun = do
    old <- gets brDryRun
    modify (\s -> s { brDryRun = newDryRun })
    return old

isDryRun :: Unbrancher Bool
isDryRun = gets brDryRun


ifTerminated :: Unbrancher a -> Unbrancher a -> Unbrancher a
ifTerminated thn els = do
    terminated <- isTerminated
    if terminated then thn else els


isTerminated :: Unbrancher Bool
isTerminated  = do
    lp <- gets brLoopInfo
    case lp of
        LoopInfo _ terminated _ _ _ _ -> return terminated
        _ -> return False


resetTerminated :: Bool -> Unbrancher ()
resetTerminated terminated = do
    lp <- gets brLoopInfo
    if lp /= NoLoop
       then modify (\s -> s { brLoopInfo = lp { loopTerminated = terminated }})
        else if terminated
             then shouldnt "Next or Break outside a loop"
             else return ()


-- | Set the Break and Next proc calls in the monad
setBreakNext :: Placed Stmt -> Placed Stmt -> Unbrancher ()
setBreakNext brk nxt = do
    lp <- gets brLoopInfo
    logUnbranch $ "Setting break = " ++ showStmt 4 (content brk)
    logUnbranch $ "Setting next  = " ++ showStmt 4 (content nxt)
    if lp == NoLoop
        then shouldnt "inside/outside loop status confused"
        else modify (\s -> s { brLoopInfo =
                               lp { loopBreak = brk, loopNext = nxt }})


-- |Record the current set of defined vars as one of the possible sets of
--  defined vars at a loop break
recordBreakVars :: Unbrancher ()
recordBreakVars = do
    vars <- gets brVars
    logUnbranch $ "Recording loop exit vars " ++ show vars
    eVars <- gets (loopExitVars . brLoopInfo)
    let eVars'' = case eVars of
            Nothing     -> Just vars
            Just eVars' -> Just $ Map.intersection eVars' vars
    logUnbranch $ "New loop exit vars " ++ show eVars''
    modify (\s -> s { brLoopInfo = (brLoopInfo s) { loopExitVars = eVars'' }})


-- | Add the specified variable to the symbol table
defVar :: VarName -> TypeSpec -> Unbrancher ()
defVar var ty =
    modify (\s -> s { brVars = Map.insert var ty $ brVars s })


-- | if the Exp is a variable, add it to the symbol table
defIfVar :: TypeSpec -> Exp -> Unbrancher ()
defIfVar _ (Typed exp ty _) = defIfVar ty exp
defIfVar defaultType (Var name _ _) = defVar name defaultType
defIfVar _ _ = return ()


setVars :: VarDict -> Unbrancher ()
setVars vs =
    modify (\s -> s { brVars = vs })


newProcName :: Unbrancher String
newProcName = do
    lift genProcName


genProc :: ProcProto -> [Placed Stmt] -> Unbrancher ()
genProc proto stmts = do
    let item = ProcDecl Private Det False proto stmts Nothing
    logUnbranch $ "Generating proc:\n" ++ show item
    modify (\s -> s { brNewDefs = item:brNewDefs s })


-- |Log a message, if we are logging unbrancher activity.
logUnbranch :: String -> Unbrancher ()
logUnbranch s = lift $ logMsg Unbranch s


----------------------------------------------------------------
--                 Unbranching statement sequences
----------------------------------------------------------------

-- | 'Unbranch' a list of statements.  If the boolean argument is true,
--   this is a "dry run", and should not generate any code, but only
--   work out which variables are defined when.
unbranchStmts :: [Placed Stmt] -> Unbrancher [Placed Stmt]
unbranchStmts [] = return []
unbranchStmts (stmt:stmts) = do
    vars <- gets brVars
    dryrun <- isDryRun
    logUnbranch $ "unbranching stmt"
        ++ (if dryrun then " (dryrun)" else " (really)")
        ++ "\n    " ++ showStmt 4 (content stmt)
        ++ "\n  with vars " ++ show vars
    ifTerminated (do logUnbranch "terminated!" ; return [])
        (unbranchStmt (content stmt) (place stmt) stmts)


-- | 'Unbranch' a single statement, along with all the following statements.
--   This transforms loops into calls to freshly generated procedures that
--   implement not only the loops themselves, but all following code. That
--   is, rather than returning at the loop exit(s), the generated procs
--   call procs for the code following the loops. Similarly, conditionals
--   are transformed by generating a separate proc for the code following
--   the conditional and adding a call to this proc at the end of each arm
--   of the conditional in place of the code following the conditional, so
--   that conditionals are always the final statement in a statement
--   sequence, as are calls to loop procs.
--
--   The input arguments to these generated procs are all the variables in
--   scope everywhere the proc is called. The proc generated for the code
--   after a conditional is called only from the end of each branch, so the
--   set of input arguments is just the intersection of the sets of
--   variables defined at the end of each branch. Also note that the only
--   variable defined by the condition of a conditional that can be used in
--   the 'else' branch is the condition variable itself. The condition may
--   be permitted to bind other variables, but in the 'else' branch the
--   condition is considered to have failed, so the other variables cannot
--   be used.
--
--   The variables in scope at the start of a loop are the ones in scope at
--   *every* call to the generated proc. Since variables defined before the
--   loop can be redefined in the loop but cannot become "lost", this means
--   the intersecion of the variables available at all calls is just the
--   set of variables defined at the start of the loop.  The inputs to the
--   proc generated for the code following a loop is the set of variables
--   defined at every 'break' in the loop.
--
--   Because these generated procs always chain to the next proc, they don't
--   need to return any values not returned by the proc they are generated
--   for, so the output arguments for all of them are just the output
--   arguments for the proc they are generated for.
--
--   Because later compiler passes will inline simple procs and remove dead
--   code and unneeded input and output arguments, we don't bother to try
--   to optimise these things here.
--
unbranchStmt :: Stmt -> OptPos -> [Placed Stmt] -> Unbrancher [Placed Stmt]
unbranchStmt stmt@(ProcCall _ _ _ args) pos stmts = do
    logUnbranch $ "Unbranching call " ++ showStmt 4 stmt
    defArgs args
    stmts' <- unbranchStmts stmts
    return $ (maybePlace stmt pos):stmts'
unbranchStmt stmt@(ForeignCall _ _ _ args) pos stmts = do
    logUnbranch $ "Unbranching foreign call " ++ showStmt 4 stmt
    defArgs args
    stmts' <- unbranchStmts stmts
    return $ (maybePlace stmt pos):stmts'
unbranchStmt (Test tstStmts tstVar) pos stmts = do
    logUnbranch "Unbranching a test statement"
    beforeVars <- gets brVars
    logUnbranch $ "test (" ++ show tstVar ++ "): " ++ showBody 8 tstStmts
    logUnbranch $ "Vars before test: " ++ show beforeVars
    tstStmts' <- unbranchStmts $ tstStmts ++
        [Unplaced
         $ ForeignCall "llvm" "move" []
         [tstVar,
          Unplaced $ Typed (Var "$$" ParamOut Ordinary)
          (TypeSpec ["wybe"] "bool" []) True]]
    afterVars <- gets brVars
    stmts' <- unbranchStmts stmts
    let tstVar' = Unplaced $ Var "$$" ParamIn Ordinary
    let genStmt = Cond tstStmts' tstVar' stmts' []
    logUnbranch $ "Conditional unbranched to " ++ showStmt 4 genStmt 
    return [maybePlace genStmt pos]
unbranchStmt (Cond tstStmts tstVar thn els) pos stmts = do
    logUnbranch "Unbranching a conditional"
    beforeVars <- gets brVars
    logUnbranch $ "test (" ++ show tstVar ++ "): " ++ showBody 8 tstStmts
    logUnbranch $ "Vars before test: " ++ show beforeVars
    tstStmts' <- unbranchStmts tstStmts
    beforeThenVars <- gets brVars
    logUnbranch $ "Unbranching then branch with vars: " ++ show beforeThenVars
    (thn',thnVars,thnTerm) <- unbranchBranch thn
    logUnbranch $ "Unbranched then is: " ++ showBody 4 thn'
    -- Vars assigned in the condition cannot be used in the else branch
    setVars beforeVars
    -- but the branch variable itself _can_ be used in the else branch
    defIfVar (TypeSpec ["wybe"] "bool" []) $ content tstVar
    resetTerminated False
    beforeElseVars <- gets brVars
    logUnbranch $ "Unbranching else branch with vars: " ++ show beforeElseVars
    (els',elsVars,elsTerm) <- unbranchBranch els
    logUnbranch $ "Unbranched else is: " ++ showBody 4 els'
    let afterVars = varsAfterITE thnVars thnTerm elsVars elsTerm
    logUnbranch $ "Vars after conditional: " ++ show afterVars
    resetTerminated $ thnTerm && elsTerm
    setVars afterVars
    stmts' <- unbranchStmts stmts
    contName <- newProcName
    dryrun <- isDryRun
    if dryrun
        then return []
        else do
            cont <- factorFreshProc contName afterVars Nothing stmts'
            let thn'' = if thnTerm then thn' else thn' ++ [cont]
            let els'' = if elsTerm then els' else els' ++ [cont]
            let genStmt = Cond tstStmts' tstVar thn'' els''
            logUnbranch $ "Conditional unbranched to " ++ showStmt 4 genStmt 
            return [maybePlace genStmt pos]
unbranchStmt (Loop body) pos stmts = do
    logUnbranch "Unbranching a loop"
    prevState <- startLoop
    logUnbranch $ "Handling loop:" ++ showBody 4 body
    beforeVars <- gets brVars
    logUnbranch $ "Vars before loop: " ++ show beforeVars
    loopName <- newProcName
    dryrun <- setDryRun True
    unbranchStmts $ body ++ [Unplaced Next]
    resetTerminated False
    setDryRun dryrun
    exitVars <- gets (fromMaybe Map.empty . loopExitVars . brLoopInfo)
    logUnbranch $ "loop exit vars from dryrun: " ++ show exitVars
    setVars exitVars
    stmts' <- unbranchStmts stmts
    logUnbranch $ "Next inputs: " ++ show beforeVars
    next <- newProcCall loopName beforeVars pos
    logUnbranch $ "Generated next " ++ showStmt 4 (content next)
    if dryrun
        then return ()
        else do
            breakName <- newProcName
            logUnbranch $ "Break inputs: " ++ show exitVars
            brk <- factorFreshProc breakName exitVars Nothing stmts'
            logUnbranch $ "Generated break " ++ showStmt 4 (content brk)
            setBreakNext brk next
            setVars beforeVars
            body' <- unbranchStmts $ body ++ [Unplaced Next]
            factorFreshProc loopName beforeVars pos body'
            logUnbranch $ "Finished handling loop"
    endLoop prevState
    return [next]
unbranchStmt (For _ _) _ _ =
    shouldnt "flattening should have removed For statements"
unbranchStmt (Nop) _ stmts = do
    logUnbranch "Unbranching a Nop"
    unbranchStmts stmts         -- might as well filter out Nops
unbranchStmt (Break) _ _ = do
    logUnbranch "Unbranching a Break"
    resetTerminated True
    recordBreakVars
    brk <- gets (loopBreak . brLoopInfo)
    logUnbranch $ "Current break proc = " ++ showStmt 4 (content brk)
    return [brk]
unbranchStmt (Next) _ _ = do
    logUnbranch "Unbranching a Next"
    resetTerminated True
    nxt <- gets (loopNext . brLoopInfo)
    logUnbranch $ "Current next proc = " ++ showStmt 4 (content nxt)
    return [nxt]


unbranchBranch :: [Placed Stmt] -> Unbrancher ([Placed Stmt],VarDict,Bool)
unbranchBranch branch = do
    branch' <- unbranchStmts branch
    branchVars <- gets brVars
    logUnbranch $ "Vars after then/else branch: " ++ show branchVars
    branchTerm <- isTerminated
    logUnbranch $
      "Then/else branch is" ++ (if branchTerm then "" else " NOT")
          ++ " terminal"
    return (branch', branchVars,branchTerm)


varsAfterITE :: VarDict -> Bool -> VarDict -> Bool -> VarDict
varsAfterITE thnVars True elsVars True   = Map.empty
varsAfterITE thnVars True elsVars False  = thnVars
varsAfterITE thnVars False elsVars True  = elsVars
varsAfterITE thnVars False elsVars False = Map.intersection thnVars elsVars


-- |A symbol table containing all input parameters
inputParams :: [Param] -> VarDict
inputParams params =
    List.foldr 
    (\(Param v ty dir _) vdict -> 
         if flowsIn dir then Map.insert v ty vdict else vdict)
    Map.empty params    


-- |Add all output arguments of a param list to the symbol table
defArgs :: [Placed Exp] -> Unbrancher ()
defArgs = mapM_ (defArg . content)


-- |Add the output variables defined by the expression to the symbol
--  table. Since the expression is already flattened, it will only be a
--  constant, in which case it doesn't define any variables, or a variable,
--  in which case it might.
defArg :: Exp -> Unbrancher ()
defArg = ifIsVarDef defVar (return ())


-- |Apply the function if the expression as a variable assignment,
--  otherwise just take the second argument.
ifIsVarDef :: (VarName -> TypeSpec -> t) -> t -> Exp -> t
ifIsVarDef f v expr = ifIsVarDef' f v expr Unspecified

ifIsVarDef' :: (VarName -> TypeSpec -> t) -> t -> Exp -> TypeSpec -> t
ifIsVarDef' f v (Typed expr ty _) _ = ifIsVarDef' f v expr ty
ifIsVarDef' f v (Var name dir _) ty =
    if flowsOut dir then f name ty else v
ifIsVarDef' _ v _ _ = v


outputVars :: VarDict -> [Placed Exp] -> VarDict
outputVars = 
    List.foldr ((ifIsVarDef Map.insert id)  . content)


-- |Generate a fresh proc with all the vars in the supplied dictionary
--  as inputs, and all the output params of the proc we're unbranching as
--  outputs.  Then return a call to this proc with the same inputs and outputs.
factorFreshProc :: ProcName -> (VarDict) -> OptPos -> [Placed Stmt]
                -> Unbrancher (Placed Stmt)
factorFreshProc pname inVars pos body = do
    proto <- newProcProto pname inVars
    genProc proto body
    newProcCall pname inVars pos


varExp :: FlowDirection -> VarName -> TypeSpec -> Placed Exp
varExp flow var ty = Unplaced $ Typed (Var var flow Ordinary) ty False


newProcCall :: ProcName -> VarDict -> OptPos -> Unbrancher (Placed Stmt)
newProcCall name inVars pos = do
    let inArgs  = List.map (uncurry $ varExp ParamIn) $ Map.toList inVars
    outArgs <- gets brOutArgs
    currMod <- lift getModuleSpec
    return $ maybePlace (ProcCall currMod name (Just 0) (inArgs ++ outArgs)) pos


newProcProto :: ProcName -> VarDict -> Unbrancher ProcProto
newProcProto name inVars = do
    let inParams  = [Param v ty ParamIn Ordinary
                    | (v,ty) <- Map.toList inVars]
    outParams <- gets brOutParams
    return $ ProcProto name (inParams ++ outParams) []



-- -- Given the specified environment and a statement sequence, returns the
-- -- environment following the statements and the loop exit environment.
-- -- The loop exit environment is Just the intersection of the environments
-- -- at all the breaks in the scope of the loop, or Nothing if there are no
-- -- such breaks.
-- loopExitVars :: VarDict -> [Placed Stmt] -> (VarDict, Maybe VarDict)
-- loopExitVars vars pstmts =
--   List.foldl stmtExitVars (vars,Nothing) $ List.map content pstmts
-- 
-- 
-- stmtExitVars :: (VarDict, Maybe VarDict) -> Stmt -> (VarDict, Maybe VarDict)
-- stmtExitVars  (vars,exits) (ProcCall _ _ _ args) =
--     (outputVars vars args, exits)
-- stmtExitVars (vars,exits) (ForeignCall _ _ _ args) =
--     (outputVars vars args, exits)
-- stmtExitVars (vars,_) (Cond tstStmts _ thn els) =
--     let (tstVars,tstExit) = loopExitVars vars tstStmts
--         (thnVars,thnExit) = loopExitVars tstVars thn
--         (elsVars,elsExit) = loopExitVars tstVars els
--     in  (Map.intersection thnVars elsVars, intersectExit thnExit elsExit)
-- stmtExitVars (vars,exits) (Loop body) =
--     let (bodyVars,bodyExit) = loopExitVars vars body
--     in  case bodyExit of 
--       Nothing -> (Map.empty, exits)
--       Just exits' -> (exits', exits)
-- stmtExitVars (vars,exits)  (Nop) = (vars,exits)
-- stmtExitVars _ (For _ _) =
--     shouldnt "flattening should have removed For statements"
-- stmtExitVars (vars,exits)  (Break) = 
--   (Map.empty, intersectExit (Just vars) exits)
-- stmtExitVars (vars,exits) (Next) = (Map.empty, exits)
-- 
-- 
-- intersectExit (Just v1) (Just v2) = Just $ Map.intersection v1 v2
-- intersectExit Nothing x = x
-- intersectExit x Nothing = x
