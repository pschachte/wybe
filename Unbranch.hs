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

module Unbranch (unbranchProc) where

import AST
import Snippets
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.List as List
import Data.Set as Set
import Data.Map as Map
import Data.Maybe
import Options (LogSelection(Unbranch))


-- |Transform away all loops, and all conditionals other than as the
--  final statement in their block.  Transform all semidet code into
--  conditional code that ends with a TestBool.  Transform away all
--  conjunctions, disjunctions, and negations.  After this, all bodies
--  comprise a sequence of ProcCall, ForeignCall, TestBool, Cond, and
--  Nop statements.  Furthermore,  Cond statements can only be the final
--  Stmt in a body, the condition of a Cond can only be a single TestBool
--  statement, and TestBool statements can only appear as the
--  condition of a Cond, or, in the case of a SemiDet proc, as the final
--  statement of a proc body.  Every SemiDet proc body must end with a
--  TestBool.

unbranchProc :: ProcDef -> Compiler ProcDef
unbranchProc proc = do
    logMsg Unbranch $ "** Unbranching proc " ++ procName proc
    let ProcDefSrc body = procImpln proc
    let detism = procDetism proc
    let tmpCtr = procTmpCount proc
    let params = procProtoParams $ procProto proc
    (body',tmpCtr',newProcs) <- unbranchBody tmpCtr params detism body
    let proto = procProto proc
    let proc' = proc { procTmpCount = tmpCtr', procImpln = ProcDefSrc body' }
    let tmpCount = procTmpCount proc
    mapM_ addProcDef newProcs
    logMsg Unbranch $ "** Unbranched defn:" ++ showProcDef 0 proc' ++ "\n"
    logMsg Unbranch "================================================\n"
    return proc'


-- |Eliminate loops and ensure that Conds only appear as the final
--  statement of a body.
unbranchBody :: Int -> [Param] -> Determinism -> [Placed Stmt]
             -> Compiler ([Placed Stmt],Int,[ProcDef])
unbranchBody tmpCtr params detism body = do
    let unbrancher = initUnbrancherState tmpCtr params
    let outparams =  brOutParams unbrancher
    let outvars = brOutArgs unbrancher
    let stmts = body
    logMsg Unbranch $ "** Unbranching with output params:" ++ show outparams
    logMsg Unbranch $ "** Unbranching with output args:" ++ show outvars
    (stmts',st) <- runStateT (unbranchStmts detism stmts) unbrancher
    return (stmts',brTempCtr st, brNewDefs st)


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
    brTempCtr    :: Int,          -- ^Number of next temp variable to make 
    brDryRun     :: Bool,         -- ^Whether to suppress code generation
    brOutParams  :: [Param],      -- ^Output arguments for generated procs
    brOutArgs    :: [Placed Exp], -- ^Output arguments for call to gen procs
    brNewDefs    :: [ProcDef]        -- ^Generated auxilliary procedures
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


initUnbrancherState :: Int -> [Param] -> UnbrancherState
initUnbrancherState tmpCtr params =
    let defined = inputParams params
        outParams = [Param nm ty ParamOut Ordinary
                    | Param nm ty fl _ <- params
                    , flowsOut fl]
        outArgs   = [Unplaced $ Typed (varSet nm) ty False
                    | Param nm ty fl _ <- params
                    , flowsOut fl]
    in Unbrancher NoLoop defined tmpCtr False outParams outArgs []


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
    -- let item = ProcDecl Private Det False proto stmts Nothing
    let name = procProtoName proto
    tmpCtr <- gets brTempCtr
    let procDef = ProcDef name proto (ProcDefSrc stmts) Nothing tmpCtr
                  Map.empty Private Det False NoSuperproc
    procDef' <- lift $ unbranchProc procDef
    logUnbranch $ "Generating proc:\n" ++ showProcDef 4 procDef'
    modify (\s -> s { brNewDefs = procDef':brNewDefs s })


-- |Return a fresh variable name.
tempVar :: Unbrancher VarName
tempVar = do
    ctr <- gets brTempCtr
    modify (\s -> s { brTempCtr = ctr + 1 })
    return $ mkTempName ctr


-- |Log a message, if we are logging unbrancher activity.
logUnbranch :: String -> Unbrancher ()
logUnbranch s = lift $ logMsg Unbranch s


----------------------------------------------------------------
--                 Unbranching statement sequences
----------------------------------------------------------------

-- | 'Unbranch' a list of statements.  If isDryRun is true,
--   this is a "dry run", and should not generate any code, but only
--   work out which variables are defined when.
unbranchStmts :: Determinism -> [Placed Stmt] -> Unbrancher [Placed Stmt]
unbranchStmts _ [] = return []
unbranchStmts detism (stmt:stmts) = do
    vars <- gets brVars
    dryrun <- isDryRun
    logUnbranch $ "unbranching stmt"
        ++ (if dryrun then " (dryrun)" else " (really)")
        ++ "\n    " ++ showStmt 4 (content stmt)
        ++ "\n  (" ++ show detism ++ ") with vars " ++ show vars
    ifTerminated (do logUnbranch "terminated!" ; return [])
        (unbranchStmt detism (content stmt) (place stmt) stmts)


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
--   The input arguments to generated procs are all the variables in
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
--   the intersection of the variables available at all calls is just the
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
unbranchStmt :: Determinism -> Stmt -> OptPos -> [Placed Stmt]
             -> Unbrancher [Placed Stmt]
unbranchStmt detism stmt@(ProcCall _ _ _ Det args) pos stmts = do
    logUnbranch $ "Unbranching call " ++ showStmt 4 stmt
    defArgs args
    leaveStmtAsIs stmt pos detism stmts
unbranchStmt Det stmt@(ProcCall md name procID SemiDet args) pos stmts =
    shouldnt $ "Semidet proc call " ++ show stmt ++ " in a Det context"
unbranchStmt SemiDet stmt@(ProcCall md name procID SemiDet args) pos [] = do
    logUnbranch $ "converting SemiDet proc call" ++ show stmt
    testVarName <- tempVar
    let result = [maybePlace (ProcCall md name procID Det
                         $ args ++ [Unplaced (boolVarSet testVarName)]) pos,
                 maybePlace (TestBool $ varGet testVarName) pos]
    logUnbranch $ "#Converted SemiDet proc call" ++ show stmt
    logUnbranch $ "#To: " ++ showBody 4 result
    return result
unbranchStmt SemiDet stmt@(ProcCall md name procID SemiDet args) pos stmts = do
    logUnbranch $ "converting SemiDet proc call" ++ show stmt
    testVarName <- tempVar
    let testStmt = TestBool $ varGet testVarName
    stmts' <- unbranchStmt SemiDet (Cond (maybePlace testStmt pos)
                                    stmts [failTest]) pos []
    let result = (maybePlace (ProcCall md name procID Det
                         $ args ++ [Unplaced (boolVarSet testVarName)]) pos
                 : stmts')
    logUnbranch $ "#Converted SemiDet proc call" ++ show stmt
    logUnbranch $ "#To: " ++ showBody 4 result
    return result
unbranchStmt detism stmt@(ForeignCall _ _ _ args) pos stmts = do
    logUnbranch $ "Unbranching foreign call " ++ showStmt 4 stmt
    defArgs args
    leaveStmtAsIs stmt pos detism stmts
unbranchStmt Det (TestBool expr) _ _ =
    shouldnt $ "TestBool " ++ show expr ++ " in a Det context"
unbranchStmt SemiDet stmt@(TestBool _) pos [] = do
    logUnbranch $ "Unbranching a final primitive test " ++ show stmt
    return [maybePlace stmt pos]
unbranchStmt SemiDet stmt@(TestBool _) pos stmts@(_:_) = do
    logUnbranch $ "Unbranching a non-final primitive test " ++ show stmt
    stmts' <- unbranchStmts SemiDet stmts
    let result = [Unplaced $ Cond (maybePlace stmt pos) stmts' [failTest]]
    logUnbranch $ "#Unbranched non-final primitive test " ++ show stmt
    logUnbranch $ "#To: " ++ showBody 4 result
    return result
unbranchStmt Det stmt@(And _) _ _ =
    shouldnt $ "Conjunction in a Det context: " ++ show stmt
unbranchStmt SemiDet (And []) pos stmts =
    unbranchStmt SemiDet (content succeedTest) pos stmts
unbranchStmt SemiDet (And [stmt]) pos stmts =
    unbranchStmts SemiDet (stmt:stmts)
unbranchStmt SemiDet (And (conj:conjs)) pos stmts = do
    logUnbranch "Unbranching conjunction"
    unbranchStmt SemiDet (Cond conj [Unplaced $ And conjs] [failTest]) pos stmts
unbranchStmt Det stmt@(Or _) _ _ =
    shouldnt $ "Disjunction in a Det context: " ++ show stmt
unbranchStmt SemiDet (Or []) pos stmts =
    unbranchStmt SemiDet (content failTest) pos stmts
unbranchStmt SemiDet (Or [stmt]) pos stmts =
    unbranchStmts SemiDet (stmt:stmts)
unbranchStmt SemiDet (Or (disj:disjs)) pos stmts = do
    logUnbranch "Unbranching disjunction"
    unbranchStmt SemiDet (Cond disj [succeedTest] [Unplaced $ Or disjs])
                 pos stmts
unbranchStmt Det stmt@(Not _) _ _ =
    shouldnt $ "Negation in a Det context: " ++ show stmt
unbranchStmt SemiDet (Not tst) pos stmts = do
    -- XXX Really should be able to implement Not as a bitwise negation
    logUnbranch "Unbranching negation"
    unbranchStmt SemiDet (Cond tst [failTest] [succeedTest]) pos stmts
unbranchStmt detism (Cond tstStmt thn els) pos stmts =
    if detStmt $ content tstStmt
    -- XXX Should warn of Cond with Det test, but can't because we transform
    --     other code into Conds.
    then (tstStmt:) <$> unbranchStmts detism (thn ++ stmts)
    else unbranchCond detism tstStmt thn els pos stmts
unbranchStmt detism (Loop body) pos stmts = do
    logUnbranch "Unbranching a loop"
    prevState <- startLoop
    logUnbranch $ "Handling loop:" ++ showBody 4 body
    beforeVars <- gets brVars
    logUnbranch $ "Vars before loop: " ++ show beforeVars
    loopName <- newProcName
    dryrun <- setDryRun True
    unbranchStmts detism $ body ++ [Unplaced Next]
    resetTerminated False
    setDryRun dryrun
    exitVars <- gets (fromMaybe Map.empty . loopExitVars . brLoopInfo)
    logUnbranch $ "loop exit vars from dryrun: " ++ show exitVars
    setVars exitVars
    stmts' <- unbranchStmts detism stmts
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
            body' <- unbranchStmts detism $ body ++ [Unplaced Next]
            factorFreshProc loopName beforeVars pos body'
            logUnbranch $ "Finished handling loop"
    endLoop prevState
    return [next]
unbranchStmt detism (For _ _) _ _ =
    shouldnt "flattening should have removed For statements"
unbranchStmt detism Nop _ stmts = do
    logUnbranch "Unbranching a Nop"
    unbranchStmts detism stmts         -- might as well filter out Nops
unbranchStmt _ Break _ _ = do
    logUnbranch "Unbranching a Break"
    resetTerminated True
    recordBreakVars
    brk <- gets (loopBreak . brLoopInfo)
    logUnbranch $ "Current break proc = " ++ showStmt 4 (content brk)
    return [brk]
unbranchStmt _ Next _ _ = do
    logUnbranch "Unbranching a Next"
    resetTerminated True
    nxt <- gets (loopNext . brLoopInfo)
    logUnbranch $ "Current next proc = " ++ showStmt 4 (content nxt)
    return [nxt]


-- |Emit the supplied statement, and process the remaining statements.
leaveStmtAsIs :: Stmt -> OptPos -> Determinism -> [Placed Stmt]
              -> Unbrancher [Placed Stmt]
leaveStmtAsIs stmt pos detism stmts = do
    stmts' <- unbranchStmts detism stmts
    return $ maybePlace stmt pos:stmts'


unbranchCond :: Determinism -> Placed Stmt -> [Placed Stmt] -> [Placed Stmt]
             -> OptPos -> [Placed Stmt] -> Unbrancher [Placed Stmt]
unbranchCond detism tstStmt thn els pos stmts = do
    logUnbranch "Unbranching a conditional:"
    logUnbranch $ showStmt 8 $ content tstStmt
    beforeVars <- gets brVars
    logUnbranch $ "Vars before test: " ++ show beforeVars
    tstStmt' <- unbranchStmt SemiDet (content tstStmt) (place tstStmt) []
    logUnbranch "Unbranched condition:"
    logUnbranch $ showBody 8 tstStmt'
    beforeThenVars <- gets brVars
    logUnbranch $ "Unbranching then branch with vars: " ++ show beforeThenVars
    (thn',thnVars,thnTerm) <- unbranchBranch detism thn
    logUnbranch $ "Unbranched then is: " ++ showBody 4 thn'
    -- Vars assigned in the condition cannot be used in the else branch
    setVars beforeVars
    -- but the branch variable itself _can_ be used in the else branch
    resetTerminated False
    beforeElseVars <- gets brVars
    logUnbranch $ "Unbranching else branch with vars: " ++ show beforeElseVars
    (els',elsVars,elsTerm) <- unbranchBranch detism els
    logUnbranch $ "Unbranched else is: " ++ showBody 4 els'
    let afterVars = varsAfterITE thnVars thnTerm elsVars elsTerm
    logUnbranch $ "Vars after conditional: " ++ show afterVars
    resetTerminated $ thnTerm && elsTerm
    setVars afterVars
    stmts' <- unbranchStmts detism stmts
    dryrun <- isDryRun
    if dryrun
        then return []
        else do
            let repeats
                  | thnTerm && elsTerm = 0
                  | thnTerm || elsTerm = 1
                  | otherwise          = 2
            cont <- maybeFactorProc stmts' repeats afterVars
            let thn'' = if thnTerm then thn' else appendStmts thn' cont
            let els'' = if elsTerm then els' else appendStmts els' cont
            genStmt <- buildCond tstStmt' thn'' beforeThenVars
                                 els'' beforeElseVars pos
            logUnbranch $ "Conditional unbranched to " ++ showBody 4 genStmt
            return genStmt

-- | Build code equivalent to Cond tsts thn els at source position pos,
--   where tsts, thn, and els have already been unbranched, so they are
--   simplified.  That means it can only contain Det ProcCalls, ForeignCalls,
--   TestBools, and Conds whose conditions are single non-constant TestBools.
--   It must also return code that satisfies this same constraint.
buildCond :: [Placed Stmt] -> [Placed Stmt] -> VarDict
          -> [Placed Stmt] -> VarDict -> OptPos -> Unbrancher [Placed Stmt]
buildCond tsts thn thnVars els elsVars pos = do
    -- Work out how many calls to thn and els will be needed
    let repeats = countRepeats . content <$> tsts
    let thnCount = sum $ fst <$> repeats
    let elsCount = sum $ snd <$> repeats
    -- Generate fresh procs for the then and else branches if necessary
    thn' <- maybeFactorProc thn thnCount thnVars
    els' <- maybeFactorProc els elsCount elsVars
    buildCond' tsts thn' els' pos


buildCond' :: [Placed Stmt] -> [Placed Stmt] -> [Placed Stmt] -> OptPos
           -> Unbrancher [Placed Stmt]
buildCond' [] thn _els _pos = return thn
buildCond' (stmt:stmts) thn els pos =
    placedApply buildCond'' stmt stmts thn els pos


buildCond'' :: Stmt -> OptPos -> [Placed Stmt] -> [Placed Stmt] -> [Placed Stmt]
            -> OptPos -> Unbrancher [Placed Stmt]
buildCond'' stmt@(ProcCall _ _ _ Det _) pos stmts thn els condPos =
    (maybePlace stmt pos:) <$> buildCond' stmts thn els condPos
buildCond'' stmt@(ProcCall _ _ _ SemiDet _) pos stmts thn els condPos =
    shouldnt $ "Should have transformed SemiDet calls before buildCond "
               ++ show stmt
buildCond'' stmt@ForeignCall{} pos stmts thn els condPos =
    (maybePlace stmt pos:) <$> buildCond' stmts thn els condPos
buildCond'' stmt@(TestBool (Typed (IntValue 1) _ _)) pos stmts thn els condPos =
    buildCond' stmts thn els condPos
buildCond'' stmt@(TestBool (Typed (IntValue 0) _ _)) pos stmts thn els condPos =
    return els
buildCond'' stmt@TestBool{} pos stmts thn els condPos = do
    thn' <- buildCond' stmts thn els condPos
    return [maybePlace (Cond (maybePlace stmt pos) thn' els) condPos]
buildCond'' stmt@(Cond tst thn' els') pos stmts thn els condPos = do
    thn'' <- buildCond' thn' thn els condPos
    els'' <- buildCond' els' thn els condPos
    (maybePlace (Cond tst thn'' els'') pos:)
      <$> buildCond' stmts thn els condPos
buildCond'' stmt _ _ _ _ _ =
    shouldnt $ "Statement type should have been eliminated before buildCond'' "
               ++ show stmt

-- | Returns a pair of an upper bound on the number of times the then and
--   else branches of a conditional will be repeated, respectively, when
--   generating code for a Cond with the specified instruction as condition.
countRepeats :: Stmt -> (Int,Int)
countRepeats (TestBool (Typed (IntValue 1) _ _)) = (1,0)
countRepeats (TestBool (Typed (IntValue 0) _ _)) = (0,1)
countRepeats (TestBool _) = (1,1)
countRepeats (ProcCall _ _ _ Det _) = (0,0)
countRepeats ForeignCall{} = (0,0)
countRepeats (Cond stmt thn els) =
    let repeats = countRepeats . content <$> thn ++ els
    in (sum $ fst <$> repeats, sum $ snd <$> repeats)
countRepeats stmt =
  shouldnt $ "statement should have been removed before countRepeats: "
             ++ show stmt


maybeFactorProc :: [Placed Stmt] -> Int -> VarDict -> Unbrancher [Placed Stmt]
maybeFactorProc stmts repeats vars = do
    let expansion = (repeats - 1) * length stmts
    if expansion <= 4
      then return stmts
      else do
      newName <- newProcName
      (:[]) <$> factorFreshProc newName vars Nothing stmts



unbranchBranch :: Determinism -> [Placed Stmt]
               -> Unbrancher ([Placed Stmt],VarDict,Bool)
unbranchBranch detism branch = do
    branch' <- unbranchStmts detism branch
    branchVars <- gets brVars
    logUnbranch $ "Vars after then/else branch: " ++ show branchVars
    branchTerm <- isTerminated
    logUnbranch $
      "Then/else branch is" ++ (if branchTerm then "" else " NOT")
          ++ " terminal"
    return (branch', branchVars,branchTerm)


-- | Add the back statements at the end of the front.  Ensure we maintain
--   the invariant that only the final statement is allowed to be a Cond.
appendStmts :: [Placed Stmt] -> [Placed Stmt] -> [Placed Stmt]
appendStmts front [] = front
appendStmts [] back = back
appendStmts front back =
    case content $ last front of
      Cond tst thn els ->
        init front
        ++ [Unplaced
            $ Cond tst (appendStmts thn back) (appendStmts els back)]
      _ -> front ++ back


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


-- |Apply the function if the expression is a variable assignment,
--  otherwise just take the second argument.
ifIsVarDef :: (VarName -> TypeSpec -> t) -> t -> Exp -> t
ifIsVarDef f v expr = ifIsVarDef' f v expr AnyType

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
    return $ maybePlace (ProcCall currMod name (Just 0) Det
                         (inArgs ++ outArgs)) pos


newProcProto :: ProcName -> VarDict -> Unbrancher ProcProto
newProcProto name inVars = do
    let inParams  = [Param v ty ParamIn Ordinary
                    | (v,ty) <- Map.toList inVars]
    outParams <- gets brOutParams
    return $ ProcProto name (inParams ++ outParams) Set.empty
