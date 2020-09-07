--  File     : Unbranch.hs
--  Author   : Peter Schachte
--  Purpose  : Turn loops and conditionals into separate procedures
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
-- BEGIN MAJOR DOC
--  This code transforms loops into fresh recursive procs, and ensures
--  that all conditionals are the last statements in their respective
--  bodies. Note that conditionals can be nested, but at the end of
--  the conditional, they must return to the caller. This is handled
--  by introducing a fresh continuation proc for any code that follows
--  the conditional. The reason for this transformation is that a
--  later pass will convert to a logic programming form which
--  implements conditionals with separate clauses, each of which
--  returns on completion.
--
--  Loops are a little more complicated.  do {a b} c d would be
--  transformed into next1, where next1 is defined as def next1 {a b
--  next1}, and break1 is defined as def break1 {c d}.  Then Next
--  and Break are handled so that they cancel all the following code
--  in their clause body.  For example, Next a b would be transformed
--  to just next1, where next1 is the next procedure for that loop.
--  Similarly Break a b would be transformed to just break1, where
--  break1 is the break procedure for that loop.  Inside a loop, a
--  conditional must be handled specially, to support breaking out of
--  the loop.  Inside a loop, if {a:: b | otherwise:: c} d e would be
--  transformed to a call to gen1, where gen2 is defined as def gen2
--  {d e}, and gen1 is defined as def gen1 {a:: b gen2 | otherwise::
--  c gen2}.  So for example do {a if {b:: Break} c} d e would be
--  transformed into next1, which is defined as def next1 {a gen1},
--  gen1 is defined as def gen1 {b:: break1 | otherwise:: gen2},
--  gen2 is defined as def gen2 {c next1}, and break1 is defined as def
--  break1 {d e}.
--
--  The tricky part of all this is handling the arguments to these
--  generated procedures.  For each generated procedure, the input
--  parameters must be a superset of the variables used in the body of
--  the procedure, and must be a subset of the variables defined prior
--  to the generated call.  Similarly, the output parameters must be a
--  a subset of the variables defined in the generated procedure, and
--  must be superset of the variables that will be used following the
--  generated call.  Ideally, we would make these the *smallest* sets
--  satifying these constraints, but later compiler passes remove
--- unnecessary parameters, so instead we go with the largest such
--  sets.  This is determined by the type/mode checker, which already
--  keeps track of variables known to be defined at each program point.
--
--  This code also eliminates other Wybe language features, such as
--  transforming SemiDet procs into Det procs with a Boolean output
--  param.  Following unbranching, code will be compiled to LPVM
--  form by the Clause module; this requires a much simplified input
--  AST form with the following requirements:
--    * All procs, and all proc calls, are Det.
--    * All statements but the last in a body are either ProcCalls
--      or ForeignCalls or Nops.
--    * The final statement in a body can be any of these same
--      statement types, or a Cond whose condition is a single
--      TestBool, and whose branches are bodies satisfying these
--      same conditions.
-- END MAJOR DOC
----------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

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
--  final statement in their block. Transform all semidet code into
--  conditional code that ends with a TestBool or a call to a semidet
--  proc. Transform all conjunctions, disjunctions, and
--  negations into conditionals. After this, all bodies comprise a sequence of ProcCall,
--  ForeignCall, TestBool, Cond, and Nop statements. Furthermore, Cond
--  statements can only be the final Stmt in a body, the condition of
--  a Cond can only be a single TestBool statement, and TestBool
--  statements can only appear as the condition of a Cond, or, in the
--  case of a SemiDet proc, as the final statement of a proc body.
--  Every SemiDet proc body must end with a TestBool, or a tail call
--  to a SemiDet proc, or a fork each of whose branches satisfies this
--  constraint.

unbranchProc :: ProcDef -> Compiler ProcDef
unbranchProc = unbranchProc' Nothing


unbranchProc' :: Maybe LoopInfo -> ProcDef -> Compiler ProcDef
unbranchProc' loopinfo proc = do
    logMsg Unbranch $ "** Unbranching proc " ++ procName proc ++ ":"
                      ++ showProcDef 0 proc ++ "\n"
    let ProcDefSrc body = procImpln proc
    let detism = procDetism proc
    let tmpCtr = procTmpCount proc
    let params = procProtoParams $ procProto proc
    let proto = procProto proc
    let params = procProtoParams proto
    let params' = (selectDetism id (++ [testOutParam]) detism) params
    let alt = selectDetism [] [move boolFalse testOutExp] detism
    let stmts = selectDetism body (body++[move boolTrue testOutExp]) detism
    let proto' = proto {procProtoParams = params'}
    (body',tmpCtr',newProcs) <-
        unbranchBody loopinfo tmpCtr params detism stmts alt
    let proc' = proc { procProto = proto'
                     , procDetism = Det
                     , procImpln = ProcDefSrc body'
                     , procTmpCount = tmpCtr'}
    logMsg Unbranch $ "** Unbranched defn:" ++ showProcDef 0 proc' ++ "\n"
    logMsg Unbranch "================================================\n"
    mapM_ addProcDef newProcs
    return proc'


-- |Eliminate loops and ensure that Conds only appear as the final
--  statement of a body.
unbranchBody :: Maybe LoopInfo -> Int -> [Param] -> Determinism
             -> [Placed Stmt] -> [Placed Stmt]
             -> Compiler ([Placed Stmt],Int,[ProcDef])
unbranchBody loopinfo tmpCtr params detism body alt = do
    let unbrancher = initUnbrancherState loopinfo tmpCtr params
    let outparams =  brOutParams unbrancher
    let outvars = brOutArgs unbrancher
    let stmts = body
    logMsg Unbranch $ "** Unbranching with output params:" ++ show outparams
    logMsg Unbranch $ "** Unbranching with output args:" ++ show outvars
    (stmts',st) <- runStateT (unbranchStmts detism stmts alt True) unbrancher
    return (stmts',brTempCtr st, brNewDefs st)


----------------------------------------------------------------
--                 Converting SemiDet procs to Det
----------------------------------------------------------------


-- |The name we give to the local variable holding the result of a
-- test (SemiDet) proc when we convert to a Det one.
testVarName :: Ident
testVarName = "$$"

-- |A synthetic output parameter carrying the test result
testOutParam :: Param
testOutParam = Param testVarName boolType ParamOut $ Implicit Nothing

-- |The output exp we use to hold the success/failure of a test proc.
testOutExp :: Exp
testOutExp = boolVarSet testVarName

-- -- |The input exp we use to hold the success/failure of a test proc.
-- testInExp :: Exp
-- testInExp = boolVarGet testVarName


----------------------------------------------------------------
--                  Handling the Unbrancher monad
----------------------------------------------------------------

-- |The Unbrancher monad is a state transformer monad carrying the
--  unbrancher state over the compiler monad.
type Unbrancher = StateT UnbrancherState Compiler

data UnbrancherState = Unbrancher {
    brLoopInfo   :: Maybe LoopInfo, -- ^If in a loop, break and continue stmts
    brVars       :: VarDict,      -- ^Types of variables defined up to here
    brTempCtr    :: Int,          -- ^Number of next temp variable to make
    brOutParams  :: [Param],      -- ^Output arguments for generated procs
    brOutArgs    :: [Placed Exp], -- ^Output arguments for call to gen procs
    brNewDefs    :: [ProcDef]     -- ^Generated unbranched auxilliary procedures
    }


data LoopInfo = LoopInfo {
    loopNext :: Placed Stmt,      -- ^Call to make for a Next
    loopBreak :: [Placed Stmt]    -- ^Code to execute for a Break
    } deriving (Eq)


initUnbrancherState :: Maybe LoopInfo -> Int -> [Param] -> UnbrancherState
initUnbrancherState loopinfo tmpCtr params =
    let defined = inputParams params
        outParams = [Param nm ty ParamOut Ordinary
                    | Param nm ty fl _ <- params
                    , flowsOut fl]
        outArgs   = [Unplaced $ Typed (varSet nm) ty False
                    | Param nm ty fl _ <- params
                    , flowsOut fl]
    in Unbrancher loopinfo defined tmpCtr outParams outArgs []


-- | Add the specified variable to the symbol table
defVar :: VarName -> TypeSpec -> Unbrancher ()
defVar var ty =
    modify (\s -> s { brVars = Map.insert var ty $ brVars s })


-- | if the Exp is a variable, add it to the symbol table
defIfVar :: TypeSpec -> Exp -> Unbrancher ()
defIfVar _ (Typed exp ty _) = defIfVar ty exp
defIfVar defaultType (Var name _ _) = defVar name defaultType
defIfVar _ _ = return ()


-- |Record the specified dictionary as the current dictionary.
setVars :: VarDict -> Unbrancher ()
setVars vs = modify (\s -> s { brVars = vs })


-- |Generate a fresh proc name that does not collide with any proc in the
-- current module.
newProcName :: Unbrancher String
newProcName = lift genProcName


-- |Create, unbranch, and record a new proc with the specified proto and body.
genProc :: Maybe LoopInfo -> ProcProto -> Determinism -> [Placed Stmt]
        -> Unbrancher ()
genProc loopinfo proto detism stmts = do
    let name = procProtoName proto
    tmpCtr <- gets brTempCtr
    let procDef = ProcDef name proto (ProcDefSrc stmts) Nothing tmpCtr
                  Map.empty Private detism False NoSuperproc
    logUnbranch $ "Unbranching fresh " ++ show detism ++ " proc:"
                  ++ showProcDef 8 procDef
    loopinfo' <- maybe (gets brLoopInfo) (return . Just) loopinfo
    procDef' <- lift $ unbranchProc' loopinfo' procDef
    logUnbranch $ "Unbranched generated " ++ show detism ++ " proc:"
                  ++ showProcDef 8 procDef
    modify (\s -> s { brNewDefs = procDef':brNewDefs s })


-- |Return a fresh variable name.
tempVar :: Unbrancher VarName
tempVar = do
    ctr <- gets brTempCtr
    modify (\s -> s { brTempCtr = ctr + 1 })
    return $ mkTempName ctr


-- |Log a message, if we are logging unbrancher activity.
logUnbranch :: String -> Unbrancher ()
logUnbranch s = do
    -- dryrun <- isDryRun
    lift $ logMsg Unbranch s
      -- $ (if dryrun then "dryrun: " else "actual: ") ++ s


-- |Return the current loop break statement(s)
getLoopBreak :: Unbrancher [Placed Stmt]
getLoopBreak = do
    inf <- gets brLoopInfo
    return $ maybe (shouldnt "break outside a loop") loopBreak inf


-- |Return the current loop continuation (next) statement
getLoopNext :: Unbrancher (Placed Stmt)
getLoopNext = do
    inf <- gets brLoopInfo
    return $ maybe (shouldnt "next outside a loop") loopNext inf


----------------------------------------------------------------
--                 Unbranching statement sequences
--
-- We handle unbranch sequences as conjunctions inside conditionals:  if
-- each statement succeeds, we carry on to the next, otherwise we execute
-- the alternative statement sequence.  The alternative sequence has
-- already been unbranched.  Any Det statement is guaranteed to
-- succeed, so we don't need a conditional for it.
----------------------------------------------------------------

-- | 'Unbranch' a list of statements
unbranchStmts :: Determinism -> [Placed Stmt] -> [Placed Stmt] -> Bool
              -> Unbrancher [Placed Stmt]
unbranchStmts detism [] _ sense = do
    logUnbranch $ "Unbranching an empty "
                  ++ selectDetism "Det" "SemiDet" detism
                  ++ " body"
    return []
unbranchStmts detism (stmt:stmts) alt sense = do
    vars <- gets brVars
    logUnbranch $ "unbranching (" ++ show detism ++ ") stmt"
        ++ "\n    " ++ showStmt 4 (content stmt)
        ++ "\n  with vars " ++ show vars
    placedApply (unbranchStmt detism) stmt stmts alt sense


-- | 'Unbranch' a single statement, given a list of following statements
--   and an already unbranched list of alternative statements. This also
--   considers the sense of the test: if True, execution should go to the
--   following statements on success and the alternative statements on
--   failure; if False, then vice-versa. The following statements are
--   represented as a pair of a list of statements that has not yet been
--   and a list of unbranched alternative statements. The alternative
--   statements will have been factored out into a call to a fresh
--   procedure if necessary (ie, if it will be used in more than one case,
--   it will be a short list).
--
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
unbranchStmt :: Determinism -> Stmt -> OptPos -> [Placed Stmt] -> [Placed Stmt]
             -> Bool -> Unbrancher [Placed Stmt]
unbranchStmt _ stmt@(ProcCall _ _ _ _ True args) _ _ _ _ =
    shouldnt $ "Resources should have been handled before unbranching: "
               ++ showStmt 4 stmt
unbranchStmt Det stmt@(ProcCall _ _ _ SemiDet _ _) _ _ _ _ =
    shouldnt $ "Semidet proc call " ++ show stmt ++ " in a Det context"
unbranchStmt SemiDet stmt@(ProcCall md name procID SemiDet _ args) pos
             stmts alt sense = do
    logUnbranch $ "converting SemiDet proc call" ++ show stmt
    testResultVar <- tempVar
    let args' = args ++ [Unplaced (boolVarSet testResultVar)]
    defArgs args'
    stmts' <- unbranchStmts SemiDet stmts alt sense
    let val = boolVarGet testResultVar
    vars <- gets brVars
    logUnbranch $ "mkCond " ++ show sense ++ " " ++ show val
                  ++ showBody 4 stmts' ++ "\nelse"
                  ++ showBody 4 alt
    let result = maybePlace (ProcCall md name procID Det False args') pos
                 : mkCond sense val pos stmts' alt vars
    logUnbranch $ "#Converted SemiDet proc call" ++ show stmt
    logUnbranch $ "#To: " ++ showBody 4 result
    return result
unbranchStmt detism stmt@(ProcCall _ _ _ Det _ args) pos stmts alt sense = do
    logUnbranch $ "Unbranching call " ++ showStmt 4 stmt
    defArgs args
    leaveStmtAsIs detism stmt pos stmts alt sense
unbranchStmt detism stmt@(ForeignCall _ _ _ args) pos stmts alt sense = do
    logUnbranch $ "Unbranching foreign call " ++ showStmt 4 stmt
    defArgs args
    leaveStmtAsIs detism stmt pos stmts alt sense
unbranchStmt detism stmt@(TestBool val) pos stmts alt sense = do
    ifSemiDet detism (showStmt 4 stmt ++ " in a Det context")
    $ do
      logUnbranch $ "Unbranching a non-final primitive test " ++ show stmt
      stmts' <- unbranchStmts SemiDet stmts alt sense
      vars <- gets brVars
      logUnbranch $ "mkCond " ++ show sense ++ " " ++ show val
                    ++ showBody 4 stmts' ++ "\nelse"
                    ++ showBody 4 alt
      let result = mkCond sense val Nothing stmts' alt vars
      logUnbranch $ "#Unbranched non-final primitive test " ++ show stmt
      logUnbranch $ "#To: " ++ showBody 4 result
      return result
unbranchStmt detism stmt@(And conj) pos stmts alt sense =
    ifSemiDet detism ("Conjunction in a Det context: " ++ show stmt)
    -- XXX might want to report if conj doesn't contain any tests
    $ unbranchStmts SemiDet (conj ++ stmts) alt sense
unbranchStmt detism stmt@(Or disjs) _ stmts alt sense = do
    ifSemiDet detism ("Disjunction in a Det context: " ++ show stmt)
    $ do
      -- XXX Need to also include variables defined in all disjuncts; should
      -- be determined in mode checker
      vars <- gets brVars
      stmts' <- maybeFactorContinuation SemiDet vars stmts alt sense
      unbranchStmts SemiDet disjs stmts' (not sense)
unbranchStmt detism stmt@(Not tst) pos stmts alt sense =
    ifSemiDet detism ("Negation in a Det context: " ++ show stmt)
    $ do
        logUnbranch "Unbranching negation"
        placedApply (unbranchStmt SemiDet) tst stmts alt (not sense)
unbranchStmt detism (Cond tstStmt thn els exitVars) pos stmts alt sense =
    if detStmt $ content tstStmt
    then (tstStmt:) <$> unbranchStmts detism (thn ++ stmts) alt sense
    else do
      let exitVars' = trustFromJust "unbranching Cond without exitVars" exitVars
      stmts' <- unbranchStmts detism stmts alt sense
      stmts'' <- maybeFactorContinuation detism exitVars' stmts' alt sense
      thn' <- unbranchStmts detism (thn ++ stmts'') alt sense
      els' <- unbranchStmts detism (els ++ stmts'') alt sense
      placedApply (unbranchStmt SemiDet) tstStmt thn' els' True
unbranchStmt detism (Loop body exitVars) pos stmts alt sense = do
    let exitVars' = trustFromJust "unbranching Loop without exitVars" exitVars
    logUnbranch $ "Handling loop:" ++ showBody 4 body
    beforeVars <- gets brVars
    logUnbranch $ "  with exit vars " ++ show exitVars'
    brk <- maybeFactorContinuation detism exitVars' stmts alt sense
    logUnbranch $ "Generated break: " ++ showBody 4 brk
    next <- factorLoopProc brk beforeVars pos detism body alt sense
    logUnbranch $ "Generated next " ++ showStmt 4 (content next)
    logUnbranch "Finished handling loop"
    return [next]
unbranchStmt _ (UseResources _ _) _ _ _ _ =
    shouldnt "resource handling should have removed use ... in statements"
-- unbranchStmt Det (For _ _) _ _ =
--     shouldnt "flattening should have removed For statements"
unbranchStmt detism Nop _ stmts alt sense = do
    logUnbranch "Unbranching a Nop"
    unbranchStmts detism stmts alt sense     -- might as well filter out Nops
unbranchStmt _ Break _ _ _ _ = do
    logUnbranch "Unbranching a Break"
    brk <- getLoopBreak
    logUnbranch $ "Current break = " ++ showBody 4 brk
    return brk
unbranchStmt _ Next _ _ _ _ = do
    logUnbranch "Unbranching a Next"
    nxt <- getLoopNext
    logUnbranch $ "Current next proc = " ++ showStmt 4 (content nxt)
    return [nxt]


-- |Emit the supplied statement, and process the remaining statements.
leaveStmtAsIs :: Determinism -> Stmt -> OptPos
              -> [Placed Stmt] -> [Placed Stmt] -> Bool
              -> Unbrancher [Placed Stmt]
leaveStmtAsIs detism stmt pos stmts alt sense = do
    logUnbranch $ "Leaving stmt as is: " ++ showStmt 4 stmt
    stmts' <- unbranchStmts detism stmts alt sense
    return $ maybePlace stmt pos:stmts'


-- | Execute the given code if semi-deterministic; otherwise report an error
ifSemiDet :: Determinism -> String -> Unbrancher a -> Unbrancher a
ifSemiDet Det msg _ = shouldnt msg
ifSemiDet SemiDet _ code = code


unbranchDisjunction :: [Placed Stmt] -> OptPos -> [Placed Stmt] -> [Placed Stmt]
                    -> Unbrancher [Placed Stmt]
unbranchDisjunction disjs pos stmts alt = nyi "Disjunction"


-- unbranchCond :: Determinism -> Placed Stmt -> [Placed Stmt] -> [Placed Stmt]
--              -> OptPos -> VarDict -> [Placed Stmt] -> Unbrancher [Placed Stmt]
-- unbranchCond detism tstStmt thn els pos exitVars stmts = do
--     logUnbranch $ "Unbranching a conditional in " ++ show detism ++ " context:"
--     logUnbranch $ showStmt 8 $ content tstStmt
--     beforeVars <- gets brVars
--     setVars exitVars
--     cont <- maybeFactorContinuation detism exitVars stmts alt
--     setVars beforeVars
--     logUnbranch $ "Vars before test: " ++ show beforeVars
--     tstStmt' <- placedApply (unbranchStmt SemiDet) tstStmt []
--     beforeThenVars <- gets brVars
--     logUnbranch "Unbranched condition:"
--     logUnbranch $ showBody 8 tstStmt'
--     logUnbranch $ "Unbranching then branch with vars: " ++ show beforeThenVars
--     thn' <- unbranchStmts detism $ thn ++ cont
--     logUnbranch $ "Unbranching else branch with vars: " ++ show beforeThenVars
--     setVars beforeVars
--     els' <- unbranchStmts detism $ els ++ cont
--     genStmt <- buildCond tstStmt' thn' beforeVars els' beforeVars pos
--                exitVars detism
--     logUnbranch $ "Conditional unbranched to " ++ showBody 4 genStmt
--     return genStmt

-- -- | Build code equivalent to Cond tsts thn els at source position pos,
-- --   where tsts, thn, and els have already been unbranched, so they are
-- --   simplified.  That means it can only contain Det ProcCalls, ForeignCalls,
-- --   TestBools, and Conds whose conditions are single non-constant TestBools.
-- --   It must also return code that satisfies this same constraint.
-- buildCond :: [Placed Stmt] -> [Placed Stmt] -> VarDict -> [Placed Stmt]
--           -> VarDict -> OptPos -> VarDict -> Determinism
--           -> Unbrancher [Placed Stmt]
-- buildCond tsts thn thnVars els elsVars pos exitVars detism = do
--     -- Work out how many calls to thn and els will be needed
--     -- let repeats = countRepeats . content <$> tsts
--     -- let thnCount = sum $ fst <$> repeats
--     -- let elsCount = sum $ snd <$> repeats
--     -- Generate fresh procs for the then and else branches if necessary
--     thn' <- maybeFactorContinuation detism thnVars thn
--     els' <- maybeFactorContinuation detism elsVars els
--     buildCond' tsts thn' els' pos exitVars detism


-- buildCond' :: [Placed Stmt] -> [Placed Stmt] -> [Placed Stmt] -> OptPos
--            -> VarDict -> Determinism -> Unbrancher [Placed Stmt]
-- buildCond' [] thn _els _pos _vars _detism = return thn
-- buildCond' (stmt:stmts) thn els exitVars pos detism =
--     placedApply buildCond'' stmt stmts thn els exitVars pos detism


-- buildCond'' :: Stmt -> OptPos -> [Placed Stmt] -> [Placed Stmt] -> [Placed Stmt]
--             -> OptPos -> VarDict -> Determinism -> Unbrancher [Placed Stmt]
-- buildCond'' stmt@(ProcCall _ _ _ Det _ _) pos stmts thn els condPos exitVars
--             detism =
--     (maybePlace stmt pos:) <$> buildCond' stmts thn els condPos exitVars detism
-- buildCond'' stmt@(ProcCall _ _ _ SemiDet _ _) pos stmts thn els condPos _ _ =
--     shouldnt $ "Should have transformed SemiDet calls before buildCond "
--                ++ show stmt
-- buildCond'' stmt@ForeignCall{} pos stmts thn els condPos exitVars detism =
--     (maybePlace stmt pos:) <$> buildCond' stmts thn els condPos exitVars detism
-- buildCond'' stmt@(TestBool (Typed (IntValue 1) _ _)) pos stmts thn els
--             condPos exitVars detism =
--     buildCond' stmts thn els condPos exitVars detism
-- buildCond'' stmt@(TestBool (Typed (IntValue 0) _ _)) _ _ _ els _ _ _ =
--     return els
-- buildCond'' stmt@TestBool{} pos stmts thn els condPos exitVars detism = do
--     thn' <- buildCond' stmts thn els condPos exitVars detism
--     return $ mkCond (maybePlace stmt pos) condPos thn' els exitVars
-- buildCond'' stmt@(Cond tst thn' els' vars) pos stmts thn els condPos exitVars
--             detism = do
--     let vars' = trustFromJust "buildCond'' given Cond with no vars" vars
--     stmts' <- maybeFactorContinuation detism vars' stmts
--     -- XXX performance bug:  should preprocess stmts into a single call
--     thn'' <- buildCond' (thn'++stmts') thn els condPos exitVars detism
--     els'' <- buildCond' (els'++stmts') thn els condPos exitVars detism
--     logUnbranch $ "Creating Cond with test = " ++ show tst
--     logUnbranch $ "                   then = " ++ showBody 26 thn''
--     logUnbranch $ "                   else = " ++ showBody 26 els''
--     return $ mkCond tst pos thn'' els'' exitVars
-- buildCond'' stmt _ _ _ _ _ _ _ =
--     shouldnt $ "Statement should have been eliminated before buildCond'': "
--                ++ show stmt


-- | Create a Cond statement, unless it can be simplified away.
mkCond :: Bool -> Exp -> OptPos -> [Placed Stmt] -> [Placed Stmt] -> VarDict
       -> [Placed Stmt]
mkCond False tst pos thn els vars = mkCond True tst pos els thn vars
mkCond True (IntValue 0) pos thn els vars = els
mkCond True (Typed (IntValue 0) _ _) pos thn els vars = els
mkCond True (IntValue 1) pos thn els vars = thn
mkCond True (Typed (IntValue 1) _ _) pos thn els vars = thn
mkCond True exp pos thn els vars
  | thn == els = thn
  | thn == [succeedTest] && els == [failTest] = [test]
  | otherwise =
    case (thn,els) of
      ([Unplaced (ForeignCall "llvm" "move" [] [thnSrc, thnDest])],
       [Unplaced (ForeignCall "llvm" "move" [] [elsSrc, elsDest])])
        | thnDest == elsDest ->
          let thnSrcContent = content thnSrc
              elsSrcContent = content elsSrc
              dest = content thnDest
          in [if thnSrcContent == boolTrue && elsSrcContent == boolFalse
              then move exp dest
              else if thnSrcContent == boolFalse && elsSrcContent == boolTrue
                   then boolNegate exp dest
                   else maybePlace (Cond test thn els $ Just vars) pos]
      _ -> [maybePlace (Cond test thn els $ Just vars) pos]
  where test = Unplaced $ TestBool exp


----------------------------------------------------------------
--               Unbranching SemiDet statement sequences
----------------------------------------------------------------

-- -- | 'Unbranch' a list of statements.  If isDryRun is true,
-- --   this is a "dry run", and should not generate any code, but only
-- --   work out which variables are defined when.
-- unbranchSemiDetStmts :: [Placed Stmt] -> Unbrancher [Placed Stmt]
-- unbranchSemiDetStmts [] = return [succeedTest]
-- unbranchSemiDetStmts (stmt:stmts) = do
--     vars <- gets brVars
--     logUnbranch $ "unbranching (SemiDet) stmt"
--         ++ "\n    " ++ showStmt 4 (content stmt)
--         ++ "\n  (SemiDet) with vars " ++ show vars
--     ifTerminated (do logUnbranch "terminated!" ; return [])
--         (placedApply unbranchSemiDet stmt stmts)


-- -- | 'Unbranch' a single SemiDet statement, along with all the following
-- --   statements. This transforms loops into calls to freshly generated
-- --   procedures that implement not only the loops themselves, but all
-- --   following code. That is, rather than returning at the loop exit(s),
-- --   the generated procs call procs for the code following the loops.
-- --   Similarly, conditionals are transformed by generating a separate proc
-- --   for the code following the conditional and adding a call to this proc
-- --   at the end of each arm of the conditional in place of the code
-- --   following the conditional, so that conditionals are always the final
-- --   statement in a statement sequence, as are calls to loop procs.
-- --
-- --   The input arguments to generated procs are all the variables in
-- --   scope everywhere the proc is called. The proc generated for the code
-- --   after a conditional is called only from the end of each branch, so the
-- --   set of input arguments is just the intersection of the sets of
-- --   variables defined at the end of each branch. Also note that the only
-- --   variable defined by the condition of a conditional that can be used in
-- --   the 'else' branch is the condition variable itself. The condition may
-- --   be permitted to bind other variables, but in the 'else' branch the
-- --   condition is considered to have failed, so the other variables cannot
-- --   be used.
-- --
-- --   The variables in scope at the start of a loop are the ones in scope at
-- --   *every* call to the generated proc. Since variables defined before the
-- --   loop can be redefined in the loop but cannot become "lost", this means
-- --   the intersection of the variables available at all calls is just the
-- --   set of variables defined at the start of the loop.  The inputs to the
-- --   proc generated for the code following a loop is the set of variables
-- --   defined at every 'break' in the loop.
-- --
-- --   Because these generated procs always chain to the next proc, they don't
-- --   need to return any values not returned by the proc they are generated
-- --   for, so the output arguments for all of them are just the output
-- --   arguments for the proc they are generated for.
-- --
-- --   Because later compiler passes will inline simple procs and remove dead
-- --   code and unneeded input and output arguments, we don't bother to try
-- --   to optimise these things here.
-- --
-- unbranchSemiDet :: Stmt -> OptPos -> [Placed Stmt] -> Unbrancher [Placed Stmt]
-- unbranchSemiDet stmt@(ProcCall _ _ _ Det _ args) pos stmts = do
--     logUnbranch $ "Unbranching call " ++ showStmt 4 stmt
--     defArgs args
--     stmts' <- unbranchSemiDetStmts stmts
--     return $ maybePlace stmt pos:stmts'
-- unbranchSemiDet stmt@(ProcCall md name procID SemiDet _ args) pos stmts = do
--     logUnbranch $ "converting SemiDet proc call" ++ show stmt
--     testVarName <- tempVar
--     let testStmt = TestBool $ varGet testVarName
--     stmts' <- unbranchSemiDetStmts stmts
--     let result = maybePlace (ProcCall md name procID Det False
--                          $ args ++ [Unplaced (boolVarSet testVarName)]) pos
--                  : mkCond (maybePlace testStmt pos) pos stmts' [failTest]
--     logUnbranch $ "#Converted SemiDet proc call" ++ show stmt
--     logUnbranch $ "#To: " ++ showBody 4 result
--     return result
-- unbranchSemiDet stmt@(ForeignCall _ _ _ args) pos stmts = do
--     logUnbranch $ "Unbranching foreign call " ++ showStmt 4 stmt
--     defArgs args
--     stmts' <- unbranchSemiDetStmts stmts
--     return $ maybePlace stmt pos:stmts'
-- unbranchSemiDet stmt@(TestBool _) pos [] = do
--     logUnbranch $ "Unbranching a final primitive test " ++ show stmt
--     return [maybePlace stmt pos]
-- unbranchSemiDet stmt@(TestBool _) pos stmts@(_:_) = do
--     logUnbranch $ "Unbranching a non-final primitive test " ++ show stmt
--     stmts' <- unbranchSemiDetStmts stmts
--     let result = mkCond (maybePlace stmt pos) Nothing stmts' [failTest]
--     logUnbranch $ "#Unbranched non-final primitive test " ++ show stmt
--     logUnbranch $ "#To: " ++ showBody 4 result
--     return result
-- unbranchSemiDet (And conj) pos stmts =
--     -- XXX might want to report if conj doesn't contain any tests
--     unbranchSemiDetStmts $ conj ++ stmts
-- unbranchSemiDet (Or []) _ stmts = return [failTest]
-- unbranchSemiDet (Or (disj:disjs)) pos stmts = do
--     logUnbranch "Unbranching disjunction"
--     unbranchCond SemiDet  disj [succeedTest] [Unplaced $ Or disjs] pos stmts
-- unbranchSemiDet (Not tst) pos stmts = do
--     logUnbranch "Unbranching negation"
--     unbranchCond SemiDet tst [failTest] [succeedTest] pos stmts
--     unbranchSemiDet (Cond tst [failTest] [succeedTest] Nothing) pos stmts
-- unbranchSemiDet (Cond tstStmt thn els _) pos stmts =
--     if detStmt $ content tstStmt
--     -- XXX Should warn of Cond with Det test, but can't because we transform
--     --     other code into Conds.
--     then (tstStmt:) <$> unbranchSemiDetStmts (thn ++ stmts)
--     else unbranchCond SemiDet tstStmt thn els pos stmts
-- unbranchSemiDet (Loop body exitVars) pos stmts = do
--     logUnbranch "Unbranching a loop with exitVars = " ++ show exitVars
--     beforeVars <- gets brVars
--     logUnbranch $ "Vars before loop: " ++ show beforeVars
--     prevState <- startLoop
--     logUnbranch $ "Handling loop:" ++ showBody 4 body
--     loopName <- newProcName
--     -- dryrun <- setDryRun True
--     -- unbranchSemiDetStmts $ body ++ [Unplaced Next]
--     -- resetTerminated False
--     -- setDryRun dryrun
--     -- exitVars <- gets (fromMaybe beforeVars . loopExitVars . brLoopInfo)
--     -- logUnbranch $ "loop exit vars from dryrun: " ++ show exitVars
--     -- setVars exitVars
--     stmts' <- unbranchSemiDetStmts stmts
--     logUnbranch $ "Next inputs: " ++ show beforeVars
--     next <- newProcCall loopName beforeVars pos
--     logUnbranch $ "Generated next " ++ showStmt 4 (content next)
--     -- if dryrun
--     --     then return ()
--     --     else do
--     breakName <- newProcName
--     logUnbranch $ "Break inputs: " ++ show exitVars
--     brk <- factorContinuationProc breakName exitVars Nothing stmts'
--     logUnbranch $ "Generated break " ++ showStmt 4 (content brk)
--     setBreakNext brk next
--     setVars beforeVars
--     body' <- unbranchSemiDetStmts $ body ++ [Unplaced Next]
--     factorContinuationProc loopName beforeVars pos body'
--     logUnbranch $ "Finished handling loop"
--     endLoop prevState
--     return [next]
-- -- unbranchSemiDet (For _ _) _ _ =
-- --     shouldnt "flattening should have removed For statements"
-- unbranchSemiDet (UseResources _ _) _ _ =
--     shouldnt "resource handling should have removed use ... in statements"
-- unbranchSemiDet Nop _ stmts = do
--     logUnbranch "Unbranching a Nop"
--     unbranchSemiDetStmts stmts         -- might as well filter out Nops
-- unbranchSemiDet Break _ _ = do
--     logUnbranch "Unbranching a Break"
--     -- resetTerminated True
--     -- recordBreakVars
--     brk <- gets (loopBreak . brLoopInfo)
--     logUnbranch $ "Current break proc = " ++ showStmt 4 (content brk)
--     return [brk]
-- unbranchSemiDet Next _ _ = do
--     logUnbranch "Unbranching a Next"
--     -- resetTerminated True
--     nxt <- gets (loopNext . brLoopInfo)
--     logUnbranch $ "Current next proc = " ++ showStmt 4 (content nxt)
--     return [nxt]


-- -- | Returns a pair of an upper bound on the number of times the then and
-- --   else branches of a conditional will be repeated, respectively, when
-- --   generating code for a Cond with the specified instruction as condition.
-- countRepeats :: Stmt -> (Int,Int)
-- countRepeats (TestBool (Typed (IntValue 1) _ _)) = (1,0)
-- countRepeats (TestBool (Typed (IntValue 0) _ _)) = (0,1)
-- countRepeats (TestBool _) = (1,1)
-- countRepeats (ProcCall _ _ _ Det _ _) = (0,0)
-- countRepeats ForeignCall{} = (0,0)
-- countRepeats (Cond stmt thn els _) =
--     let repeats = countRepeats . content <$> thn ++ els
--     in (sum $ fst <$> repeats, sum $ snd <$> repeats)
-- countRepeats stmt =
--   shouldnt $ "statement should have been removed before countRepeats: "
--              ++ show stmt


-- |Convert a list of the final statements of a proc body into a short list of
-- statements by turning them into a fresh proc if necessary.  The resulting
-- statement list will have been unbranched.
maybeFactorContinuation :: Determinism -> VarDict -> [Placed Stmt]
                        -> [Placed Stmt] -> Bool -> Unbrancher [Placed Stmt]
maybeFactorContinuation detism vars stmts alt sense = do
    -- XXX need better heuristic:  stmts must also be flat
    logUnbranch $ "Maybe factor continuation: " ++ showBody 4 stmts
    if length stmts <= 2
      then unbranchStmts detism stmts alt sense
      else (:[]) <$> factorContinuationProc vars Nothing detism stmts alt sense



-- unbranchBranch :: Determinism -> [Placed Stmt]
--                -> Unbrancher ([Placed Stmt],VarDict,Bool)
-- unbranchBranch detism branch = do
--     branch' <- case detism of
--       Det     -> unbranchStmts branch
--       SemiDet -> unbranchSemiDetStmts branch
--     branchVars <- gets brVars
--     logUnbranch $ "Vars after then/else branch: " ++ show branchVars
--     branchTerm <- isTerminated
--     logUnbranch $
--       "Then/else branch is" ++ (if branchTerm then "" else " NOT")
--           ++ " terminal"
--     return (branch', branchVars,branchTerm)


-- | Add the back statements at the end of the front.  Ensure we maintain
--   the invariant that only the final statement is allowed to be a Cond.
appendStmts :: [Placed Stmt] -> [Placed Stmt] -> [Placed Stmt]
appendStmts front [] = front
appendStmts [] back = back
appendStmts front back =
    case content $ last front of
      Cond tst thn els _ ->
        -- XXX Need exit vars below
        init front
        ++ [Unplaced
            $ Cond tst (appendStmts thn back) (appendStmts els back) Nothing]
      _ -> front ++ back


-- varsAfterITE :: VarDict -> Bool -> VarDict -> Bool -> VarDict
-- varsAfterITE thnVars True elsVars True   = Map.empty
-- varsAfterITE thnVars True elsVars False  = thnVars
-- varsAfterITE thnVars False elsVars True  = elsVars
-- varsAfterITE thnVars False elsVars False = Map.intersection thnVars elsVars


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
outputVars = List.foldr (ifIsVarDef Map.insert id  . content)


-- |Generate a fresh proc with all the vars in the supplied dictionary
--  as inputs, and all the output params of the proc we're unbranching as
--  outputs.  Then return a call to this proc with the same inputs and outputs.
--  Because this uses the list of outputs for the proc currently being
--  unbranched as the output list for the generated proc, this can only be used
--  for the final code for a proc.  The fresh proc will be recorded and will be
--  unbranched later.
factorContinuationProc :: VarDict -> OptPos -> Determinism
                       -> [Placed Stmt] -> [Placed Stmt] -> Bool
                       -> Unbrancher (Placed Stmt)
factorContinuationProc inVars pos detism stmts alt sense = do
    pname <- newProcName
    logUnbranch $ "Factoring "
      ++ selectDetism "Det" "SemiDet" detism
      ++ " continuation proc "
      ++ pname ++ ":"
      ++ showBody 4 stmts
    stmts' <- unbranchStmts detism stmts alt sense
    proto <- newProcProto pname inVars
    loopinfo <- gets brLoopInfo
    genProc loopinfo proto detism stmts'
    newProcCall pname inVars pos detism


-- |Generate a fresh proc with all the vars in the supplied dictionary
--  as inputs, and all the output params of the proc we're unbranching as
--  outputs.  Then return a call to this proc with the same inputs and outputs.
factorLoopProc :: [Placed Stmt] -> VarDict -> OptPos -> Determinism
               -> [Placed Stmt] -> [Placed Stmt] -> Bool
               -> Unbrancher (Placed Stmt)
factorLoopProc break inVars pos detism stmts alt sense = do
    pname <- newProcName
    logUnbranch $ "Factoring "
      ++ selectDetism "Det" "SemiDet" detism
      ++ " loop proc "
      ++ pname ++ ":"
      ++ showBody 4 stmts
    stmts' <- unbranchStmts detism stmts alt sense
    proto <- newProcProto pname inVars
    next <- newProcCall pname inVars pos detism
    let loopinfo = Just (LoopInfo next break)
    genProc loopinfo proto detism stmts'
    return next

varExp :: FlowDirection -> VarName -> TypeSpec -> Placed Exp
varExp flow var ty = Unplaced $ Typed (Var var flow Ordinary) ty False


newProcCall :: ProcName -> VarDict -> OptPos -> Determinism
            -> Unbrancher (Placed Stmt)
newProcCall name inVars pos detism = do
    let inArgs  = List.map (uncurry $ varExp ParamIn) $ Map.toList inVars
    outArgs <- gets brOutArgs
    currMod <- lift getModuleSpec
    let call = ProcCall currMod name (Just 0) detism False (inArgs ++ outArgs)
    logUnbranch $ "Generating call: " ++ showStmt 4 call
    -- XXX must handle semidet calls
    return $ maybePlace call pos


newProcProto :: ProcName -> VarDict -> Unbrancher ProcProto
newProcProto name inVars = do
    let inParams  = [Param v ty ParamIn Ordinary
                    | (v,ty) <- Map.toList inVars]
    outParams <- gets brOutParams
    return $ ProcProto name (inParams ++ outParams) Set.empty


-- |Return the first value when the detism is Det, the second otherwise
selectDetism :: a -> a -> Determinism -> a
selectDetism det _  Det = det
selectDetism _ semi SemiDet = semi
