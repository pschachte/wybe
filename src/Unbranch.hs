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
--  the loop.  Inside a loop, if {a:: b | else:: c} d e would be
--  transformed to a call to gen1, where gen2 is defined as def gen2
--  {d e}, and gen1 is defined as def gen1 {a:: b gen2 | else::
--  c gen2}.  So for example do {a if {b:: Break} c} d e would be
--  transformed into next1, which is defined as def next1 {a gen1},
--  gen1 is defined as def gen1 {b:: break1 | else:: gen2},
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

{-# LANGUAGE TupleSections #-}

module Unbranch (unbranchProc) where

import AST
import Resources
import Debug.Trace
import Snippets
import Config
import Control.Monad
import Control.Monad.Trans       (lift)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.List                 as List
import Data.Set                  as Set
import Data.Map                  as Map
import Data.Maybe
import Data.Tuple.HT             (mapFst)
import Options                   (LogSelection(Unbranch))
import Util
import LLVM.Internal.Function (getPrefixData)


-- |Transform away all loops, and all conditionals other than as the final
--  statement in their block. Transform all semidet code into conditional code
--  that ends with a TestBool or a call to a semidet proc. Transform all
--  conjunctions, disjunctions, and negations into conditionals. After this, all
--  bodies comprise a sequence of ProcCall, ForeignCall, TestBool, Cond, and Nop
--  statements. Furthermore, Cond statements can only be the final Stmt in a
--  body, the condition of a Cond can only be a single TestBool statement, and
--  TestBool statements can only appear as the condition of a Cond, or, in the
--  case of a SemiDet proc, as the final statement of a proc body. Every SemiDet
--  proc body must end with a TestBool, or a tail call to a SemiDet proc, or a
--  fork each of whose branches satisfies this constraint.

unbranchProc :: ProcDef -> Int -> Compiler ProcDef
unbranchProc proc _ = unbranchProc' proc


unbranchProc' :: ProcDef -> Compiler ProcDef
unbranchProc' proc = do
    let name = procName proc
    logMsg Unbranch $ "** Unbranching proc " ++ name ++ ":"
                      ++ showProcDef 0 proc ++ "\n"
    let ProcDefSrc body = procImpln proc
    let detism = procDetism proc
    let tmpCtr = procTmpCount proc
    let params = procProtoParams $ procProto proc
    let proto = procProto proc
    let params = procProtoParams proto
    let params' = selectDetism id addTestOutParam detism
                $ contentApply unbranchParam <$> params
    let stmts = selectDetism body (body++[move boolTrue testOutExp]) detism
    let impurity = procImpurity proc
    let proto' = proto {procProtoParams = params'}
    (body',tmpCtr',newProcs) <-
        unbranchBody name tmpCtr params' detism impurity stmts
    let proc' = proc { procProto = proto'
                     , procDetism = selectDetism detism Det detism
                     , procImpln = ProcDefSrc body'
                     , procTmpCount = tmpCtr'}
    logMsg Unbranch $ "** Unbranched defn:" ++ showProcDef 0 proc' ++ "\n"
    logMsg Unbranch "================================================\n"
    mapM_ addProcDef newProcs
    return proc'


-- |Eliminate loops and ensure that Conds only appear as the final
--  statement of a body.
unbranchBody :: ProcName -> Int -> [Placed Param] -> Determinism -> Impurity
             -> [Placed Stmt] -> Compiler ([Placed Stmt],Int,[ProcDef])
unbranchBody name tmpCtr params detism impurity body = do
    let unbrancher =
            initUnbrancherState Nothing tmpCtr detism impurity params name
    let outparams =  brOutParams unbrancher
    let outvars = brOutArgs unbrancher
    let stmts = body
    logMsg Unbranch $ "** Unbranching with output params:" ++ show outparams
    logMsg Unbranch $ "** Unbranching with output args:" ++ show outvars
    (stmts',st) <- runStateT (unbranchStmts stmts) unbrancher
    return (stmts',brTempCtr st, brNewDefs st)


----------------------------------------------------------------
--                 Converting SemiDet procs to Det
----------------------------------------------------------------

-- |A synthetic output parameter carrying the test result
testOutParam :: Param
testOutParam = Param outputStatusName boolType ParamOut Ordinary


-- |The output exp we use to hold the success/failure of a test proc.
testOutExp :: Exp
testOutExp = boolVarSet outputStatusName


-- |The input exp we use to hold the success/failure of a test proc.
testInExp :: Exp
testInExp = boolVarGet outputStatusName


-- | Get the index a test output should be if the given params are from a
-- SemiDet proc
testOutIndex :: [Param] -> Int
testOutIndex = length . takeWhile (((==Free) ||| (==Ordinary)) . paramFlowType)


-- | Add a test output param to the list of params, as well as the index of the
-- test output
addTestOutParam :: [Placed Param] -> [Placed Param]
addTestOutParam params = insertAt (testOutIndex $ content <$> params) (Unplaced testOutParam) params


-- | Add a tmp var to the list of expressions in the position dictated by the
-- ProcFunctor to determinise a statement
addTestOutExp :: ProcFunctor -> [Placed Exp] -> Unbrancher ([Placed Exp], Exp)
addTestOutExp func args = do
    testResultVar <- tempVar
    (nParams, detism) <- case func of
        Higher fn ->
            case content fn of
                Typed _ (HigherOrderType mods params) _ -> do
                    return (length params, modifierDetism mods)
                _ -> shouldnt "badly typed higher in addTestOutExp"
        First mod nm pId -> do
            ProcDef{procProto=ProcProto _ params _, procDetism=detism}
                <- lift $ getProcDef $ ProcSpec mod nm
                                        (trustFromJust "addTestOutExp" pId)
                                        generalVersion
            return (testOutIndex $ content <$> params, detism)
    let idx = selectDetism (nParams - 1) nParams detism
    return (insertAt idx (Unplaced $ boolVarSet testResultVar) args,
            boolVarGet testResultVar)

----------------------------------------------------------------
--                  Handling the Unbrancher monad
----------------------------------------------------------------

-- |The Unbrancher monad is a state transformer monad carrying the
--  unbrancher state over the compiler monad.
type Unbrancher = StateT UnbrancherState Compiler

data UnbrancherState = Unbrancher {
    brLoopInfo   :: Maybe LoopInfo,
                                  -- ^If in a loop, break and continue stmts
    brVars       :: VarDict,      -- ^Types of variables defined up to here
    brTempCtr    :: Int,          -- ^Number of next temp variable to make
    brOutParams  :: [Placed Param],
                                  -- ^Output arguments for generated procs
    brOutArgs    :: [Placed Exp], -- ^Output arguments for call to gen procs
    brInOutVars  :: Set VarName,  -- ^In/Out argument names
    brNewDefs    :: [ProcDef],    -- ^Generated unbranched auxilliary procedures
    brClosures   :: Map (ProcSpec, Map Integer Exp) ProcSpec,
                                  -- ^Generated procs for closures
    brPreassigned:: Set VarName,  -- ^Variables already assigned at entry to
                                  -- the current SemiDet context (and so must be
                                  -- saved if they are reassigned)
    brDetism     :: Determinism,  -- ^The determinism of the current context
    brImpurity   :: Impurity,     -- ^The impurity of the enclosing proc
    brAlternate  :: [Placed Stmt], -- ^Code to execute in case of failure
    brSense      :: Bool,         -- ^True iff execute brAlternate on failure 
    brProcName   :: ProcName      -- ^The name of the proc being unbranched
    }


data LoopInfo = LoopInfo {
    loopNext :: Placed Stmt,      -- ^Call to make for a Next
    loopBreak :: [Placed Stmt]    -- ^Code to execute for a Break
    } deriving (Eq)


initUnbrancherState :: Maybe LoopInfo -> Int -> Determinism -> Impurity
                    -> [Placed Param] -> ProcName -> UnbrancherState
initUnbrancherState loopinfo tmpCtr detism impurity params =
    let defined = inputParams $ content <$> params
        outParams = [unbranchParam (Param nm ty ParamOut ft) `maybePlace` pos
                    | (Param nm ty fl ft, pos) <- unPlace <$> params
                    , flowsOut fl]
        outArgs   = [Typed (varSet nm) (unbranchType ty) Nothing `maybePlace` pos
                    | (Param nm ty fl _, pos) <- unPlace <$> params
                    , flowsOut fl]
        inOuts = [nm
                 | (Param nm _ fl _, pos) <- unPlace <$> params
                 , flowsOut fl && flowsIn fl]
        alt = selectDetism [] [move boolFalse testOutExp] detism
    in Unbrancher loopinfo defined tmpCtr outParams outArgs
            (Set.fromList inOuts) [] Map.empty Set.empty detism impurity
            alt True


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
setVars :: VarDict -> Unbrancher VarDict
setVars vars = do
    oldVars <- gets brVars
    modify (\s -> s { brVars = vars })
    return oldVars


-- |Execute an unbrancher with brVars temporarily set as specified
withVars :: VarDict -> Unbrancher a -> Unbrancher a
withVars vars unbrancher = do
    oldVars <- setVars vars
    unbrancher <* setVars oldVars


-- |Execute the specified code with the brancher determinism set to SemiDet, and
-- with the specified alternative code, and then reset the determinism to what
-- it was. 
inSemiDetContext :: [Placed Stmt] -> Unbrancher a -> Unbrancher a
inSemiDetContext alt code = do
    oldDetism <- gets brDetism
    oldAlt <- gets brAlternate
    modify $ \s -> s { brAlternate = alt, brDetism = SemiDet }
    result <- code
    modify (\s -> s { brAlternate = oldAlt, brDetism = oldDetism })
    return result


-- |Execute the specified goal with the specified function applied to the
-- sense of the unbrancher state; leave the sense of the state as it was
withSense :: (Bool -> Bool) -> Unbrancher a -> Unbrancher a
withSense fn code = do
    sense <- gets brSense
    modify $ \s -> s { brSense = fn sense }
    result <- code
    modify $ \s -> s { brSense = sense }
    return result


-- |Generate a fresh proc name that does not collide with any proc in the
-- current module.
newProcName :: ProcName -> Unbrancher String
newProcName name = lift . genProcName . (`specialName2` name) =<< gets brProcName


-- |Create, unbranch, and record a new proc with the specified proto,
-- determinism and body.  Takes its impurity from the parent proc.
genProc :: ProcProto -> Determinism -> [Placed Stmt] -> Unbrancher ()
genProc proto detism stmts = do
    let name = procProtoName proto
    tmpCtr <- gets brTempCtr
    impurity <- gets brImpurity
    -- call site count will be refilled later
    let procDef = ProcDef name proto (ProcDefSrc stmts) Nothing tmpCtr 0
                  Map.empty Private detism MayInline impurity GeneratedProc
                  NoSuperproc Map.empty
    logUnbranch $ "Generating fresh " ++ show detism ++ " proc:"
                  ++ showProcDef 8 procDef
    logUnbranch $ "Unbranched generated " ++ show detism ++ " proc:"
                  ++ showProcDef 8 procDef
    modify (\s -> s { brNewDefs = procDef:brNewDefs s })


-- |Return a fresh variable name.
tempVar :: Unbrancher VarName
tempVar = do
    ctr <- gets brTempCtr
    modify (\s -> s { brTempCtr = ctr + 1 })
    return $ mkTempName ctr


-- |Log a message, if we are logging unbrancher activity.
logUnbranch :: String -> Unbrancher ()
logUnbranch s = do
    lift $ logMsg Unbranch s


-- |Return the current loop break statement(s)
getLoopBreak :: OptPos -> Unbrancher [Placed Stmt]
getLoopBreak pos = do
    mbInfo <- gets brLoopInfo
    case mbInfo of
        Just info -> return $ loopBreak info
        Nothing   -> do
            lift $ errmsg pos "Break outside of a loop"
            return []


-- |Return the current loop continuation (next) statement
getLoopNext :: OptPos -> Unbrancher (Placed Stmt)
getLoopNext pos = do
    mbInfo <- gets brLoopInfo
    case mbInfo of
        Just info -> return $ loopNext info
        Nothing   -> do
            lift $ errmsg pos "Next outside of a loop"
            return $ Unplaced Nop


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
unbranchStmts :: [Placed Stmt] -> Unbrancher [Placed Stmt]
unbranchStmts [] = do
    detism <- gets brDetism
    logUnbranch $ "Unbranching an empty " ++ show detism ++ " body"
    return []
unbranchStmts (stmt:stmts) = do
    detism <- gets brDetism
    vars <- gets brVars
    logUnbranch $ "unbranching " ++ show detism ++ " stmt"
        ++ "\n    " ++ showStmt 4 (content stmt)
        ++ "\n  with vars " ++ showVarMap vars
    placedApply unbranchStmt stmt stmts


-- | 'Unbranch' a single statement, given a list of following statements and an
--   already unbranched list of alternative statements. This also considers the
--   sense of the test: if True, execution should go to the following statements
--   on success and the alternative statements on failure; if False, then
--   vice-versa. The following statements are represented as a pair of a list of
--   not yet unbranched statements and a list of unbranched alternative
--   statements. The alternative statements will have been factored out into a
--   call to a fresh procedure if necessary (ie, if it will be used in more than
--   one case, it will be a short list).
--
--   This transforms loops into calls to freshly generated procedures that
--   implement not only the loops themselves, but all following code. That is,
--   rather than returning at the loop exit(s), the generated procs call procs
--   for the code following the loops. Similarly, conditionals are transformed
--   by generating a separate proc for the code following the conditional and
--   adding a call to this proc at the end of each arm of the conditional in
--   place of the code following the conditional, so that conditionals are
--   always the final statement in a statement sequence, as are calls to loop
--   procs.
--
--   The input arguments to generated procs are all the variables in scope
--   everywhere the proc is called. The proc generated for the code after a
--   conditional is called only from the end of each branch, so the set of input
--   arguments is just the intersection of the sets of variables defined at the
--   end of each branch. Also note that the only variable defined by the
--   condition of a conditional that can be used in the 'else' branch is the
--   condition variable itself. The condition may be permitted to bind other
--   variables, but in the 'else' branch the condition is considered to have
--   failed, so the other variables cannot be used.
--
--   The variables in scope at the start of a loop are the ones in scope at
--   *every* call to the generated proc. Since variables defined before the loop
--   can be redefined in the loop but cannot become "lost", this means the
--   intersection of the variables available at all calls is just the set of
--   variables defined at the start of the loop.  The inputs to the proc
--   generated for the code following a loop is the set of variables defined at
--   every 'break' in the loop.
--
--   Because these generated procs always chain to the next proc, they don't
--   need to return any values not returned by the proc they are generated for,
--   so the output arguments for all of them are just the output arguments for
--   the proc they are generated for.
--
--   Because later compiler passes will inline simple procs and remove dead code
--   and unneeded input and output arguments, we don't bother to try to optimise
--   these things here.
--
unbranchStmt :: Stmt -> OptPos -> [Placed Stmt]
             -> Unbrancher [Placed Stmt]
unbranchStmt stmt@(ProcCall _ _ True args) _ _ =
    shouldnt $ "Resources should have been handled before unbranching: "
               ++ showStmt 4 stmt
unbranchStmt stmt@(ProcCall func SemiDet _ args) pos stmts = do
    mustBeSemiDet ("SemiDet proc call " ++ show stmt)
    logUnbranch $ "converting SemiDet proc call" ++ show stmt
    (args', val) <- addTestOutExp func args
    args'' <- unbranchArgs args'
    condVars <- gets brVars
    stmts' <- unbranchStmts stmts
    vars <- gets brVars
    alt <- gets brAlternate
    sense <- gets brSense
    logUnbranch $ "mkCond " ++ show sense ++ " " ++ show val
                ++ showBody 4 stmts' ++ "\nelse"
                ++ showBody 4 alt
    func' <- unbranchProcFunctor func
    result <- (maybePlace (ProcCall func' Det False args'') pos :)
               <$> mkCond sense val pos stmts' alt condVars vars
    logUnbranch $ "#Converted SemiDet proc call" ++ show stmt
    logUnbranch $ "#To: " ++ showBody 4 result
    return result
unbranchStmt stmt@(ProcCall func calldetism r args) pos stmts = do
    alt <- gets brAlternate
    logUnbranch $ "Unbranching call " ++ showStmt 4 stmt
    args' <- unbranchArgs args
    func' <- unbranchProcFunctor func
    let stmt' = ProcCall func' calldetism r args'
    case calldetism of
      Terminal -> return [maybePlace stmt' pos] -- no execution after Terminal
      Failure  -> return [maybePlace stmt' pos] -- no execution after Failure
      Det      -> leaveStmtAsIs stmt' pos stmts
      SemiDet  -> shouldnt "SemiDet case already covered!"
unbranchStmt stmt@(ForeignCall l nm fs args) pos stmts = do
    alt <- gets brAlternate
    logUnbranch $ "Unbranching foreign call " ++ showStmt 4 stmt
    args' <- unbranchArgs args
    let stmt' = ForeignCall l nm fs args'
    leaveStmtAsIs stmt' pos stmts
unbranchStmt stmt@(TestBool val) pos stmts = do
    alt <- gets brAlternate
    mustBeSemiDet (showStmt 4 stmt)
    condVars <- gets brVars
    logUnbranch $ "Unbranching a non-final primitive test " ++ show stmt
    stmts' <- unbranchStmts stmts
    vars <- gets brVars
    sense <- gets brSense
    logUnbranch $ "mkCond " ++ show sense ++ " " ++ show val
                ++ showBody 4 stmts' ++ "\nelse"
                ++ showBody 4 alt
    result <- mkCond sense val Nothing stmts' alt condVars vars
    logUnbranch $ "#Unbranched non-final primitive test " ++ show stmt
    logUnbranch $ "#To: " ++ showBody 4 result
    return result
unbranchStmt stmt@(And conj) pos stmts = do
    alt <- gets brAlternate
    logUnbranch $ "Unbranching conjunction " ++ show stmt
    unbranchStmts (conj ++ stmts)
unbranchStmt stmt@(Or [] exitVars _) pos stmts = do
    alt <- gets brAlternate
    mustBeSemiDet "Empty disjunction"
    unbranchStmt (TestBool boolFalse) pos stmts
unbranchStmt stmt@(Or [disj] exitVars _) _ stmts = do
    alt <- gets brAlternate
    placedApply unbranchStmt disj stmts
unbranchStmt stmt@(Or (disj:disjs) exitVars res) pos stmts = do
    alt <- gets brAlternate
    let exitVars' = trustFromJust "unbranching Disjunction without exitVars"
                    exitVars
    let res' = trustFromJust "unbranching Loop without res" res
    logUnbranch $ "Unbranching disjunction " ++ show stmt
    logUnbranch $ "Following disjunction: " ++ showBody 4 stmts
    logUnbranch $ "Disjunction alternative: " ++ showBody 4 alt
    stmts' <- maybeFactorContinuation exitVars' res' stmts
    logUnbranch $ "Disjunction successor: " ++ showBody 4 stmts'
    beforeDisjVars <- gets brVars
    disjs' <- unbranchStmt (Or disjs exitVars res) pos stmts'
    -- Update known vars back to state before condition (must have failed)
    modify $ \s -> s { brVars = beforeDisjVars }
    inSemiDetContext disjs'
        $ placedApply unbranchStmt disj stmts'
unbranchStmt stmt@(Not tst) pos stmts = do
    alt <- gets brAlternate
    mustBeSemiDet ("Negation " ++ show stmt)
    logUnbranch "Unbranching negation"
    withSense not $ placedApply unbranchStmt tst stmts
unbranchStmt (Cond tst thn els condVars exitVars res) pos stmts = do
    alt <- gets brAlternate
    let condVars' = trustFromJust "unbranching Cond without condVars" condVars
    let exitVars' = trustFromJust "unbranching Cond without exitVars" exitVars
    let res' = trustFromJust "unbranching Loop without res" res
    stmts'' <- maybeFactorContinuation exitVars' res' stmts
    beforeCondVars <- gets brVars
    -- Update known vars to include vars generated by condition
    modify $ \s -> s { brVars = condVars' }
    thn' <- unbranchStmts (thn ++ stmts'')
    -- Update known vars back to state before condition (must have failed)
    modify $ \s -> s { brVars = beforeCondVars }
    els' <- unbranchStmts (els ++ stmts'')
    inSemiDetContext els' $ withSense (const True)
        $ placedApply unbranchStmt tst thn'
unbranchStmt (Loop body exitVars res) pos stmts = do
    alt <- gets brAlternate
    let exitVars' = trustFromJust "unbranching Loop without exitVars" exitVars
    let res' = trustFromJust "unbranching Loop without res" res
    logUnbranch $ "Handling loop:" ++ showBody 4 body
    beforeVars <- gets brVars
    logUnbranch $ "  with entry vars " ++ showVarMap beforeVars
    brk <- maybeFactorContinuation exitVars' res' stmts
    logUnbranch $ "Generated break: " ++ showBody 4 brk
    next <- factorLoopProc brk beforeVars pos res'
                (body ++ [maybePlace Next pos])
    logUnbranch $ "Generated next " ++ showStmt 4 (content next)
    logUnbranch "Finished handling loop"
    return [next]
unbranchStmt UseResources{} _ _ =
    shouldnt "resource handling should have removed use ... in statements"
unbranchStmt For{} _ _ =
    shouldnt "flattening should have removed For statements"
unbranchStmt Case{} _ _ =
    shouldnt "flattening should have removed Case statements"
unbranchStmt Nop _ stmts = do
    alt <- gets brAlternate
    logUnbranch "Unbranching a Nop"
    unbranchStmts stmts     -- might as well filter out Nops
unbranchStmt Fail pos stmts = do
    alt <- gets brAlternate
    logUnbranch "Unbranching a Fail"
    -- XXX JB we stil have alt stmts to go...
    -- return [maybePlace Fail pos] -- no execution after Fail
    return alt
unbranchStmt Break pos _ = do
    logUnbranch "Unbranching a Break"
    brk <- getLoopBreak pos
    logUnbranch $ "Current break = " ++ showBody 4 brk
    return brk
unbranchStmt Next pos _ = do
    logUnbranch "Unbranching a Next"
    nxt <- getLoopNext pos
    logUnbranch $ "Current next proc = " ++ showStmt 4 (content nxt)
    return [nxt]

-- |Emit the supplied statement, and process the remaining statements.
leaveStmtAsIs :: Stmt -> OptPos -> [Placed Stmt] -> Unbrancher [Placed Stmt]
leaveStmtAsIs stmt pos stmts = do
    logUnbranch $ "Leaving stmt as is: " ++ showStmt 4 stmt
    stmts' <- unbranchStmts stmts
    return $ maybePlace stmt pos:stmts'


-- | Execute the given code if the context is semi-deterministic; otherwise
-- report an error
mustBeSemiDet :: String -> Unbrancher ()
mustBeSemiDet msg = do
    detism <- gets brDetism
    when (detism < SemiDet)
        $ shouldnt $ msg ++ " in a " ++ show detism ++ " context"


-- | Create a Cond statement, unless it can be simplified away.
mkCond :: Bool -> Exp -> OptPos -> [Placed Stmt] -> [Placed Stmt]
       -> VarDict -> VarDict -> Unbrancher [Placed Stmt]
mkCond False tst pos thn els condVars vars =
    mkCond True tst pos els thn condVars vars
mkCond True (IntValue 0) pos thn els condVars vars = return els
mkCond True (Typed (IntValue 0) _ _) pos thn els condVars vars = return els
mkCond True (IntValue 1) pos thn els condVars vars = return thn
mkCond True (Typed (IntValue 1) _ _) pos thn els condVars vars = return thn
mkCond True intval@(Typed val ty _) pos thn els condVars vars
 | ty == intType = do
    tmp <- tempVar
    let comparison =
            Unplaced (ForeignCall "llvm" "icmp_ne" []
                [Unplaced intval,
                 Unplaced $ iVal 0 `withType` intType,
                 Unplaced $ boolVarSet tmp])
    (comparison:) <$> mkCond True (boolVarGet tmp) pos thn els condVars vars
mkCond True exp pos thn els condVars vars
  | thn == els = return thn
  | otherwise =
    case (thn,els) of
      ([Unplaced (ForeignCall "llvm" "move" [] [thnSrc, thnDest])],
       [Unplaced (ForeignCall "llvm" "move" [] [elsSrc, elsDest])])
        | thnDest == elsDest ->
          let thnSrcContent = content thnSrc
              elsSrcContent = content elsSrc
              dest = content thnDest
          in return [if thnSrcContent == boolTrue && elsSrcContent == boolFalse
                     then move exp dest
                     else if thnSrcContent == boolFalse
                             && elsSrcContent == boolTrue
                     then boolNegate exp dest
                     else maybePlace
                        (Cond test thn els
                            (Just condVars) (Just vars) (Just Set.empty)) pos]
      _ -> return [maybePlace (Cond test thn els
                            (Just condVars) (Just vars) (Just Set.empty)) pos]
  where test = Unplaced $ TestBool exp


-- |Convert a list of the final statements of a proc body into a short list of
-- statements by turning them into a fresh proc if necessary.  The resulting
-- statement list will have been unbranched.
maybeFactorContinuation :: VarDict -> Set ResourceSpec -> [Placed Stmt]
                        -> Unbrancher [Placed Stmt]
maybeFactorContinuation vars res stmts = do
    detism <- gets brDetism
    logUnbranch $ "Maybe factor " ++ show detism ++ " continuation: "
                  ++ showBody 4 stmts
    logUnbranch $ "  with brVars: " ++ showVarMap vars
    withVars vars
      $ if length stmts <= 2 && all (flatStmt . content) stmts
        then unbranchStmts stmts
        else (:[]) <$> factorContinuationProc vars Nothing res stmts


-- |Test that a statement is not compound
flatStmt :: Stmt -> Bool
flatStmt ProcCall{}    = True
flatStmt ForeignCall{} = True
flatStmt Nop           = True
flatStmt TestBool{}    = True
flatStmt (Not stmt)    = flatStmt $ content stmt
flatStmt Break         = True
flatStmt Next          = True
flatStmt _             = False


-- |A symbol table containing all input parameters
inputParams :: [Param] -> VarDict
inputParams params =
    List.foldr
    (\(Param v ty dir _) vdict ->
         if flowsIn dir then Map.insert v ty vdict else vdict)
    Map.empty params


-- | Unbranch a type, ensuring that all higher order types are no longer SemiDet
unbranchType :: TypeSpec -> TypeSpec
unbranchType (TypeSpec mod nm params) = TypeSpec mod nm $ unbranchType <$> params
unbranchType (HigherOrderType mods tfs) =
    let (tys, flows) = unzipTypeFlows tfs
        tfs' = zipWith TypeFlow (unbranchType <$> tys) flows
    in selectDetism
            (HigherOrderType mods tfs')
            (HigherOrderType mods{modifierDetism=Det}
                $ tfs' ++ [TypeFlow boolType ParamOut])
            (modifierDetism mods)
unbranchType ty = ty


-- | Unbranch a param, ensuring the type of the param is unbrached
unbranchParam :: Param -> Param
unbranchParam param@Param{paramType=ty} = param{paramType=unbranchType ty}


-- Unbranch a ProcFunctore, tansforming expressions in Highers
unbranchProcFunctor :: ProcFunctor -> Unbrancher ProcFunctor
unbranchProcFunctor func@First{} = return func
unbranchProcFunctor (Higher fn)  = Higher . head <$> unbranchArgs [fn]


-- |Add all output arguments of a param list to the symbol table
--  and hoist all closures
unbranchArgs :: [Placed Exp] -> Unbrancher [Placed Exp]
unbranchArgs args = do
    detism <- gets brDetism
    selectDetism (return ())
          (mapM_ (noteReassignment . content) args) detism
    mapM_ (defArg . content) args
    mapM (placedApply unbranchExp) args


noteReassignment :: Exp -> Unbrancher ()
noteReassignment (Typed exp _ _) = noteReassignment exp
noteReassignment (Var name flow _)
  | flowsOut flow = do
    procName <- gets brProcName
    reassigned <- Map.member name <$> gets brVars
    when reassigned $ do
        logUnbranch $ "Reassignment of variable " ++ name
            ++ " in " ++ showProcName procName

noteReassignment _ = return ()


-- | Unbranch an expression, transforming Closures and AnonProcs into fresh
-- 'closure' procs.  This shouldn't be called outside of unbranchArgs.
unbranchExp :: Exp -> OptPos -> Unbrancher (Placed Exp)
unbranchExp (Typed exp ty cast) pos = do
    exp' <- content <$> unbranchExp exp Nothing
    let ty' = unbranchType ty
    let cast' = unbranchType <$> cast
    return $ maybePlace (Typed exp' ty' cast') pos
unbranchExp exp@(AnonProc mods params pstmts clsd res) pos = do
    let clsd' = trustFromJust "unbranch anon proc without closed" clsd
    let res' = trustFromJust "unbranch anon proc without resources" res
    name <- newProcName "anon"
    logUnbranch $ "Creating Closure for " ++ show exp ++ " under " ++ name
    let ProcModifiers detism inlining impurity _ _ = mods
    let (freeParams, freeVars) = unzip $ uncurry freeParamVar <$> Map.toAscList clsd'
    logUnbranch $ "  With params " ++ show params
    logUnbranch $ "  With free variables " ++ show freeVars
    tmpCtr <- gets brTempCtr
    let procProto = ProcProto name (freeParams ++ (Unplaced <$> params)) res'
    let procDef = ProcDef name procProto (ProcDefSrc pstmts) Nothing tmpCtr 0
                    Map.empty Private detism inlining impurity AnonymousProc
                    NoSuperproc Map.empty
    procDef' <- lift $ unbranchProc procDef tmpCtr
    logUnbranch $ "  Resultant hoisted proc: " ++ show procProto
    procSpec <- lift $ addProcDef procDef'
    addClosure procSpec freeVars pos name
unbranchExp exp@(Closure ps free) pos = do
    free' <- unbranchArgs free
    isClosure <- lift $ isClosureProc ps
    if isClosure
    then return $ maybePlace exp pos
    else newProcName "closure" >>= addClosure ps free pos
unbranchExp exp pos = return $ maybePlace exp pos


-- | Create and add a closure of the given ProcSpec with the given name
-- and free variables
addClosure :: ProcSpec -> [Placed Exp] -> OptPos -> String
           -> Unbrancher (Placed Exp)
addClosure regularProcSpec@(ProcSpec mod nm pID _) free pos name = do
    ProcDef{procDetism=detism, procInlining=inlining, procImpurity=impurity,
            procProto=procProto@ProcProto{procProtoParams=params,
                                          procProtoResources=res}}
        <- lift $ getProcDef regularProcSpec
    let (params', args, constMap) = makeFreeParams (content <$> params) free
    closProcs <- gets brClosures
    case Map.lookup (regularProcSpec, constMap) closProcs of
        Just closProc -> return $ Closure closProc free `maybePlace` pos
        Nothing -> do
            let pDefClosure =
                    ProcDef name (ProcProto name params' res)
                    (ProcDefSrc [Unplaced $ ProcCall (First mod nm $ Just pID)
                                                detism False args])
                    Nothing 0 0 Map.empty Private detism inlining impurity
                    (ClosureProc regularProcSpec) NoSuperproc Map.empty
            logUnbranch $ "Creating closure for " ++ show regularProcSpec
            logUnbranch $ "  with params: " ++ show params'
            logUnbranch $ "  with args  : " ++ show args
            logUnbranch $ "  with free  : " ++ show free
            pDefClosure' <- lift $ unbranchProc pDefClosure 0
            closureProcSpec <- lift $ addProcDef pDefClosure'
            logUnbranch $ "  Resultant closure proc: " ++ show closureProcSpec
            modify $ \s -> s{brClosures=Map.insert (regularProcSpec, constMap)
                                        closureProcSpec $ brClosures s}
            return $ Closure closureProcSpec free `maybePlace` pos


-- | Transform a list of params a prefix of corresponding arguments into a
-- list of params, args, and free variables, where the transformed list of
-- params are the closure's params, the args are the arguments to the inner call,
-- and the free variables represent the variables that are free to the closure.
-- This removes params/free variables where the expression is a known constant
makeFreeParams :: [Param] -> [Placed Exp]
               -> ([Placed Param], [Placed Exp], Map Integer Exp)
makeFreeParams params exps = makeFreeParams' 1 params $ unPlace <$> exps


makeFreeParams' :: Integer -> [Param] -> [(Exp, OptPos)]
                -> ([Placed Param], [Placed Exp], Map Integer Exp)
makeFreeParams' _ params [] = (Unplaced <$> params', paramToVar <$> params', Map.empty)
  where params' = freeParamToOrdinary . unbranchParam <$> params
makeFreeParams' _ [] _ = shouldnt "too many exps for params"
makeFreeParams' idx ((Param nm pTy fl _):params) ((Typed exp ty cast,pos):exps)
    | flowsOut fl = shouldnt "out flowing free param"
    | otherwise   = (param':params', exp' `maybePlace` pos:exps', constMap')
  where
    (params', exps', constMap) = makeFreeParams' (idx + 1) params exps
    param' = Param nm (unbranchType pTy) ParamIn Free `maybePlace` pos
    mbExp = expIsConstant exp
    exp' = Typed (fromMaybe (Var nm ParamIn Free) $ expIsConstant exp) ty' cast'
    constMap' = if isJust mbExp
                then Map.insert idx exp' constMap
                else constMap
    ty' = unbranchType ty
    cast' = unbranchType <$> cast
makeFreeParams' _ _ _ = shouldnt "untyped free var"


-- | Set the ArgFlowType of a Free Param to Ordinary, else do nothing
freeParamToOrdinary :: Param -> Param
freeParamToOrdinary param@(Param _ _ _ Free) = param{paramFlowType=Ordinary}
freeParamToOrdinary param                    = param


-- |Get Free Param and Typed Var for the given VarName and TypeSpec
freeParamVar :: VarName -> TypeSpec -> (Placed Param, Placed Exp)
freeParamVar nm ty =
    let ty' = unbranchType ty
    in (Unplaced $ Param nm ty' ParamIn Free,
        Unplaced $ Typed (Var nm ParamIn Free) ty' Nothing)


-- |Add the output variables defined by the expression to the symbol
--  table. Since the expression is already flattened (excluding AnonProcs),
--  it will only be a constant, in which case it doesn't define any variables,
--  or a variable, in which case it might.
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
ifIsVarDef' _ v t ty = v


outputVars :: VarDict -> [Placed Exp] -> VarDict
outputVars = List.foldr (ifIsVarDef Map.insert id  . content)


continutationProcName :: ProcName
continutationProcName = "cont"


-- |Generate a fresh proc with all the vars in the supplied dictionary
--  as inputs, and all the output params of the proc we're unbranching as
--  outputs.  Then return a call to this proc with the same inputs and outputs.
--  Because this uses the list of outputs for the proc currently being
--  unbranched as the output list for the generated proc, this can only be used
--  for the final code for a proc.  The fresh proc will be recorded and will be
--  unbranched later.
factorContinuationProc :: VarDict -> OptPos -> Set ResourceSpec
                       -> [Placed Stmt] -> Unbrancher (Placed Stmt)
factorContinuationProc inVars pos res stmts = do
    detism <- gets brDetism
    name <- newProcName continutationProcName
    logUnbranch $ "Factoring " ++ show detism ++ " continuation proc "
                  ++ name ++ ":" ++ showBody 4 stmts
    stmts' <- unbranchStmts stmts
    inOuts <- gets brInOutVars
    let stmtsIns = stmtsInputs stmts'
    let usedVars = Map.filterWithKey (const . (`Set.member` (stmtsIns `Set.union` inOuts))) inVars
    proto <- newProcProto name usedVars res
    genProc proto Det stmts' -- Continuation procs are always Det
    newProcCall name usedVars pos Det


-- |Generate a fresh proc with all the vars in the supplied dictionary
--  as inputs, and all the output params of the proc we're unbranching as
--  outputs.  Then return a call to this proc with the same inputs and outputs.
factorLoopProc :: [Placed Stmt] -> VarDict -> OptPos -> Set ResourceSpec
               -> [Placed Stmt] -> Unbrancher (Placed Stmt)
factorLoopProc break inVars pos res stmts = do
    detism <- gets brDetism
    pname <- newProcName continutationProcName
    logUnbranch $ "Factoring " ++ show detism ++ " loop proc "
                  ++ pname ++ ":" ++ showBody 4 stmts
                  ++ "\nLoop input vars = " ++ show inVars
    alt <- gets brAlternate
    let stmtsIns = stmtsInputs $ break ++ stmts ++ alt
    inOuts <- gets brInOutVars
    outs <- gets $ Set.fromList . List.map (paramName . content) . brOutParams
    let usedVars = Map.filterWithKey
                    (const . (`Set.member` (stmtsIns `Set.union` inOuts `Set.union` outs)))
                    inVars
    next <- newProcCall pname usedVars pos Det -- Continuation procs always Det
    let loopinfo = Just (LoopInfo next break)
    oldLoopinfo <- gets brLoopInfo
    modify (\s -> s { brLoopInfo = loopinfo })
    stmts' <- withVars usedVars $ unbranchStmts stmts
    modify (\s -> s { brLoopInfo = oldLoopinfo })
    proto <- newProcProto pname usedVars res
    genProc proto Det stmts'
    return next

varExp :: FlowDirection -> VarName -> TypeSpec -> Placed Exp
varExp flow var ty
    = Unplaced $ Typed (Var var flow Ordinary) (unbranchType ty) Nothing


newProcCall :: ProcName -> VarDict -> OptPos -> Determinism
            -> Unbrancher (Placed Stmt)
newProcCall name inVars pos detism = do
    let inArgs  = List.map (uncurry $ varExp ParamIn) $ Map.toList inVars
    outArgs <- gets brOutArgs
    currMod <- lift getModuleSpec
    let call = ProcCall (First currMod name (Just 0)) detism False (inArgs ++ outArgs)
    logUnbranch $ "Generating call: " ++ showStmt 4 call
    return $ maybePlace call pos


newProcProto :: ProcName -> VarDict -> Set ResourceSpec -> Unbrancher ProcProto
newProcProto name inVars res = do
    let inParams  = [Unplaced $ unbranchParam $ Param v ty ParamIn Ordinary
                    | (v,ty) <- Map.toList inVars]
    outParams <- gets brOutParams
    return $ ProcProto name (inParams ++ outParams)
           $ Set.map (`ResourceFlowSpec` ParamInOut) res


-- |Return the second value when the detism is SemiDet, otherwise the second.
selectDetism :: a -> a -> Determinism -> a
selectDetism _ semi SemiDet = semi
selectDetism det _  _ = det
