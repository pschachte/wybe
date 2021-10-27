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
import Debug.Trace
import Snippets
import Config
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

unbranchProc :: ProcDef -> Int -> Compiler ProcDef
unbranchProc proc _ = unbranchProc' Nothing proc


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
        unbranchBody loopinfo tmpCtr params' detism stmts alt
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

-- |A synthetic output parameter carrying the test result
testOutParam :: Param
testOutParam = Param outputStatusName boolType ParamOut $ Implicit Nothing

-- |The output exp we use to hold the success/failure of a test proc.
testOutExp :: Exp
testOutExp = boolVarSet outputStatusName

-- -- |The input exp we use to hold the success/failure of a test proc.
testInExp :: Exp
testInExp = boolVarGet outputStatusName


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
        outArgs   = [Unplaced $ Typed (varSet nm) ty Nothing
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
setVars :: VarDict -> Unbrancher (VarDict)
setVars vars = do
    oldVars <- gets brVars
    modify (\s -> s { brVars = vars })
    return oldVars


-- |Execute an unbrancher with brVars temporarily set as specified
withVars :: VarDict -> Unbrancher a -> Unbrancher a
withVars vars unbrancher = do
    oldVars <- setVars vars
    unbrancher <* setVars oldVars


-- |Generate a fresh proc name that does not collide with any proc in the
-- current module.
newProcName :: Unbrancher String
newProcName = lift genProcName


-- |Create, unbranch, and record a new proc with the specified proto and body.
genProc :: ProcProto -> Determinism -> [Placed Stmt] -> Unbrancher ()
genProc proto detism stmts = do
    let name = procProtoName proto
    tmpCtr <- gets brTempCtr
    -- call site count will be refilled later
    let procDef = ProcDef name proto (ProcDefSrc stmts) Nothing tmpCtr 0
                  Map.empty Private detism MayInline Pure NoSuperproc
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
    logUnbranch $ "Unbranching an empty " ++ show detism ++ " body"
    return []
unbranchStmts detism (stmt:stmts) alt sense = do
    vars <- gets brVars
    logUnbranch $ "unbranching " ++ show detism ++ " stmt"
        ++ "\n    " ++ showStmt 4 (content stmt)
        ++ "\n  with vars " ++ showVarMap vars
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
unbranchStmt _ stmt@(ProcCall _ _ True args) _ _ _ _ =
    shouldnt $ "Resources should have been handled before unbranching: "
               ++ showStmt 4 stmt
unbranchStmt context stmt@(ProcCall _ SemiDet _ _) _ _ _ _
  | context < SemiDet
  = shouldnt $ "SemiDet proc call " ++ show stmt
               ++ " in a " ++ show context ++ " context"
unbranchStmt SemiDet stmt@(ProcCall func SemiDet _ args) pos
             stmts alt sense = do
    logUnbranch $ "converting SemiDet proc call" ++ show stmt
    testResultVar <- tempVar
    let args' = args ++ [Unplaced (boolVarSet testResultVar)]
    args'' <- defArgsHoistClosures args'
    condVars <- gets brVars
    stmts' <- unbranchStmts SemiDet stmts alt sense
    let val = boolVarGet testResultVar
    vars <- gets brVars
    logUnbranch $ "mkCond " ++ show sense ++ " " ++ show val
                  ++ showBody 4 stmts' ++ "\nelse"
                  ++ showBody 4 alt
    func' <- case func of
                First{} -> return func
                Higher fn -> do
                    [fn'] <- defArgsHoistClosures [fn]
                    return $ Higher fn'
    let result = maybePlace (ProcCall func' Det False args'') pos
                 : mkCond sense val pos stmts' alt condVars vars
    logUnbranch $ "#Converted SemiDet proc call" ++ show stmt
    logUnbranch $ "#To: " ++ showBody 4 result
    return result
unbranchStmt detism stmt@(ProcCall func calldetism r args) pos stmts alt
             sense = do
    logUnbranch $ "Unbranching call " ++ showStmt 4 stmt
    args' <- defArgsHoistClosures args
    func' <- case func of
                First m n pId -> return func
                Higher fn -> do
                    [fn'] <- defArgsHoistClosures [fn]
                    return $ Higher fn'
    let stmt' = ProcCall func' calldetism r args'
    case calldetism of
      Terminal -> return [maybePlace stmt' pos] -- no execution after Terminal
      Failure  -> return [maybePlace stmt' pos] -- no execution after Failure
      Det      -> leaveStmtAsIs detism stmt' pos stmts alt sense
      SemiDet  -> shouldnt "SemiDet case already covered!"
unbranchStmt detism stmt@(ForeignCall l nm fs args) pos stmts alt sense = do
    logUnbranch $ "Unbranching foreign call " ++ showStmt 4 stmt
    args' <- defArgsHoistClosures args
    let stmt' = ForeignCall l nm fs args'
    leaveStmtAsIs detism stmt' pos stmts alt sense
unbranchStmt detism stmt@(TestBool val) pos stmts alt sense = do
    ifSemiDet detism (showStmt 4 stmt ++ " in a Det context")
    $ do
      condVars <- gets brVars
      logUnbranch $ "Unbranching a non-final primitive test " ++ show stmt
      stmts' <- unbranchStmts SemiDet stmts alt sense
      vars <- gets brVars
      logUnbranch $ "mkCond " ++ show sense ++ " " ++ show val
                    ++ showBody 4 stmts' ++ "\nelse"
                    ++ showBody 4 alt
      let result = mkCond sense val Nothing stmts' alt condVars vars
      logUnbranch $ "#Unbranched non-final primitive test " ++ show stmt
      logUnbranch $ "#To: " ++ showBody 4 result
      return result
unbranchStmt detism stmt@(And conj) pos stmts alt sense =
    ifSemiDet detism ("Conjunction in a Det context: " ++ show stmt)
    $ do
      logUnbranch $ "Unbranching conjunction " ++ show stmt
      unbranchStmts SemiDet (conj ++ stmts) alt sense
unbranchStmt detism stmt@(Or disjs exitVars) _ stmts alt sense = do
    ifSemiDet detism ("Disjunction in a Det context: " ++ show stmt)
    $ do
      let exitVars' = trustFromJust "unbranching Disjunction without exitVars"
                      exitVars
      logUnbranch $ "Unbranching disjunction " ++ show stmt
      logUnbranch $ "Following disjunction: " ++ showBody 4 stmts
      logUnbranch $ "Disjunction alternative: " ++ showBody 4 alt
      stmts' <- maybeFactorContinuation SemiDet exitVars' stmts alt sense
      logUnbranch $ "Disjunction successor: " ++ showBody 4 stmts'
      unbranchStmts SemiDet (disjs ++ alt) stmts' (not sense)
unbranchStmt detism stmt@(Not tst) pos stmts alt sense =
    ifSemiDet detism ("Negation in a Det context: " ++ show stmt)
    $ do
        logUnbranch "Unbranching negation"
        placedApply (unbranchStmt SemiDet) tst stmts alt (not sense)
unbranchStmt detism (Cond tst thn els condVars exitVars) pos stmts alt sense =do
    let condVars' = trustFromJust "unbranching Cond without condVars" condVars
    let exitVars' = trustFromJust "unbranching Cond without exitVars" exitVars
    stmts'' <- maybeFactorContinuation detism exitVars' stmts alt sense
    beforeCondVars <- gets brVars
    -- Update known vars to include vars generated by condition
    modify $ \s -> s { brVars = condVars' }
    thn' <- unbranchStmts detism (thn ++ stmts'') alt sense
    -- Update known vars back to state before condition (must have failed)
    modify $ \s -> s { brVars = beforeCondVars }
    els' <- unbranchStmts detism (els ++ stmts'') alt sense
    placedApply (unbranchStmt SemiDet) tst thn' els' True
unbranchStmt detism (Loop body exitVars) pos stmts alt sense = do
    let exitVars' = trustFromJust "unbranching Loop without exitVars" exitVars
    logUnbranch $ "Handling loop:" ++ showBody 4 body
    beforeVars <- gets brVars
    logUnbranch $ "  with entry vars " ++ showVarMap beforeVars
    brk <- maybeFactorContinuation detism exitVars' stmts alt sense
    logUnbranch $ "Generated break: " ++ showBody 4 brk
    next <- factorLoopProc brk beforeVars pos detism body alt sense
    logUnbranch $ "Generated next " ++ showStmt 4 (content next)
    logUnbranch "Finished handling loop"
    return [next]
unbranchStmt _ (UseResources _ _ _) _ _ _ _ =
    shouldnt "resource handling should have removed use ... in statements"
unbranchStmt _ (For _ body) _ _ _ _ =
    shouldnt "flattening should have removed For statements"
unbranchStmt detism Nop _ stmts alt sense = do
    logUnbranch "Unbranching a Nop"
    unbranchStmts detism stmts alt sense     -- might as well filter out Nops
unbranchStmt detism Fail pos stmts alt sense = do
    logUnbranch "Unbranching a Fail"
    return [maybePlace Fail pos] -- no execution after Fail
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
ifSemiDet SemiDet _ code = code
ifSemiDet _ msg _ = shouldnt msg


unbranchDisjunction :: [Placed Stmt] -> OptPos -> [Placed Stmt] -> [Placed Stmt]
                    -> Unbrancher [Placed Stmt]
unbranchDisjunction disjs pos stmts alt = nyi "Disjunction"


-- | Create a Cond statement, unless it can be simplified away.
mkCond :: Bool -> Exp -> OptPos -> [Placed Stmt] -> [Placed Stmt]
       -> VarDict -> VarDict -> [Placed Stmt]
mkCond False tst pos thn els condVars vars =
    mkCond True tst pos els thn condVars vars
mkCond True (IntValue 0) pos thn els condVars vars = els
mkCond True (Typed (IntValue 0) _ _) pos thn els condVars vars = els
mkCond True (IntValue 1) pos thn els condVars vars = thn
mkCond True (Typed (IntValue 1) _ _) pos thn els condVars vars = thn
mkCond True exp pos thn els condVars vars
  | thn == els = thn
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
                   else maybePlace
                        (Cond test thn els (Just condVars) (Just vars)) pos]
      _ -> [maybePlace (Cond test thn els (Just condVars) (Just vars)) pos]
  where test = Unplaced $ TestBool exp


-- |Convert a list of the final statements of a proc body into a short list of
-- statements by turning them into a fresh proc if necessary.  The resulting
-- statement list will have been unbranched.
maybeFactorContinuation :: Determinism -> VarDict -> [Placed Stmt]
                        -> [Placed Stmt] -> Bool -> Unbrancher [Placed Stmt]
maybeFactorContinuation detism vars stmts alt sense = do
    logUnbranch $ "Maybe factor " ++ show detism ++ " continuation: "
                  ++ showBody 4 stmts
    logUnbranch $ "  with brVars: " ++ showVarMap vars
    withVars vars
      $ if length stmts <= 2 && all (flatStmt . content) stmts
        then unbranchStmts detism stmts alt sense
        else (:[]) <$> factorContinuationProc vars Nothing detism
                                              stmts alt sense


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


-- |Add all output arguments of a param list to the symbol table
--  and hoist all closures
defArgsHoistClosures :: [Placed Exp] -> Unbrancher [Placed Exp]
defArgsHoistClosures args = do
    mapM_ (defArg . content) args
    mapM (placedApply $ hoistClosure False) args


-- |Add the output variables defined by the expression to the symbol
--  table. Since the expression is already flattened (excluding lambdas), 
--  it will only be a constant, in which case it doesn't define any variables, 
--  or a variable, in which case it might.
defArg :: Exp -> Unbrancher ()
defArg = ifIsVarDef defVar (return ())


hoistClosure :: Bool -> Exp -> OptPos -> Unbrancher (Placed Exp)
hoistClosure isRef (Typed exp ty cast) pos = do
    exp' <- content <$> hoistClosure isRef exp Nothing
    return $ maybePlace (Typed exp' ty cast) pos
hoistClosure isRef exp@(Lambda mods params pstmts) pos = do
    logUnbranch $ "Creating procref for " ++ show exp
    let ProcModifiers detism inlining impurity resourceful unknown conflict = mods
    lift $ checkConflictingMods "anonymous procedure" pos unknown
    lift $ checkUnknownMods "anonymous procedure" pos conflict
    name <- newProcName
    let holeVars = paramToHoleVar <$> params
    logUnbranch $ "  With params " ++ show holeVars
    let stmtVars = foldStmts const ((. expInputs) . Set.union) Set.empty pstmts
    defd <- gets (Set.toList . Set.filter (flip Set.member stmtVars . fst)
                             . Set.fromList . Map.toList . brVars)
    let (closedParams, closedVars) = if isRef then ([], [])
                                     else unzip $ uncurry closedParamVar <$> defd
    let env = Just closedParams
    logUnbranch $ "  With closed variables " ++ show closedVars

    tmpCtr <- gets brTempCtr
    let procProto = ProcProto name (closedParams ++ params) Set.empty
    let pDefRegular = ProcDef name procProto (ProcDefSrc pstmts) Nothing tmpCtr 0
                      Map.empty Private detism Inline Pure NoSuperproc
    pDefRegular' <- lift $ unbranchProc pDefRegular tmpCtr
    logUnbranch $ "  Resultant regular proc: " ++ show procProto
    procSpec@ProcSpec{procSpecMod=mod,procSpecName=nm,procSpecID=procId}
        <- lift (addProcDef pDefRegular')
    let detism' = selectDetism detism Det detism
    let params' = setParamType intType <$> params 
                    ++ [testOutParam{paramType=intType, paramFlowType=Hole} 
                       | detism == SemiDet]
    let holeVars' = paramToHoleVar <$> params'
    let pDefClosure =
            ProcDef name procProto{procProtoParams=closedParams ++ params'}
            (ProcDefSrc
                $ Unplaced <$>
                    ProcCall (First mod nm (Just procId)) detism' False
                        ((Unplaced <$> closedVars) ++ holeVars')
                    :[ ForeignCall "lpvm" "cast" []
                         [var ParamIn ty, var ParamOut intType]
                    | Typed (Var nm fl a) ty cast <- (content <$> holeVars)
                                                  ++ [testInExp | detism == SemiDet]
                    , flowsOut fl && ty /= intType
                    , let var f t = Unplaced $ Typed (Var nm f a) t cast])
            Nothing tmpCtr 0
            Map.empty Private detism' Inline Pure (ClosureOf procSpec)
    pDefClosure' <- lift $ unbranchProc pDefClosure tmpCtr
    closureProcSpec <- lift (addProcDef pDefClosure')
    return $ maybePlace (ProcRef closureProcSpec closedVars) pos
hoistClosure _ (ProcRef ps@(ProcSpec m nm pID _) []) pos = do
    ProcDef{procDetism=detism, procInlining=inlining, procImpurity=impurity,
            procProto=ProcProto{procProtoParams=params}} 
        <- lift $ getProcDef ps
    let mods = ProcModifiers detism inlining impurity Resourceless [] []
    hoistClosure True (Lambda mods (setParamArgFlowType Hole <$> params)  
                            [Unplaced $ ProcCall (First m nm $ Just pID) detism False 
                                      $ paramToHoleVar <$> params]) pos 
hoistClosure _ exp@(ProcRef ps _) pos = shouldnt $ "hoist closure of " ++ show exp 
hoistClosure _ exp pos = return $ maybePlace exp pos



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
    logUnbranch $ "Factoring " ++ show detism ++ " continuation proc "
                  ++ pname ++ ":" ++ showBody 4 stmts
    stmts' <- unbranchStmts detism stmts alt sense
    proto <- newProcProto pname inVars
    genProc proto Det stmts' -- Continuation procs are always Det
    newProcCall pname inVars pos Det


-- |Generate a fresh proc with all the vars in the supplied dictionary
--  as inputs, and all the output params of the proc we're unbranching as
--  outputs.  Then return a call to this proc with the same inputs and outputs.
factorLoopProc :: [Placed Stmt] -> VarDict -> OptPos -> Determinism
               -> [Placed Stmt] -> [Placed Stmt] -> Bool
               -> Unbrancher (Placed Stmt)
factorLoopProc break inVars pos detism stmts alt sense = do
    pname <- newProcName
    logUnbranch $ "Factoring " ++ show detism ++ " loop proc "
                  ++ pname ++ ":" ++ showBody 4 stmts
                  ++ "\nLoop input vars = " ++ show inVars
    next <- newProcCall pname inVars pos Det -- Continuation procs always Det
    let loopinfo = Just (LoopInfo next break)
    oldLoopinfo <- gets brLoopInfo
    modify (\s -> s { brLoopInfo = loopinfo })
    stmts' <- withVars inVars $ unbranchStmts detism stmts alt sense
    modify (\s -> s { brLoopInfo = oldLoopinfo })
    proto <- newProcProto pname inVars
    genProc proto Det stmts'
    return next

varExp :: FlowDirection -> VarName -> TypeSpec -> Placed Exp
varExp flow var ty = Unplaced $ Typed (Var var flow Ordinary) ty Nothing


newProcCall :: ProcName -> VarDict -> OptPos -> Determinism
            -> Unbrancher (Placed Stmt)
newProcCall name inVars pos detism = do
    let inArgs  = List.map (uncurry $ varExp ParamIn) $ Map.toList inVars
    outArgs <- gets brOutArgs
    currMod <- lift getModuleSpec
    let call = ProcCall (First currMod name (Just 0)) detism False (inArgs ++ outArgs)
    logUnbranch $ "Generating call: " ++ showStmt 4 call
    return $ maybePlace call pos


newProcProto :: ProcName -> VarDict -> Unbrancher ProcProto
newProcProto name inVars = do
    let inParams  = [Param v ty ParamIn Ordinary
                    | (v,ty) <- Map.toList inVars]
    outParams <- gets brOutParams
    return $ ProcProto name (inParams ++ outParams) Set.empty


-- |Return the second value when the detism is SemiDet, otherwise the second.
selectDetism :: a -> a -> Determinism -> a
selectDetism _ semi SemiDet = semi
selectDetism det _  _ = det
