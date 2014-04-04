--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Convert parse tree into AST
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

-- |Support for normalising wybe code as parsed to a simpler form
--  to make compiling easier.
module Normalise (normalise) where

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
import Flatten
import NumberVars

-- |Normalise a list of file items, storing the results in the current module.
normalise :: [Item] -> Compiler ()
normalise items = do
    mapM_ normaliseItem items
    -- Now generate main proc if needed
    bdy <- getCompiler (body . mainClauseSt)
    unless (List.null bdy) 
      $ addProc "" (PrimProto "" []) [List.reverse bdy] Nothing Private
    

-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) items pos) = do
    dir <- getDirectory
    parentmod <- getModuleSpec
    enterModule dir (parentmod ++ [name]) (Just params)
    addType name (TypeDef (length params) pos) vis
    normalise items
    mod <- finishModule
    addSubmod name mod pos vis
    return ()
normaliseItem (ModuleDecl vis name items pos) = do
    dir <- getDirectory
    parentmod <- getModuleSpec
    enterModule dir (parentmod ++ [name]) Nothing
    normalise items
    mod <- finishModule
    addSubmod name mod pos vis
    return ()
normaliseItem (ImportMods vis imp modspecs pos) = do
    mapM_ (\spec -> addImport spec imp Nothing vis) modspecs
normaliseItem (ImportItems vis imp modspec imports pos) = do
    addImport modspec imp (Just imports) vis
normaliseItem (ResourceDecl vis name typ pos) =
  addResource name (SimpleResource typ pos) vis
normaliseItem (FuncDecl vis (FnProto name params) resulttype result pos) =
  normaliseItem $
  ProcDecl 
  vis
  (ProcProto name $ params ++ [Param "$" resulttype ParamOut])
  [Unplaced $ ProcCall "=" [Unplaced $ Var "$" ParamOut, result]
   noVars noVars]
  pos
normaliseItem (ProcDecl vis proto@(ProcProto name params) stmts pos) = do
    let (stmts',tempCtr) = flattenBody stmts
    -- liftIO $ putStrLn $ "Flattened body = " ++ show stmts'
    (initVars,stmts'',finalVars) <- numberVars params stmts' pos
    -- liftIO $ putStrLn $ "Numbered body = " ++ show stmts''
    proto' <- primProto initVars finalVars proto
    (_,procstate) <- userClauseComp $ compileStmts stmts''
    addProc name proto' [List.reverse $ body procstate] pos vis
normaliseItem (CtorDecl vis proto pos) = do
    modspec <- getModuleSpec
    Just modparams <- getModuleParams
    addCtor vis (last modspec) modparams proto
normaliseItem (StmtDecl stmt pos) = do
  clauseState <- getCompiler mainClauseSt
  (_,clauseState') <- runStateT (compileStmts [maybePlace stmt pos])
                      clauseState
  updateCompiler (\m -> m { mainClauseSt = clauseState'})

-- |Add a contructor for the specified type.
addCtor :: Visibility -> Ident -> [Ident] -> FnProto -> Compiler ()
addCtor vis typeName typeParams (FnProto ctorName params) = do
    let typespec = TypeSpec typeName $ List.map (\n->TypeSpec n []) typeParams
    normaliseItem 
      (FuncDecl Public (FnProto ctorName params) typespec
       (Unplaced $ Where 
        ([Unplaced $ ForeignCall "$" "alloc" [Unplaced $ StringValue typeName,
                                              Unplaced $ StringValue ctorName,
                                              Unplaced $ Var "$rec" ParamOut]
           noVars noVars]
         ++
         (List.map (\(Param var _ dir) ->
                     (Unplaced $ ForeignCall "$" "mutate"
                      [Unplaced $ StringValue $ typeName,
                       Unplaced $ StringValue ctorName,
                       Unplaced $ StringValue var,
                       Unplaced $ Var "$rec" ParamInOut,
                       Unplaced $ Var var ParamIn]
                       noVars noVars))
          params))
        (Unplaced $ Var "$rec" ParamIn))
       Nothing)
    mapM_ (addGetterSetter vis typespec ctorName) params

-- |Add a getter and setter for the specified type.
addGetterSetter :: Visibility -> TypeSpec -> Ident -> Param -> Compiler ()
addGetterSetter vis rectype ctorName (Param field fieldtype _) = do
    normaliseItem $ FuncDecl vis 
      (FnProto field [Param "$rec" rectype ParamIn])
      fieldtype 
      (Unplaced $ ForeignFn "$" "access" 
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamIn])
      Nothing
    normaliseItem $ ProcDecl vis 
      (ProcProto field 
       [Param "$rec" rectype ParamInOut,
        Param "$field" fieldtype ParamIn])
      [Unplaced $ ForeignCall "$" "mutate"
       [Unplaced $ StringValue $ typeName rectype,
        Unplaced $ StringValue ctorName,
        Unplaced $ StringValue field,
        Unplaced $ Var "$rec" ParamInOut,
        Unplaced $ Var "$field" ParamIn]
       noVars noVars]
       Nothing

----------------------------------------------------------------
-- |Make a fresh proc with a fresh name
compileFreshProc :: ProcName -> LoopInfo -> VarVers -> VarVers -> 
                    [[Placed Stmt]] -> ClauseComp Stmt
compileFreshProc name loopInfo initVars finalVars clauses = do
  -- liftIO $ putStrLn $ "compiling separate proc:  " ++ show clauses
  -- XXX get list of defined variables; this becomes list of inParams
  -- XXX outParams is this list plus variables defined by all clauses
  results <- mapM (genClauseComp loopInfo) clauses
  let clauses' = List.map (List.reverse . body) results
  -- liftIO $ putStrLn $ "compiled code:  " ++ show clauses'
  if List.all List.null clauses'
    then
      return Nop
    else do
      let inVars = Map.keys initVars
      let outVars = List.filter (not . (sameAtKey initVars finalVars))
                    $ Map.keys finalVars
      let inParams = inferredParams initVars FlowIn inVars
      let outParams = inferredParams finalVars FlowOut outVars
      -- XXX
      let inArgs = inferredArgs initVars ParamIn
      let outArgs = inferredArgs finalVars ParamOut
      lift $ addProc name (PrimProto name (inParams++outParams)) 
        clauses' Nothing Private
      return $ ProcCall name (inArgs++outArgs) initVars finalVars

inferredParams :: VarVers -> PrimFlow -> [VarName] -> [PrimParam]
inferredParams vars flow included =
    List.map (\v -> PrimParam (PrimVarName v (vars!v)) Unspecified flow Ordinary)
    included


inferredArgs :: VarVers -> FlowDirection -> [Placed Exp]
inferredArgs vars flow = do
    List.map (\v -> Unplaced $ Var v flow) $ Map.keys vars


sameAtKey :: (Eq b, Ord a) => Map a b -> Map a b -> a -> Bool
sameAtKey m1 m2 k = (Map.lookup k m1) == (Map.lookup k m2)


-- |Compile a single complete clause, using a fresh ClauseComp monad
genClauseComp :: LoopInfo -> [Placed Stmt] -> ClauseComp ClauseCompState
genClauseComp loopInfo1 clause = do
    tmpNum <- gets tmpCount
    loopInfo0 <- gets loopInfo
    let loopInfo = case loopInfo1 of
            NoLoop -> loopInfo0
            _ -> loopInfo1
    (_,state) <- lift $ runClauseComp tmpNum loopInfo $ compileStmts clause
    return state

-- |Compile the specified statements to primitive statements.
compileStmts :: [Placed Stmt] -> ClauseComp ()
compileStmts [] = return ()
compileStmts (stmt:stmts) = compileStmts' (content stmt) stmts (place stmt)

-- |Compile the specified statement, plus the list of following statements
compileStmts' :: Stmt -> [Placed Stmt] -> Maybe SourcePos -> ClauseComp ()
compileStmts' (ProcCall name args initVars finalVars) rest pos = do
  primArgs <- mapM (\a->primArg (content a) (place a) initVars finalVars) 
              args
  instr (PrimCall name Nothing $ concat primArgs) pos
  compileStmts rest
compileStmts' (ForeignCall lang name args initVars finalVars) rest pos = do
  primArgs <- mapM (\a->primArg (content a) (place a) initVars finalVars) 
              args
  instr (PrimForeign lang name Nothing $ concat primArgs) pos
  compileStmts rest
compileStmts' (Cond exp thn els initVars finalVars) rest pos = do
  switchName <- lift $ genProcName
  switch <- compileFreshProc switchName NoLoop initVars finalVars
            [(Unplaced $ Guard exp 1 initVars finalVars):thn, 
             (Unplaced $ Guard exp 0 initVars finalVars):els]
  compileStmts' switch rest Nothing
compileStmts' (Loop loopBody initVars finalVars) rest pos = do
  loopName <- lift $ genProcName
  loop <- compileFreshProc loopName NoLoop initVars finalVars
              [loopBody++[Unplaced Next]]
  compileStmts' loop rest Nothing
compileStmts' (Guard exp val initVars finalVars) rest pos = do
  parg <- primArg (content exp) (place exp) initVars finalVars
  case parg of
    [ArgVar name FlowIn _] -> instr (PrimGuard name val) pos
    [ArgInt n] ->
      when (n /= val) $ instr PrimFail pos
    _ -> do
      lift $ message Error "Can't use a non-integer type as a Boolean" pos
      instr PrimFail pos
  compileStmts rest
compileStmts' Nop rest pos = compileStmts rest
compileStmts' (For gen initVars finalVars) rest pos = do
    inf <- gets loopInfo
    case inf of
        NoLoop -> lift $ message Error "Loop op outside of a loop" pos
        LoopInfo _ _ _ -> do
            cond <- compileGenerator gen pos
            switchName <- lift $ genProcName
            switch <- compileFreshProc switchName NoLoop initVars finalVars
                      [Unplaced (Guard cond 1 initVars finalVars):rest,
                       [Unplaced $ Guard cond 0 initVars finalVars]]
            compileStmts' switch [] Nothing
compileStmts' Break rest pos = do
    inf <- gets loopInfo
    case inf of
        NoLoop -> lift $ message Error "Loop op outside of a loop" pos
        LoopInfo _ _ _ -> return ()
compileStmts' Next rest pos = do
    inf <- gets loopInfo
    case inf of
        NoLoop -> lift $ message Error "Loop op outside of a loop" pos
        LoopInfo _ _ _ -> return ()
        -- LoopInfo cont _ _ -> do
        --     switchName <- lift $ genProcName
        --     switch <- compileFreshProc switchName
        --               [[Unplaced (Guard cond 1), 
        --                 maybePlace cont pos],
        --                (Unplaced $ Guard cond 0):rest]
        --     compileStmts' switch [] Nothing


-- |Compile an argument into a PrimArg if it's flattened; if not, return Nothing
primArg :: Exp -> OptPos -> VarVers -> VarVers -> ClauseComp [PrimArg]
primArg (IntValue a) pos initVars finalVars = return [ArgInt a]
primArg (FloatValue a) pos initVars finalVars = return [ArgFloat a]
primArg (StringValue a) pos initVars finalVars = return [ArgString a]
primArg (CharValue a) pos initVars finalVars = return [ArgChar a]
primArg (Var name dir) pos initVars finalVars = do
  var <- lift $ flowVar name dir pos initVars finalVars
  return var
primArg exp pos initVars finalVars =
  error $ "Internal error: " ++ show (maybePlace exp pos) ++ 
  " remains after flattening"


-- |Compile a list of expressions as proc call arguments to a list of 
--  primitive arguments, a list of statements to execute before the 
--  call to bind those arguments, and a list of statements to execute 
--  after the call to store the results appropriately.
normaliseArgs :: [Placed Exp] 
                 -> ClauseComp ([Placed Exp],[Placed Stmt],[Placed Stmt],
                                FlowDirection)
normaliseArgs exps = do
  argsResults <- mapM normalisePlacedExp exps
  return $ List.foldr (\(a1,pre1,post1,flow1)(a2,pre2,post2,flow2) -> 
                        (a1++a2,pre1++pre2,post1++post2,flow1 `flowJoin` flow2))
    ([],[],[],NoFlow) argsResults

normalisePlacedExp :: Placed Exp -> ClauseComp ([Placed Exp],[Placed Stmt],
                                                [Placed Stmt], FlowDirection)
normalisePlacedExp pexp = normaliseExp (content pexp) (place pexp)

-- |Normalise a single expressions with specified flow direction to
--  primitive argument(s), a list of statements to execute
--  to bind it, and a list of statements to execute 
--  after the call to store the result appropriately.
--  The first part of the output (a Placed Exp) will always be a list
--  of only atomic Exps and Var references (in any direction).
normaliseExp :: Exp -> Maybe SourcePos
              -> ClauseComp ([Placed Exp],[Placed Stmt],[Placed Stmt],
                             FlowDirection)
normaliseExp exp@(IntValue a) pos = 
  return ([maybePlace exp pos],[],[],ParamIn)
normaliseExp exp@(FloatValue a) pos = 
  return ([maybePlace exp pos],[],[],ParamIn)
normaliseExp exp@(StringValue a) pos = 
  return ([maybePlace exp pos],[],[],ParamIn)
normaliseExp exp@(CharValue a) pos = 
  return ([maybePlace exp pos],[],[],ParamIn)
normaliseExp exp@(Var name dir) pos = 
  return ([maybePlace exp pos],[],[],dir)
normaliseExp (Where stmts exp) _ = do
  (e,pres,posts,flow) <- normaliseExp (content exp) (place exp)
  return (e,stmts++pres,posts,flow)
normaliseExp (CondExp cond thn els) pos = do
  resultName <- freshVar
  return ([Unplaced $ Var resultName ParamIn],
          [maybePlace (Cond cond
                  [Unplaced $ ProcCall "=" 
                   [Unplaced $ Var resultName ParamOut,thn] noVars noVars]
                  [Unplaced $ ProcCall "=" 
                   [Unplaced $ Var resultName ParamOut,els] noVars noVars]
                  noVars noVars) pos],
          [],ParamIn)
normaliseExp (Fncall name exps) pos = do
  resultName <- freshVar
  (args,pres,posts,flow) <- normaliseArgs exps
  let pres' = if flowsIn flow then 
                pres++[maybePlace 
                       (ProcCall name
                        (List.map (fmap inputArg) args
                        ++[Unplaced $ Var resultName ParamOut])
                        noVars noVars)
                       pos]
              else pres
  let posts' = if flowsOut flow then 
                 [maybePlace
                  (ProcCall name
                   (args++[Unplaced $ Var resultName ParamIn])
                   noVars noVars)
                  pos]++posts
               else posts
  return ([Unplaced $ Var resultName flow],pres',posts',flow)
normaliseExp (ForeignFn lang name exps) pos = do
  resultName <- freshVar
  (args,pres,posts,flow) <- normaliseArgs exps
  let pres' = if flowsIn flow then 
                pres++[maybePlace 
                       (ForeignCall lang name
                        (args++[Unplaced $ Var resultName ParamOut])
                        noVars noVars)
                       pos]
              else pres
  let posts' = if flowsOut flow then 
                 posts++[maybePlace 
                         (ForeignCall lang name
                                (args++[Unplaced $ Var resultName ParamIn])
                                noVars noVars)
                         pos]
               else posts
  return ([Unplaced $ Var resultName flow],pres',posts',flow)


-- |Compile a loop generator to three lists of primitive statements:
--  statements to execute before, during, and after the loop.
compileGenerator :: Generator -> Maybe SourcePos -> ClauseComp (Placed Exp)
compileGenerator (In var exp) pos = do
    (args,init,_,_) <- normalisePlacedExp exp
    stateVarName <- freshVar
    let asn = Unplaced $ ProcCall "=" 
              (Unplaced (Var stateVarName ParamOut):args) noVars noVars
    modify (\st -> st { loopInfo = 
                             (loopInfo st) {loopInit = 
                                                 (loopInit $ loopInfo st)
                                                 ++init++[asn]}})
    let stateArg = Unplaced $ Var stateVarName ParamInOut
    let varArg = Unplaced $ Var var ParamOut
    testVarName <- freshVar
    let testArg = Unplaced $ Var testVarName ParamOut
    compileStmts' (ProcCall "next" [stateArg,varArg,testArg] noVars noVars) [] Nothing
    return $ Unplaced $ Var testVarName ParamIn
compileGenerator (InRange var exp updateOp inc limit) pos = do
    (args,init1,_,_) <- normalisePlacedExp exp
    (incArgs,init2,_,_) <- normalisePlacedExp inc
    let asn = Unplaced $ ProcCall "=" 
              (Unplaced (Var var ParamOut):args) noVars noVars
    let varIn = Unplaced $ Var var ParamIn
    let varOut = Unplaced $ Var var ParamOut
    compileStmts' (ProcCall updateOp ([varIn]++incArgs++[varOut]) noVars noVars) [] Nothing
    case limit of
        Nothing -> do
            modify (\st -> st { loopInfo = 
                                     (loopInfo st) {loopInit = 
                                                         (loopInit 
                                                          $ loopInfo st)
                                                         ++init1++init2++[asn]}
                              })
            return $ Unplaced $ IntValue 1
        Just (comp,limit') -> do
            testVarName <- freshVar
            let testArg = Unplaced $ Var testVarName ParamOut
            (limitArgs,init3,_,_) <- normalisePlacedExp limit'
            modify (\st -> st { loopInfo = 
                                     (loopInfo st) {loopInit = 
                                                         (loopInit 
                                                          $ loopInfo st)
                                                         ++init1++init2
                                                         ++init3++[asn]}
                              })
            compileStmts' (ProcCall comp
                           ([varIn]++limitArgs++[testArg]) noVars noVars) [] 
              Nothing
            return $ Unplaced $ Var testVarName ParamIn


-- |Set up a loop with the specified continuation and break calls
initLoop :: Stmt -> ClauseComp ()
initLoop cont = 
    modify (\st -> st { loopInfo = LoopInfo cont [] [] })


----------------------------------------------------------------

-- | Report an error if the specified flow direction has output.
mustBeIn :: FlowDirection -> Maybe SourcePos -> ClauseComp ()
mustBeIn flow pos =
    when (flowsOut flow)
    $ lift $ message Error "Flow error:  invalid output argument" pos

-- |Does the specified flow direction flow in?
flowsIn :: FlowDirection -> Bool
flowsIn NoFlow     = False
flowsIn ParamIn    = True
flowsIn ParamOut   = False
flowsIn ParamInOut = True

-- |Does the specified flow direction flow out?
flowsOut :: FlowDirection -> Bool
flowsOut NoFlow     = False
flowsOut ParamIn = False
flowsOut ParamOut = True
flowsOut ParamInOut = True

inFlow :: FlowDirection -> FlowDirection
inFlow NoFlow     = NoFlow
inFlow ParamIn = ParamIn
inFlow ParamOut = NoFlow
inFlow ParamInOut = ParamIn

inputArg :: Exp -> Exp
inputArg (Var name dir) = Var name $ inFlow dir
inputArg exp = exp

-- |Transform the specified primitive argument to an input parameter.
expIsInput :: Exp -> Bool
expIsInput (Var var dir) = flowsIn dir
-- XXX Shouldn't assume everything but variables are inputs
expIsInput _ = True

-- |Join on the lattice of flow directions (NoFlow is bottom, 
--  ParamInOut is top, and the others are incomparable in between).
flowJoin :: FlowDirection -> FlowDirection -> FlowDirection
flowJoin NoFlow     x          = x
flowJoin x          NoFlow     = x
flowJoin ParamInOut _          = ParamInOut
flowJoin _          ParamInOut = ParamInOut
flowJoin ParamIn    ParamOut   = ParamInOut
flowJoin ParamIn    ParamIn    = ParamIn
flowJoin ParamOut   ParamOut   = ParamOut
flowJoin ParamOut   ParamIn    = ParamInOut
