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
import DefUse

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
  [Unplaced $ ProcCall "=" [Unplaced $ Var "$" ParamOut, result]]
  pos
normaliseItem (ProcDecl vis proto@(ProcProto name params) stmts pos) = do
    let proto'@(PrimProto _ params') = primProto proto
    (_,procstate) <- runClauseComp params' 0 $ compileStmts stmts
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
                                              Unplaced $ Var "$rec" ParamOut]]
         ++
         (List.map (\(Param var _ dir) ->
                     (Unplaced $ ForeignCall "$" "mutate"
                      [Unplaced $ StringValue $ typeName,
                       Unplaced $ StringValue ctorName,
                       Unplaced $ StringValue var,
                       Unplaced $ Var "$rec" ParamInOut,
                       Unplaced $ Var var ParamIn]))
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
        Unplaced $ Var "$field" ParamIn]]
       Nothing

-- -- |Normalise the specified statements to primitive statements.
-- normaliseStmts :: [Placed Stmt] -> ClauseComp [Placed Prim]
-- normaliseStmts [] = return []
-- normaliseStmts (stmt:stmts) = normaliseStmts' (content stmt) stmts $ place stmt

-- -- |Normalise the specified statement, plus the list of following statements, 
-- --  to a list of primitive statements.
-- normaliseStmts' :: Stmt -> [Placed Stmt] -> Maybe SourcePos -> ClauseComp [Placed Prim]
-- normaliseStmts' (ProcCall name args) stmts pos = do
--   (args',pre,post) <- normaliseArgs args
--   back <- normaliseStmts stmts
--   return $ pre ++ [maybePlace (PrimCall name Nothing args') pos] ++ post ++ back
-- normaliseStmts' (ForeignCall lang name args) stmts pos = do
--   (args',pre,post) <- normaliseArgs args
--   back <- normaliseStmts stmts
--   return $ pre ++ [maybePlace (PrimForeign lang name Nothing args') pos] ++ post ++ back
-- normaliseStmts' (Cond exp thn els) stmts pos = do
--   (exp',condstmts) <- normaliseOuterExp exp []
--   thn' <- normaliseStmts thn
--   els' <- normaliseStmts els
--   stmts' <- normaliseStmts stmts
--   normaliseCond exp' condstmts thn' els' stmts' pos
-- normaliseStmts' (Loop loop) stmts pos = do
--   (init,body,update) <- normaliseLoopStmts loop
--   back <- normaliseStmts stmts
--   return $ init ++ [maybePlace (PrimLoop $ body++update) pos] ++ back
-- normaliseStmts' Nop stmts pos = normaliseStmts stmts


-- -- |Normalise a conditional, generating a call to a two-clause proc, 
-- --  where each clause ends with a call to another new proc that 
-- --  handles the rest of the computation after the conditional
-- normaliseCond :: PrimArg 
--                  -> [Placed Prim] 
--                  -> [Placed Prim] 
--                  -> [Placed Prim] 
--                  -> [Placed Prim] 
--                  -> Maybe SourcePos 
--                  -> ClauseComp [Placed Prim]
-- normaliseCond exp' condstmts thn' els' stmts pos = do
--   condproc <- lift $ genProcName
--   confluence <- lift $ genProcName
--   let continuation = if List.null stmts then [] 
--                      else [Unplaced $ PrimCall confluence Nothing []]
--   thenGuard <- lift $ makeGuard exp' 1 pos
--   elseGuard <- lift $ makeGuard exp' 0 pos
--   let thn'' = condstmts ++ thenGuard ++ thn' ++ continuation
--   let els'' = condstmts ++ elseGuard ++ els' ++ continuation
--   lift $ addProc condproc (PrimProto condproc []) [thn'',els''] Nothing Private
--   if List.null stmts then 
--       return () 
--     else 
--       lift $ 
--       addProc confluence (PrimProto confluence []) [stmts] Nothing Private
--   return $ condstmts ++ [Unplaced $ PrimCall condproc Nothing []]



-- -- |Normalise the specified loop statements to primitive statements.
-- normaliseLoopStmts :: [Placed LoopStmt] -> 
--                       ClauseComp ([Placed Prim],[Placed Prim],[Placed Prim])
-- normaliseLoopStmts [] = return ([],[],[])
-- normaliseLoopStmts (stmt:stmts) = do
--   (backinit,backbody,backupdate) <- normaliseLoopStmts stmts
--   (frontinit,frontbody,frontupdate) <- case stmt of
--     Placed stmt' pos -> normaliseLoopStmt stmt' $ Just pos
--     Unplaced stmt'   -> normaliseLoopStmt stmt' Nothing
--   return $ (frontinit ++ backinit, 
--             frontbody ++ backbody,
--             frontupdate ++ backupdate)

-- -- |Normalise a single loop statement to three list of primitive statements:
-- --  statements to execute before, during, and afte the loop.p
-- normaliseLoopStmt :: LoopStmt -> Maybe SourcePos -> 
--                      ClauseComp ([Placed Prim],[Placed Prim],[Placed Prim])
-- normaliseLoopStmt (For gen) pos = normaliseGenerator gen pos
-- normaliseLoopStmt (BreakIf exp) pos = do
--   (exp',stmts) <- normaliseOuterExp exp []
--   condVarName <- freshVar
--   condAssign <- assign condVarName exp'
--   condExp <- getVar condVarName
--   return ([],stmts ++ [condAssign, maybePlace (PrimBreakIf condExp) pos],[])
-- normaliseLoopStmt (NextIf exp) pos = do
--   (exp',stmts) <- normaliseOuterExp exp []
--   condVarName <- freshVar
--   condAssign <- assign condVarName exp'
--   condExp <- getVar condVarName
--   return ([],stmts ++ [condAssign, maybePlace (PrimNextIf condExp) pos],[])
-- normaliseLoopStmt (NormalStmt stmt) pos = do
--   stmts <- normaliseStmts' (content stmt) [] pos
--   return ([],stmts,[])


-- -- |Normalise a loop generator to three list of primitive statements:
-- --  statements to execute before, during, and afte the loop.p
-- normaliseGenerator :: Generator -> Maybe SourcePos ->
--                       ClauseComp ([Placed Prim],[Placed Prim],[Placed Prim])
-- normaliseGenerator (In var exp) pos = do
--   (arg,init) <- normaliseOuterExp exp []
--   stateVar <- freshVar
--   testVarName <- freshVar
--   asn <- assign stateVar arg
--   stateArg <- inOutVar stateVar
--   varArg <- inOutVar var
--   testArg <- outVar testVarName
--   testVar <- getVar testVarName
--   let update = procCall "next" (stateArg ++ varArg ++ testArg)
--   return (init++[asn,update],
--           [update],[Unplaced $ PrimBreakIf testVar])
-- normaliseGenerator (InRange var exp updateOp inc limit) pos = do
--   (arg,init1) <- normaliseOuterExp exp []
--   (incArg,init2) <- normaliseOuterExp inc []
--   varIn <- inVar var
--   varOut <- outVar var
--   let update = [procCall updateOp (varIn ++ [incArg] ++ varOut)]
--   asn <- assign var arg
--   (init,test) <- case limit of
--     Nothing -> return (init1++init2,[])
--     Just (comp,limit') -> do
--       testVarName <- freshVar
--       testArg <- outVar testVarName
--       testVar <- getVar testVarName
--       (limitArg,init3) <- normaliseOuterExp limit' []
--       varArg <- inVar var
--       return (init1++init2++init3,
--               [procCall comp (varArg ++ [limitArg] ++ testArg),
--                Unplaced $ PrimBreakIf testVar])
--   return (init++[asn],test,update)


-- -- |Normalise a list of expressions as proc call arguments to a list of 
-- --  primitive arguments, a list of statements to execute before the 
-- --  call to bind those arguments, and a list of statements to execute 
-- --  after the call to store the results appropriately.
-- normaliseArgs :: [Placed Exp] 
--                  -> ClauseComp ([Exp],[Placed Prim],[Placed Prim])
-- normaliseArgs [] = return ([],[],[])
-- normaliseArgs (pexp:args) = do
--   (arg,pre,post) <- normaliseExp (content pexp) (place pexp)
--   (args',pres,posts) <- normaliseArgs args
--   return (arg ++ args', pre ++ pres, post ++ posts)


-- -- -- |Normalise a single read-only expression to a primitve argument 
-- -- --  and a list of primitive statements to bind that argument.
-- -- normaliseOuterExp :: Placed Exp -> [Placed Prim] -> 
-- --                      ClauseComp (PrimArg,[Placed Prim])
-- -- normaliseOuterExp exp stmts = do
-- --     ([arg],_,pre,post) <- normaliseExp (content exp) (place exp) ParamIn stmts
-- --     return (arg,pre++post)


-- -- |Normalise a single expressions with specified flow direction to
-- --  primitive argument(s), a list of statements to execute
-- --  to bind it, and a list of statements to execute 
-- --  after the call to store the result appropriately.
-- normaliseExp :: Exp -> Maybe SourcePos ->
--                 ClauseComp (Exp,FlowDirection,[Placed Prim],[Placed Prim])
-- normaliseExp exp@(IntValue a) pos = return (exp,[],[])
-- normaliseExp exp@(FloatValue a) pos dir rest = do
--   mustBeIn dir pos
--   return ([ArgFloat a], ParamIn, [], rest)
-- normaliseExp (StringValue a) pos dir rest = do
--   mustBeIn dir pos
--   return ([ArgString a], ParamIn, [], rest)
-- normaliseExp (CharValue a) pos dir rest = do
--   mustBeIn dir pos
--   return ([ArgChar a], ParamIn, [], rest)
-- normaliseExp (Var name dir) pos _ rest = do
--   args <- flowVar name dir
--   return (args, dir, [], rest)
-- normaliseExp (Where stmts exp) pos dir rest = do
--   mustBeIn dir pos
--   stmts1 <- normaliseStmts stmts
--   (exp',stmts2) <- normaliseOuterExp exp []
--   return ([exp'], ParamIn, stmts1++stmts2, rest)
-- normaliseExp (CondExp cond thn els) pos dir rest = do
--   mustBeIn dir pos
--   (cond',stmtscond) <- normaliseOuterExp cond []
--   (thn',stmtsthn) <- normaliseOuterExp thn []
--   resultVar <- freshVar
--   thnAssign <- assign resultVar thn'
--   (els',stmtsels) <- normaliseOuterExp els []
--   elsAssign <- assign resultVar els'
--   result <- inVar resultVar
--   body <- normaliseCond cond' stmtscond 
--           (stmtsthn++[thnAssign]) (stmtsels++[elsAssign]) rest pos
--   return (result, ParamIn, body, [])
-- normaliseExp (Fncall name exps) pos dir rest = do
--   mustBeIn dir pos
--   (exps',dir',pre,post) <- normalisePlacedExps exps rest
--   let inexps = List.filter argIsInput exps'
--   resultName <- freshVar
--   let dir'' = dir `flowJoin` dir'
--   pre' <- if flowsIn dir'' 
--           then do
--               resultOut <- outVar resultName
--               let args = inexps++resultOut
--               let instr = maybePlace (PrimCall name Nothing args) pos
--               return $ pre ++ [instr]
--           else return pre
--   post' <- if flowsOut dir''
--            then do
--                resultIn <- inVar resultName
--                let args = exps'++resultIn
--                let instr = maybePlace (PrimCall name Nothing args) pos
--                return $ instr:post
--            else return $ post
--   result <- flowVar resultName dir'' -- XXX shouldn't ignore list tail
--   return (result, dir'', pre', post')
-- normaliseExp (ForeignFn lang name exps) pos dir rest = do
--   mustBeIn dir pos
--   (exps',_,pre,post) <- normalisePlacedExps exps rest
--   resultName <- freshVar
--   resultIn <- inVar resultName
--   resultOut <- outVar resultName
--   let args = exps'++resultOut
--   let pre' = pre ++ [maybePlace (PrimForeign lang name Nothing args) pos]
--   return (resultIn, ParamIn, pre', post)

----------------------------------------------------------------
-- |Make a fresh proc with a fresh name
compileFreshProc :: ProcName -> [[Placed Stmt]] -> ClauseComp Stmt
compileFreshProc name clauses = do
  -- liftIO $ putStrLn $ "compiling separate proc:  " ++ show clauses
  tmpNum <- gets tmpCount
  results <- mapM (compileClause (return ()) tmpNum) clauses
  let clauses' = List.map (List.reverse . body) results
  -- liftIO $ putStrLn $ "compiled code:  " ++ show clauses'
  if List.all List.null clauses'
    then
      return Nop
    else do
      let inMap = Map.unions $ List.map uses results
      -- liftIO $ putStrLn $ "generating proc " ++ name 
      --   ++ " with args " ++ show inMap
      let inVars = Map.keys inMap
      -- liftIO $ putStrLn $ "used vars:  " ++ show inVars
      outParams <- gets outParams
      -- liftIO $ putStrLn $ "out params:  " ++ show outParams
      inParams <- mapM 
                  (\n -> do 
                        inf <- gets (Map.lookup n . vars)
                        let thistype = maybe Unspecified typ inf
                        let num = maybe 0 ordinal inf
                        return $ PrimParam (PrimVarName n num) thistype 
                          FlowIn Ordinary)
                  inVars
      let inArgs = List.map (\(n,_) -> Unplaced $ Var n ParamIn) $ assocs inMap
      let outArgs = List.map (\n -> Unplaced $ Var n ParamOut)
                    $ List.map (primVarName . paramName) outParams
      lift $ addProc name (PrimProto name (inParams++outParams)) 
        clauses' Nothing Private
      return $ ProcCall name (inArgs++outArgs)

-- |Compile a single complete clause, using a fresh ClauseComp monad
compileClause :: ClauseComp () -> Int -> [Placed Stmt] 
                 -> ClauseComp ClauseCompState
compileClause init tmpNum clause = do
    (_,state) <- extendClauseComp
                 (do                     
                       init
                       compileStmts clause
                 )
    return state

-- |Compile the specified statements to primitive statements.
compileStmts :: [Placed Stmt] -> ClauseComp ()
compileStmts [] = return ()
compileStmts (stmt:stmts) = compileStmts' (content stmt) stmts (place stmt)

-- |Compile the specified statement, plus the list of following statements
compileStmts' :: Stmt -> [Placed Stmt] -> Maybe SourcePos 
                 -> ClauseComp ()
compileStmts' (ProcCall name args) rest pos = do
  primArgs <- mapM (\a->primArg (content a) (place a)) args
  if List.all isJust primArgs
    then do
      instr (PrimCall name Nothing $ concat $ List.map fromJust primArgs) pos
      compileStmts rest
    else do
      (args'',pre,post,_) <- normaliseArgs args
      compileStmts $ 
        pre ++ [maybePlace (ProcCall name args'') pos] ++ post ++ rest
compileStmts' (ForeignCall lang name args) rest pos = do
  primArgs <- mapM (\a->primArg (content a) (place a)) args
  if List.all isJust primArgs
    then do
      instr (PrimForeign lang name Nothing 
             $ concat $ List.map fromJust primArgs) pos
      compileStmts rest
    else do
      (args'',pre,post,_) <- normaliseArgs args
      compileStmts $ 
        pre ++ [maybePlace (ForeignCall lang name args'') pos] ++ post ++ rest
compileStmts' (Cond exp thn els) rest pos = do
  -- XXX bug:  reports uninitialised variables for many vars 
  -- referenced in confluence, because they are not known to outer 
  -- monad.  Will need to report errors here, not in compileVarRef.
  switchName <- lift $ genProcName
  switch <- compileFreshProc switchName
            [(Unplaced $ Guard exp 1):thn, (Unplaced $ Guard exp 0):els]
  compileStmts' switch rest Nothing
compileStmts' (Loop loop) rest pos = do
  -- afterName <- lift $ genProcName
  -- let (_,afterUsed) = pstmtsDefUse rest
  -- let afterCall = ProcCall afterName 
  --                 $ [Unplaced $ Var name ParamIn | name <- Set.elems afterUsed]
  loopName <- lift $ genProcName
  let (_,loopUsed) = pstmtsDefUse loop
  liftIO $ putStrLn $ "Loop " ++ loopName ++ " body = " ++ show loop
  liftIO $ putStrLn $ "Loop vars = " ++ show loopUsed
  let loopCall = ProcCall loopName 
                 $ [Unplaced $ Var name ParamIn | name <- Set.elems loopUsed]
  tmpNum <- gets tmpCount
  bodyComp <- compileClause (initLoop loopCall) tmpNum
             (loop++[Unplaced loopCall]) 
  -- XXX need to specify type of params
  lift $ addProc loopName (PrimProto loopName [])
-- XXX need to specify params
                           -- [PrimParam (PrimVarName name 0) Unspecified 
                           --  FlowIn Ordinary
                           -- | name <- Set.elems afterUsed])
        [(List.reverse $ body bodyComp)] Nothing Private
  let init = loopInit $ loopInfo bodyComp
  let term = loopTerm $ loopInfo bodyComp
  -- after <- compileFreshProc afterName [term++rest]
  compileStmts (init ++ [Unplaced loopCall] ++ term ++ rest)
compileStmts' (Guard exp val) rest pos = do
  parg <- primArg (content exp) (place exp)
  if isJust parg then do
    case fromJust parg of
      [ArgVar name FlowIn _] -> instr (PrimGuard name val) pos
      [ArgInt n] ->
        when (n /= val) $ instr PrimFail pos
      _ -> do
        lift $ message Error "Can't use a non-integer type as a Boolean" pos
        instr PrimFail pos
    compileStmts rest
    else do
    ([exp'],pre,post,_) <- normalisePlacedExp exp
    compileStmts $ 
      pre ++ [maybePlace (Guard exp' val) pos] ++ post ++ rest
compileStmts' Nop rest pos = compileStmts rest
compileStmts' (For gen) rest pos = do
    inf <- gets loopInfo
    case inf of
        NoLoop -> lift $ message Error "Loop op outside of a loop" pos
        LoopInfo _ _ _ -> do
            cond <- compileGenerator gen pos
            switchName <- lift $ genProcName
            switch <- compileFreshProc switchName
                      [Unplaced (Guard cond 1):rest,
                       [Unplaced $ Guard cond 0]]
            compileStmts' switch [] Nothing
compileStmts' (BreakIf cond) rest pos = do
    inf <- gets loopInfo
    case inf of
        NoLoop -> lift $ message Error "Loop op outside of a loop" pos
        LoopInfo _ _ _ -> do
            switchName <- lift $ genProcName
            switch <- compileFreshProc switchName
                      [[Unplaced (Guard cond 1)],
                       (Unplaced $ Guard cond 0):rest]
            compileStmts' switch [] Nothing
compileStmts' (NextIf cond) rest pos = do
    inf <- gets loopInfo
    case inf of
        NoLoop -> lift $ message Error "Loop op outside of a loop" pos
        LoopInfo cont _ _ -> do
            switchName <- lift $ genProcName
            switch <- compileFreshProc switchName
                      [[Unplaced (Guard cond 1), 
                        maybePlace cont pos],
                       (Unplaced $ Guard cond 0):rest]
            compileStmts' switch [] Nothing


-- |Compile an argument into a PrimArg if it's flattened; if not, return Nothing
primArg :: Exp -> OptPos -> ClauseComp (Maybe [PrimArg])
primArg (IntValue a) pos = return $ Just [ArgInt a]
primArg (FloatValue a) pos = return $ Just [ArgFloat a]
primArg (StringValue a) pos = return $ Just [ArgString a]
primArg (CharValue a) pos = return $ Just [ArgChar a]
primArg (Var name dir) pos = do
  var <- flowVar name dir pos
  return $ Just var
primArg _ pos = return Nothing


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
                   [Unplaced $ Var resultName ParamOut,thn]]
                  [Unplaced $ ProcCall "=" 
                   [Unplaced $ Var resultName ParamOut,els]]) pos],
          [],ParamIn)
normaliseExp (Fncall name exps) pos = do
  resultName <- freshVar
  (args,pres,posts,flow) <- normaliseArgs exps
  let pres' = if flowsIn flow then 
                pres++[maybePlace 
                       (ProcCall name $
                        List.map (mapPlaced inputArg) args
                        ++[Unplaced $ Var resultName ParamOut])
                       pos]
              else pres
  let posts' = if flowsOut flow then 
                 [maybePlace
                  (ProcCall name $
                   args++[Unplaced $ Var resultName ParamIn])
                  pos]++posts
               else posts
  return ([Unplaced $ Var resultName flow],pres',posts',flow)
normaliseExp (ForeignFn lang name exps) pos = do
  resultName <- freshVar
  (args,pres,posts,flow) <- normaliseArgs exps
  let pres' = if flowsIn flow then 
                pres++[maybePlace 
                       (ForeignCall lang name $
                        args++[Unplaced $ Var resultName ParamOut])
                       pos]
              else pres
  let posts' = if flowsOut flow then 
                 posts++[maybePlace 
                         (ForeignCall lang name $
                                args++[Unplaced $ Var resultName ParamIn])
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
              (Unplaced (Var stateVarName ParamOut):args)
    modify (\st -> st { loopInfo = 
                             (loopInfo st) {loopInit = 
                                                 (loopInit $ loopInfo st)
                                                 ++init++[asn]}})
    let stateArg = Unplaced $ Var stateVarName ParamInOut
    let varArg = Unplaced $ Var var ParamOut
    testVarName <- freshVar
    let testArg = Unplaced $ Var testVarName ParamOut
    compileStmts' (ProcCall "next" [stateArg,varArg,testArg]) [] Nothing
    return $ Unplaced $ Var testVarName ParamIn
compileGenerator (InRange var exp updateOp inc limit) pos = do
    (args,init1,_,_) <- normalisePlacedExp exp
    (incArgs,init2,_,_) <- normalisePlacedExp inc
    let asn = Unplaced $ ProcCall "=" 
              (Unplaced (Var var ParamOut):args)
    let varIn = Unplaced $ Var var ParamIn
    let varOut = Unplaced $ Var var ParamOut
    compileStmts' (ProcCall updateOp ([varIn]++incArgs++[varOut])) [] Nothing
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
            compileStmts' (ProcCall comp ([varIn]++limitArgs++[testArg])) [] 
              Nothing
            return $ Unplaced $ Var testVarName ParamIn


compileVarRef :: (VarName,OptPos) -> ClauseComp PrimArg
compileVarRef (var,pos) = do
    inf <- gets (Map.lookup var . vars)
    case inf of
        Nothing -> do
            lift $ message Error ("Unintitialised variable " ++ var) pos
            return $ ArgVar (PrimVarName var 0) FlowIn Ordinary
        Just (VarInfo vname num _) ->
            return $ ArgVar (PrimVarName vname num) FlowIn Ordinary

compileVarDef :: VarName -> ClauseComp PrimArg
compileVarDef var = do
    inf <- gets (Map.lookup var . vars)
    case inf of
        Nothing -> do
            lift $ message Error ("Undefined variable " ++ var) Nothing
            return $ ArgVar (PrimVarName var 0) FlowOut Ordinary
        Just (VarInfo vname num _) ->
            return $ ArgVar (PrimVarName vname num) FlowOut Ordinary

-- |Set up a loop with the specified continuation and break calls
initLoop :: Stmt -> ClauseComp ()
initLoop cont = 
    modify (\st -> st { loopInfo = LoopInfo cont [] [] })


----------------------------------------------------------------

-- -- |Normalise a list of expressions as function call arguments to a list of 
-- --  primitive arguments; a flow direction summarising whether there 
-- --  are any inputs and any outputs among the function arguments;
-- --  a list of statements to execute before the 
-- --  call to bind those arguments, and a list of statements to execute 
-- --  after the call to store the results appropriately.
-- normalisePlacedExps :: [Placed Exp] -> [Placed Prim] ->
--                       ClauseComp ([PrimArg],FlowDirection,
--                                   [Placed Prim],[Placed Prim])
-- normalisePlacedExps [] rest = return ([],NoFlow,[],rest)
-- normalisePlacedExps (exp:exps) rest = do
--   (args',flow',pres,posts) <- normalisePlacedExps exps rest
--   (exp',flow,pre,post) <- normaliseExp (content exp) (place exp) ParamIn []
--   return  (exp' ++ args', flow `flowJoin` flow', pre ++ pres, post ++ posts)

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

-- -- |Generate a primitive assignment statement.
-- assign :: VarName -> PrimArg -> ClauseComp (Placed Prim)
-- assign var val = do
--   lval <- outVar var
--   return $ procCall "=" (lval ++ [val])

-- -- |Generate a primitive proc call
-- procCall :: ProcName -> [PrimArg] -> Placed Prim
-- procCall proc args = Unplaced $ PrimCall proc Nothing args

-- -- |Generate a primitive conditional.
-- makeGuard :: PrimArg -> Integer -> Maybe SourcePos -> ClauseComp ()
-- makeGuard arg val pos = do
--   case arg of
--     ArgVar name FlowIn _ -> instr (PrimGuard name val) pos
--     ArgInt n ->
--       when (n /= val) $ instr PrimFail pos
--     _ -> do
--       lift $ message Error "Can't use a non-integer type as a Boolean" pos
--       instr PrimFail pos


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
