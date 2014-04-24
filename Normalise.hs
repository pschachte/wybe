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
import Unbranch
import NumberVars

-- |Normalise a list of file items, storing the results in the current module.
normalise :: [Item] -> Compiler ()
normalise items = do
    mapM_ normaliseItem items
    -- Now generate main proc if needed
    stmts <- gets stmtDecls
    unless (List.null stmts)
      $ normaliseItem (ProcDecl Private (ProcProto "" []) (List.reverse stmts) 
                       Nothing)
    

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
    stmts' <- flattenBody stmts
    -- liftIO $ putStrLn $ "Flattened body:\n" ++ show (ProcDecl vis proto stmts' pos)
    (stmts'',genProcs) <- unbranchBody params stmts'
    let procs = ProcDecl vis proto stmts'' pos:genProcs
    -- liftIO $ mapM_ (\item -> putStrLn $ show item) procs
    mapM_ compileProc procs
    -- (initVars,stmts'',finalVars) <- numberVars params stmts' pos
    -- liftIO $ putStrLn $ "Numbered body:\n" ++ show (ProcDecl vis proto stmts'' pos)
    -- proto' <- primProto initVars finalVars proto
    -- (_,procstate) <- userClauseComp $ compileStmts stmts''
    -- addProc name proto' [List.reverse $ body procstate] pos vis
    -- mapM_ (\(proto,body) -> 
    --         addProc (procProtoName proto) proto body Nothing Private)
    --   genProcs
normaliseItem (CtorDecl vis proto pos) = do
    modspec <- getModuleSpec
    Just modparams <- getModuleParams
    addCtor vis (last modspec) modparams proto
normaliseItem (StmtDecl stmt pos) = do
    modify (\s -> s { stmtDecls = maybePlace stmt pos : stmtDecls s})


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
--                 Clause compiler monad
----------------------------------------------------------------

-- |The clause compiler monad is a state transformer monad carrying the 
--  clause compiler state over the compiler monad.
type ClauseComp = StateT ClauseCompState Compiler


-- |The state of compilation of a clause; used by the ClauseComp
-- monad.
data ClauseCompState = ClauseComp {
    vars :: Map VarName Int    -- ^current var number for each var
  }


initClauseComp :: ClauseCompState
initClauseComp = ClauseComp Map.empty


nextVar :: String -> ClauseComp PrimVarName
nextVar name = do
    modify (\s -> s { vars = Map.alter incrMaybe name $ vars s })
    currVar name


currVar :: String -> ClauseComp PrimVarName
currVar name = do
    dict <- gets vars
    return $ mkPrimVarName dict name


mkPrimVarName :: Map String Int -> String -> PrimVarName
mkPrimVarName dict name =
    case Map.lookup name dict of
        Nothing -> shouldnt $ "Referred to undefined variable '" ++ name ++ "'"
        Just n  -> PrimVarName name n


incrMaybe :: Maybe Int -> Maybe Int
incrMaybe Nothing = Just 0
incrMaybe (Just n) = Just $ n + 1


-- |Run a clause compiler function from the Compiler monad to compile
--  a generated procedure.
evalClauseComp :: ClauseComp t -> Compiler t
evalClauseComp clcomp =
    evalStateT clcomp initClauseComp


compileProc :: Item -> Compiler ()
compileProc (ProcDecl vis (ProcProto name params) body pos) = do
    (params',body') <- evalClauseComp $ do
        mapM_ nextVar $ List.map paramName $ 
          List.filter (flowsIn . paramFlow) params
        startVars <- gets vars
        compiled <- compileBody body
        endVars <- gets vars
        return (List.map (primParam startVars endVars) params, compiled)
    addProc name (PrimProto name params') body' pos vis
    return ()
compileProc decl =
    shouldnt $ "compileProc applied to non-proc " ++ show decl


-- |Convert a Param to single PrimParam.  Only ParamIn and ParamOut 
--  params should still exist at this point. 
primParam :: Map VarName Int -> Map VarName Int -> Param -> PrimParam
primParam initVars finalVars (Param name typ ParamIn) =
    PrimParam (mkPrimVarName initVars name) typ FlowIn Ordinary
primParam initVars finalVars (Param name typ ParamOut) = do
    PrimParam (mkPrimVarName finalVars name) typ FlowOut Ordinary
primparam _ _ param =
    shouldnt $ "Flattening error: param '" ++ show param ++ "' remains"



-- |Compile a proc body to LPVM form.  By the time we get here, the 
--  form of the body is very limited:  it is either a single Cond 
--  statement, or it is a list of ProcCalls and ForeignCalls.  
--  Everything else has already been transformed away.
compileBody :: [Placed Stmt] -> ClauseComp [[Placed Prim]]
compileBody [placed]
  | case content placed of
      Cond _ _ _ _ _ -> True
      _ -> False
 = do
      let Cond tst thn els _ _  = content placed
      initial <- gets vars
      tst' <- mapM compileSimpleStmt tst
      thn' <- mapM compileSimpleStmt thn
      afterThen <- gets vars
      modify (\s -> s { vars = initial })
      els' <- mapM compileSimpleStmt els
      afterElse <- gets vars
      let final = Map.intersectionWith max afterThen afterElse
      modify (\s -> s { vars = final })
      let thn'' = thn' ++ reconcilingAssignments afterThen final
      let els'' = els' ++ reconcilingAssignments afterElse final
      return [Unplaced (PrimGuard tst' 1):thn'',
              Unplaced (PrimGuard tst' 0):els'']
compileBody stmts = do
    prims <- mapM compileSimpleStmt stmts
    return [prims]

compileSimpleStmt :: Placed Stmt -> ClauseComp (Placed Prim)
compileSimpleStmt stmt = do
    stmt' <- compileSimpleStmt' (content stmt)
    return $ maybePlace stmt' (place stmt)

compileSimpleStmt' :: Stmt -> ClauseComp Prim
compileSimpleStmt' (ProcCall name args _ _) = do
    args' <- mapM (compileArg . content) args
    return $ PrimCall name Nothing args'
compileSimpleStmt' (ForeignCall lang name args _ _) = do
    args' <- mapM (compileArg . content) args
    return $ PrimForeign lang name Nothing args'
compileSimpleStmt' (Nop _) = do
    return $ PrimNop
compileSimpleStmt' stmt =
    shouldnt $ "Normalisation left complex statement:\n" ++ showStmt 4 stmt


compileArg :: Exp -> ClauseComp PrimArg
compileArg (IntValue int) = return $ ArgInt int
compileArg (FloatValue float) = return $ ArgFloat float
compileArg (StringValue string) = return $ ArgString string
compileArg (CharValue char) = return $ ArgChar char
compileArg (Var name ParamIn) = do
    name' <- currVar name
    return $ ArgVar name' FlowIn Ordinary
compileArg (Var name ParamOut) = do
    name' <- nextVar name
    return $ ArgVar name' FlowOut Ordinary
compileArg arg =
    shouldnt $ "Normalisation left complex argument: " ++ show arg


reconcilingAssignments :: Map VarName Int -> Map VarName Int -> [Placed Prim]
reconcilingAssignments caseVars jointVars =
    let vars =
          List.filter (\v -> caseVars ! v /= jointVars ! v) $ keys jointVars
    in  List.map (reconcileOne caseVars jointVars) vars


reconcileOne :: (Map VarName Int) -> (Map VarName Int) -> VarName -> Placed Prim
reconcileOne caseVars jointVars var =
    Unplaced $
    PrimCall "=" Nothing [
        ArgVar (mkPrimVarName jointVars var) FlowOut Ordinary,
        ArgVar (mkPrimVarName caseVars var) FlowIn Ordinary]


-- -- |Generate a single instruction for the clause currently being compiled
-- instr :: Prim -> OptPos -> ClauseComp ()
-- instr PrimNop _ = return ()      -- Don't bother to generate Nops
-- instr prim pos = do
--   bdy <- gets body
--   modify (\st -> st {body = (maybePlace prim pos):bdy})


-- insertInputParam :: PrimParam -> Map VarName VarInfo -> Map VarName VarInfo
-- insertInputParam (PrimParam (PrimVarName var num) typ FlowIn _) symtab =
--     Map.insert var (VarInfo var num typ) symtab
-- insertInputParam (PrimParam _ _ FlowOut _) symtab = symtab    


-- ----------------------------------------------------------------
-- -- |Make a fresh proc with a fresh name
-- compileFreshProc :: ProcName -> LoopInfo -> VarVers -> VarVers -> 
--                     [[Placed Stmt]] -> ClauseComp Stmt
-- compileFreshProc name loopInfo initVars finalVars clauses = do
--   -- liftIO $ putStrLn $ "compiling separate proc:  " ++ show clauses
--   -- XXX get list of defined variables; this becomes list of inParams
--   -- XXX outParams is this list plus variables defined by all clauses
--   results <- mapM (genClauseComp loopInfo) clauses
--   let clauses' = List.map (List.reverse . body) results
--   -- liftIO $ putStrLn $ "compiled code:  " ++ show clauses'
--   if List.all List.null clauses'
--     then
--       return $ Nop initVars
--     else do
--       let (inVars,outVars) = allArgs initVars finalVars
--       let inParams = inferredParams initVars FlowIn inVars
--       let outParams = inferredParams finalVars FlowOut outVars
--       lift $ addProc name (PrimProto name (inParams++outParams)) 
--         clauses' Nothing Private
--       return $ generatedCall name inVars outVars initVars finalVars

-- allArgs :: VarVers -> VarVers -> ([VarName],[VarName])
-- allArgs BottomVarVers _ = ([],[])
-- allArgs (VarVers initVars) BottomVarVers = (Map.keys initVars,[])
-- allArgs (VarVers initVars) (VarVers finalVars) =
--     (Map.keys initVars,
--      List.filter (not . (sameAtKey initVars finalVars)) $ Map.keys finalVars)


-- inferredParams :: VarVers -> PrimFlow -> [VarName] -> [PrimParam]
-- inferredParams BottomVarVers _ _ = []
-- inferredParams (VarVers m) flow included =
--     List.map (\v -> PrimParam (PrimVarName v (m!v)) Unspecified flow Ordinary)
--     included


-- generatedCall :: ProcName -> [VarName] -> [VarName] -> VarVers -> VarVers -> Stmt
-- generatedCall name inNames outNames initVars finalVars =
--     let inArgs  = List.map (\v -> Unplaced $ Var v ParamIn) inNames
--         outArgs = List.map (\v -> Unplaced $ Var v ParamOut) outNames
--     in  ProcCall name (inArgs++outArgs) initVars finalVars


-- sameAtKey :: (Eq b, Ord a) => Map a b -> Map a b -> a -> Bool
-- sameAtKey m1 m2 k = (Map.lookup k m1) == (Map.lookup k m2)


-- -- |Compile a single complete clause, using a fresh ClauseComp monad
-- genClauseComp :: LoopInfo -> [Placed Stmt] -> ClauseComp ClauseCompState
-- genClauseComp loopInfo1 clause = do
--     tmpNum <- gets tmpCount
--     loopInfo0 <- gets loopInfo
--     let loopInfo = case loopInfo1 of
--             NoLoop -> loopInfo0
--             _ -> loopInfo1
--     (_,state) <- lift $ evalClauseComp tmpNum loopInfo $ compileStmts clause
--     return state


-- -- | Compile one normalised proc definition.
-- -- compileProc :: Item -> Compiler ()
-- -- compileProc (ProcDecl vis proto body pos) = do
    


-- -- |Compile the specified statements to primitive statements.
-- compileStmts :: [Placed Stmt] -> ClauseComp ()
-- compileStmts [] = return ()
-- compileStmts (stmt:stmts) = compileStmts' (content stmt) stmts (place stmt)

-- -- |Compile the specified statement, plus the list of following statements
-- compileStmts' :: Stmt -> [Placed Stmt] -> Maybe SourcePos -> ClauseComp ()
-- compileStmts' (ProcCall name args initVars finalVars) rest pos = do
--   primArgs <- mapM (\a->primArg (content a) (place a) initVars finalVars) 
--               args
--   instr (PrimCall name Nothing $ concat primArgs) pos
--   compileStmts rest
-- compileStmts' (ForeignCall lang name args initVars finalVars) rest pos = do
--   primArgs <- mapM (\a->primArg (content a) (place a) initVars finalVars) 
--               args
--   instr (PrimForeign lang name Nothing $ concat primArgs) pos
--   compileStmts rest
-- -- compileStmts' (Cond tests thn els initVars finalVars) rest pos = do
-- --   inf <- gets loopInfo
-- --   switchName <- lift $ genProcName
-- --   if inf == NoLoop || rest == []
-- --      then do
-- --       switch <- compileFreshProc switchName NoLoop initVars finalVars
-- --                 [Unplaced (Guard tests 1 initVars noVars):thn,
-- --                  Unplaced (Guard tests 0 initVars noVars):els]
-- --       compileStmts' switch rest Nothing
-- --     else do
-- --       contName <- lift $ genProcName
-- --       continuation <- compileFreshProc contName inf finalVars  
-- --                       (lastFinalVars rest) [rest]
-- --       switch <- compileFreshProc switchName inf initVars finalVars
-- --                 [Unplaced (Guard tests 1 initVars noVars):thn ++
-- --                  [Unplaced continuation],
-- --                  Unplaced (Guard tests 0 initVars noVars):els ++ 
-- --                  [Unplaced continuation]]
-- --       compileStmts' switch [] Nothing
-- -- compileStmts' (Loop loopBody initVars finalVars) rest pos = do
-- --   loopName <- lift $ genProcName
-- --   let (inVars,outVars) = allArgs initVars finalVars
-- --   loop <- compileFreshProc loopName 
-- --           -- The noVars below will be replaced for each Next goal, but all
-- --           -- will share the outVars.
-- --           (LoopInfo (generatedCall loopName inVars outVars initVars finalVars) 
-- --            [] [])
-- --           initVars finalVars [loopBody]
-- --   compileStmts' loop rest Nothing
-- compileStmts' (Guard guarded val initVars finalVars) rest pos = do
--   state <- genClauseComp NoLoop guarded
--   instr (PrimGuard (body state) val) pos
--   compileStmts rest
-- compileStmts' (Nop _) rest pos = compileStmts rest
-- -- compileStmts' (Break initVars) rest pos = do
-- --     inf <- gets loopInfo
-- --     case inf of
-- --         NoLoop -> lift $ message Error "Break outside of a loop" pos
-- --         LoopInfo _ _ _ -> do -- Must bind outputs as necessary
-- --             -- XXX what should I do here?
-- --             return ()
-- -- compileStmts' (Next initVars) rest pos = do
-- --     inf <- gets loopInfo
-- --     case inf of
-- --         NoLoop -> lift $ message Error "Next outside of a loop" pos
-- --         LoopInfo cont _ _ -> do
-- --             compileStmts' (replaceCallInittVars cont initVars) [] Nothing
-- --             return ()
-- compileStmts' stmt rest pos =
--     error $ "Normalise error:  " ++ showStmt 4 stmt


-- replaceCallInittVars :: Stmt -> VarVers -> Stmt
-- replaceCallInittVars (ProcCall name args _ finalVars) initVars =
--     ProcCall name args initVars finalVars
-- replaceCallInittVars _ _ =
--     shouldnt "expected 'next' statement to be a call"

-- -- |Compile an argument into a PrimArg if it's flattened; if not, return Nothing
-- primArg :: Exp -> OptPos -> VarVers -> VarVers -> ClauseComp [PrimArg]
-- primArg (IntValue a) pos initVars finalVars = return [ArgInt a]
-- primArg (FloatValue a) pos initVars finalVars = return [ArgFloat a]
-- primArg (StringValue a) pos initVars finalVars = return [ArgString a]
-- primArg (CharValue a) pos initVars finalVars = return [ArgChar a]
-- primArg (Var name dir) pos initVars finalVars = do
--   var <- lift $ flowVar name dir pos initVars finalVars
--   return var
-- primArg exp pos initVars finalVars =
--   shouldnt $ show (maybePlace exp pos) ++ " remains after flattening"


-- -- |Compile a list of expressions as proc call arguments to a list of 
-- --  primitive arguments, a list of statements to execute before the 
-- --  call to bind those arguments, and a list of statements to execute 
-- --  after the call to store the results appropriately.
-- normaliseArgs :: [Placed Exp] 
--                  -> ClauseComp ([Placed Exp],[Placed Stmt],[Placed Stmt],
--                                 FlowDirection)
-- normaliseArgs exps = do
--   argsResults <- mapM normalisePlacedExp exps
--   return $ List.foldr (\(a1,pre1,post1,flow1)(a2,pre2,post2,flow2) -> 
--                         (a1++a2,pre1++pre2,post1++post2,flow1 `flowJoin` flow2))
--     ([],[],[],NoFlow) argsResults

-- normalisePlacedExp :: Placed Exp -> ClauseComp ([Placed Exp],[Placed Stmt],
--                                                 [Placed Stmt], FlowDirection)
-- normalisePlacedExp pexp = normaliseExp (content pexp) (place pexp)

-- -- |Normalise a single expressions with specified flow direction to
-- --  primitive argument(s), a list of statements to execute
-- --  to bind it, and a list of statements to execute 
-- --  after the call to store the result appropriately.
-- --  The first part of the output (a Placed Exp) will always be a list
-- --  of only atomic Exps and Var references (in any direction).
-- normaliseExp :: Exp -> Maybe SourcePos
--               -> ClauseComp ([Placed Exp],[Placed Stmt],[Placed Stmt],
--                              FlowDirection)
-- normaliseExp exp@(IntValue a) pos = 
--   return ([maybePlace exp pos],[],[],ParamIn)
-- normaliseExp exp@(FloatValue a) pos = 
--   return ([maybePlace exp pos],[],[],ParamIn)
-- normaliseExp exp@(StringValue a) pos = 
--   return ([maybePlace exp pos],[],[],ParamIn)
-- normaliseExp exp@(CharValue a) pos = 
--   return ([maybePlace exp pos],[],[],ParamIn)
-- normaliseExp exp@(Var name dir) pos = 
--   return ([maybePlace exp pos],[],[],dir)
-- normaliseExp (Where stmts exp) _ = do
--   (e,pres,posts,flow) <- normaliseExp (content exp) (place exp)
--   return (e,stmts++pres,posts,flow)
-- normaliseExp (CondExp cond thn els) pos = do
--   resultName <- freshVar
--   return ([Unplaced $ Var resultName ParamIn],
--           [maybePlace (Cond cond
--                   [Unplaced $ ProcCall "=" 
--                    [Unplaced $ Var resultName ParamOut,thn] noVars noVars]
--                   [Unplaced $ ProcCall "=" 
--                    [Unplaced $ Var resultName ParamOut,els] noVars noVars]
--                   noVars noVars) pos],
--           [],ParamIn)
-- normaliseExp (Fncall name exps) pos = do
--   resultName <- freshVar
--   (args,pres,posts,flow) <- normaliseArgs exps
--   let pres' = if flowsIn flow then 
--                 pres++[maybePlace 
--                        (ProcCall name
--                         (List.map (fmap inputArg) args
--                         ++[Unplaced $ Var resultName ParamOut])
--                         noVars noVars)
--                        pos]
--               else pres
--   let posts' = if flowsOut flow then 
--                  [maybePlace
--                   (ProcCall name
--                    (args++[Unplaced $ Var resultName ParamIn])
--                    noVars noVars)
--                   pos]++posts
--                else posts
--   return ([Unplaced $ Var resultName flow],pres',posts',flow)
-- normaliseExp (ForeignFn lang name exps) pos = do
--   resultName <- freshVar
--   (args,pres,posts,flow) <- normaliseArgs exps
--   let pres' = if flowsIn flow then 
--                 pres++[maybePlace 
--                        (ForeignCall lang name
--                         (args++[Unplaced $ Var resultName ParamOut])
--                         noVars noVars)
--                        pos]
--               else pres
--   let posts' = if flowsOut flow then 
--                  posts++[maybePlace 
--                          (ForeignCall lang name
--                                 (args++[Unplaced $ Var resultName ParamIn])
--                                 noVars noVars)
--                          pos]
--                else posts
--   return ([Unplaced $ Var resultName flow],pres',posts',flow)


-- -- |Compile a loop generator to three lists of primitive statements:
-- --  statements to execute before, during, and after the loop.
-- compileGenerator :: Generator -> Maybe SourcePos -> ClauseComp (Placed Exp)
-- compileGenerator (In var exp) pos = do
--     (args,init,_,_) <- normalisePlacedExp exp
--     stateVarName <- freshVar
--     let asn = Unplaced $ ProcCall "=" 
--               (Unplaced (Var stateVarName ParamOut):args) noVars noVars
--     modify (\st -> st { loopInfo = 
--                              (loopInfo st) {loopInit = 
--                                                  (loopInit $ loopInfo st)
--                                                  ++init++[asn]}})
--     let stateArg = Unplaced $ Var stateVarName ParamInOut
--     let varArg = Unplaced $ Var var ParamOut
--     testVarName <- freshVar
--     let testArg = Unplaced $ Var testVarName ParamOut
--     compileStmts' (ProcCall "next" [stateArg,varArg,testArg] noVars noVars) [] Nothing
--     return $ Unplaced $ Var testVarName ParamIn


-- -- |Set up a loop with the specified continuation and break calls
-- initLoop :: Stmt -> ClauseComp ()
-- initLoop cont = 
--     modify (\st -> st { loopInfo = LoopInfo (Unplaced cont) (Unplaced cont) [] [] })


-- ----------------------------------------------------------------

-- inFlow :: FlowDirection -> FlowDirection
-- inFlow NoFlow     = NoFlow
-- inFlow ParamIn = ParamIn
-- inFlow ParamOut = NoFlow
-- inFlow ParamInOut = ParamIn

-- inputArg :: Exp -> Exp
-- inputArg (Var name dir) = Var name $ inFlow dir
-- inputArg exp = exp

-- -- |Transform the specified primitive argument to an input parameter.
-- expIsInput :: Exp -> Bool
-- expIsInput (Var var dir) = flowsIn dir
-- -- XXX Shouldn't assume everything but variables are inputs
-- expIsInput _ = True

-- -- |Join on the lattice of flow directions (NoFlow is bottom, 
-- --  ParamInOut is top, and the others are incomparable in between).
-- flowJoin :: FlowDirection -> FlowDirection -> FlowDirection
-- flowJoin NoFlow     x          = x
-- flowJoin x          NoFlow     = x
-- flowJoin ParamInOut _          = ParamInOut
-- flowJoin _          ParamInOut = ParamInOut
-- flowJoin ParamIn    ParamOut   = ParamInOut
-- flowJoin ParamIn    ParamIn    = ParamIn
-- flowJoin ParamOut   ParamOut   = ParamOut
-- flowJoin ParamOut   ParamIn    = ParamInOut


-- lastFinalVars :: [Placed Stmt] -> VarVers
-- lastFinalVars = stmtFinalVars . content . last

-- stmtFinalVars :: Stmt -> VarVers
-- stmtFinalVars (ProcCall _ _ _ vars) = vars
-- stmtFinalVars (ForeignCall _ _ _ _ vars) = vars
-- stmtFinalVars (Cond _ _ _ _ vars) = vars
-- stmtFinalVars (Loop _ _ vars) = vars
-- stmtFinalVars (Guard _ _ _ vars) = vars
-- stmtFinalVars (Nop vars) = vars
-- stmtFinalVars (For _ _ _ vars) = vars
-- stmtFinalVars (Break vars) = vars
-- stmtFinalVars (Next vars) = vars
