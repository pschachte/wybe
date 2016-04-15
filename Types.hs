--  File     : Types.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

-- |Support for type checking/inference.
module Types (validateModExportTypes, typeCheckMod, checkFullyTyped) where

import           AST
import           Control.Monad.State
import           Data.Graph
import           Data.List           as List
import           Data.Map            as Map
import           Data.Maybe
import           Data.Set            as Set
import           Options             (LogSelection (Types))
import           Resources
import           Util

import           Debug.Trace


----------------------------------------------------------------
--           Validating proc parameter type declarations
----------------------------------------------------------------


-- |Check declared types of exported procs for the specified module.
-- This doesn't check that the types are correct vis-a-vis the
-- definition, just that the declared types are valid types, and it
-- updates the types to their fully-module-qualified versions.
validateModExportTypes :: ModSpec -> Compiler ()
validateModExportTypes thisMod = do
    logTypes $ "**** Validating parameter types in module " ++
           showModSpec thisMod
    reenterModule thisMod
    iface <- getModuleInterface
    procs <- getModuleImplementationField (Map.toAscList . modProcs)
    procs' <- mapM (uncurry validateProcDefsTypes) procs
    updateModImplementation (\imp -> imp { modProcs = Map.fromAscList procs'})
    finishModule
    logTypes $ "**** Exiting module " ++ showModSpec thisMod
    return ()


validateProcDefsTypes :: Ident -> [ProcDef] -> Compiler (Ident,[ProcDef])
validateProcDefsTypes name defs = do
    defs' <- mapM (validateProcDefTypes name) defs
    return (name, defs')


validateProcDefTypes :: Ident -> ProcDef -> Compiler ProcDef
validateProcDefTypes name def = do
    let public = procVis def == Public
    let pos = procPos def
    let proto = procProto def
    let params = procProtoParams proto
    logTypes $ "Validating def of " ++ name
    params' <- mapM (validateParamType name pos public) params
    return $ def { procProto = proto { procProtoParams = params' }}


validateParamType :: Ident -> OptPos -> Bool -> Param -> Compiler Param
validateParamType pname ppos public param = do
    let ty = paramType param
    checkDeclIfPublic pname ppos public ty
    ty' <- fmap (fromMaybe Unspecified) $ lookupType ty ppos
    let param' = param { paramType = ty' }
    return param'


checkDeclIfPublic :: Ident -> OptPos -> Bool -> TypeSpec -> Compiler ()
checkDeclIfPublic pname ppos public ty = do
    when (public && ty == Unspecified) $
         message Error ("Public proc '" ++ pname ++
                        "' with undeclared parameter or return type") ppos


-- |Type check a single module named in the second argument; the
--  first argument is a list of all the modules in this module
-- dependency SCC.
typeCheckMod :: ModSpec -> Compiler ()
typeCheckMod thisMod = do
    logTypes $ "**** Type checking module " ++ showModSpec thisMod
    reenterModule thisMod
    procs <- getModuleImplementationField (Map.toList . modProcs)
    let ordered =
            stronglyConnComp
            [(name, name,
              nub $ concatMap (localBodyProcs thisMod . procImpln) procDefs)
             | (name,procDefs) <- procs]
    logTypes $ "**** Strongly connected components:\n" ++
      (intercalate "\n" $
       List.map (\scc -> "    " ++ intercalate ", "
                         (case scc of
                             AcyclicSCC name -> [name]
                             CyclicSCC list -> list)) ordered)
    errs <- mapM (typecheckProcSCC thisMod) ordered
    mapM_ (\e -> message Error (show e) Nothing) $ concat $ reverse errs
    finishModule
    logTypes $ "**** Exiting module " ++ showModSpec thisMod
    return ()


----------------------------------------------------------------
--                           Supporting types
----------------------------------------------------------------


-- |The reason a variable is given a certain type
data TypeReason = ReasonParam ProcName Int OptPos
                                      -- Formal param type/flow inconsistent
                | ReasonResource ProcName Ident OptPos
                                      -- Declared resource inconsistent
                | ReasonUndef ProcName ProcName OptPos
                                      -- Call to unknown proc
                | ReasonUninit ProcName VarName OptPos
                                      -- Use of uninitialised variable
                | ReasonArgType ProcName Int OptPos
                                      -- Actual param type inconsistent
                | ReasonCond OptPos   -- Conditional expression not bool
                | ReasonArgFlow ProcName Int OptPos
                                      -- Actual param flow inconsistent
                | ReasonOverload [ProcSpec] OptPos
                                      -- Multiple procs with same types/flows
                | ReasonAmbig ProcName OptPos [(VarName,[TypeSpec])]
                                      -- Proc defn has ambiguous types
                | ReasonArity ProcName ProcName OptPos Int Int
                                      -- Call to proc with wrong arity
                | ReasonUndeclared ProcName OptPos
                                      -- Public proc with some undeclared types
                | ReasonEqual Exp Exp OptPos
                                      -- expression types should be equal
                | ReasonShouldnt      -- Nothing should go wrong with this
                deriving (Eq, Ord)

instance Show TypeReason where
    show (ReasonParam name num pos) =
        makeMessage pos $
            "Type/flow error in definition of " ++ name ++
            ", parameter " ++ show num
    show (ReasonResource name resName pos) =
            "Type/flow error in definition of " ++ name ++
            ", resource " ++ resName
    show (ReasonArgType name num pos) =
        makeMessage pos $
            "Type error in call to " ++ name ++ ", argument " ++ show num
    show (ReasonCond pos) =
        makeMessage pos $
            "Type error in conditional expression"
    show (ReasonArgFlow name num pos) =
        makeMessage pos $
            "Flow error in call to " ++ name ++ ", argument " ++ show num
    show (ReasonOverload pspecs pos) =
        makeMessage pos $
            "Ambiguous overloading: call could refer to:" ++
            List.concatMap (("\n    "++) . show) (reverse pspecs)
    show (ReasonAmbig procName pos varAmbigs) =
        makeMessage pos $
            "Type ambiguity in defn of " ++ procName ++ ":" ++
            concat ["\n    Variable '" ++ v ++ "' could be: " ++
                    intercalate ", " (List.map show typs)
                   | (v,typs) <- varAmbigs]
    show (ReasonUndef callFrom callTo pos) =
        makeMessage pos $
            "Call to unknown '" ++ callTo ++ "' from " ++ callFrom
    show (ReasonUninit callFrom var pos) =
        makeMessage pos $
            "Unknown variable/constant '" ++ var ++ "'"
    show (ReasonArity callFrom callTo pos callArity procArity) =
        makeMessage pos $
            (if callFrom == ""
             then "Toplevel call"
             else "Call from " ++ callFrom) ++
            " to " ++ callTo ++ " with " ++
            (if callArity == procArity
             then "unsupported argument flow"
             else show callArity ++ " arguments, expected " ++ show procArity)
    show (ReasonUndeclared name pos) =
        makeMessage pos $
        "Public definition of '" ++ name ++ "' with some undeclared types."
    show (ReasonEqual exp1 exp2 pos) =
        makeMessage pos $
        "Expressions must have compatible types:\n    "
        ++ show exp1 ++ "\n    "
        ++ show exp2
    show (ReasonShouldnt) =
        makeMessage Nothing "Mysterious typing error"


-- | A type assignment for variables (symbol table), with a list of type errors
-- XXX Need to handle type unification properly by allowing a variable to
--     specify its type as whatever the type of another variable is. 
data Typing = Typing {
                  typingDict::Map VarName TypeSpec,
                  typingErrs::[TypeReason]
                  }
            deriving (Show,Eq,Ord)


initTyping :: Typing
initTyping = Typing Map.empty []


validTyping :: Typing -> Bool
validTyping (Typing _ errs) = List.null errs


varType :: Typing -> VarName -> Maybe TypeSpec
varType typing var = Map.lookup var $ typingDict typing


typeError :: TypeReason -> Typing -> Typing
typeError err (Typing dict errs) = Typing dict $ err:errs


addOneType :: TypeReason -> VarName -> TypeSpec -> Typing -> Typing
addOneType reason name typ typing@(Typing types errs) =
    -- Be sure we insert Unspecified if it's not already there, because
    -- it distinguishes a defined variable with unknown type from an
    -- undefined variable
    case Map.lookup name types of
      Nothing -> Typing (Map.insert name typ types) errs
      Just oldTyp ->
          if oldTyp `subtypeOf` typ
          then typing -- the type we already have covers the new one:  keep it
          else if typ `properSubtypeOf` oldTyp
               then -- the new type is compatible but better:  substitute it
                    Typing (Map.insert name typ types) errs
               else -- old and new types are incompatible:  report error
                    --trace ("addOneType " ++ name ++ ":" ++ show typ ++
                    --       " vs. " ++ show oldTyp ++ " FAILED") $
                    typeError reason typing


-- |Returns the first argument restricted to the variables appearing
--  in the second.
projectTyping :: Typing -> Typing -> Typing
projectTyping (Typing typing errs) (Typing interest _) =
    Typing (Map.filterWithKey (\k _ -> Map.member k interest) typing) errs
    

-- Simple subtype relation for now; every type is a subtype of the
-- unspecified type.
-- XXX Extend to support actual subtypes
properSubtypeOf :: TypeSpec -> TypeSpec -> Bool
properSubtypeOf _ Unspecified = True
properSubtypeOf _ _ = False


subtypeOf :: TypeSpec -> TypeSpec -> Bool
subtypeOf sub super =
    sub `properSubtypeOf` super
    || case (sub,super) of
         (TypeSpec mod1 name1 params1, TypeSpec mod2 name2 params2) ->
           name1 == name2
           && (mod1 == mod2 || mod2 == [])
           && length params1 == length params2
           && List.all (uncurry subtypeOf) (zip params1 params2)
         (_,_) -> False

meetTypes :: TypeSpec -> TypeSpec -> Maybe TypeSpec
meetTypes ty1 ty2 =
    if ty1 `subtypeOf` ty2
    then Just ty1
    else if ty2 `properSubtypeOf` ty1
         then Just ty2
         else Nothing


localBodyProcs :: ModSpec -> ProcImpln -> [Ident]
localBodyProcs thisMod (ProcDefSrc body) =
    foldProcCalls (localCalls thisMod) (++) [] body
localBodyProcs thisMod (ProcDefPrim _ _) =
    shouldnt "Type checking compiled code"
localBodyProcs thisMod (ProcDefBlocks _ _ _) =
    shouldnt "Type checking compiled code"

localCalls :: ModSpec -> ModSpec -> Ident -> (Maybe Int) -> [Placed Exp] -> [Ident]
localCalls thisMod m name _ _
  | m == [] || m == thisMod = [name]
localCalls _ _ _ _ _ = []


exprType :: Typing -> Exp -> Maybe TypeSpec
exprType _ (IntValue _) = Just $ TypeSpec ["wybe"] "int" []
exprType _ (FloatValue _) = Just $ TypeSpec ["wybe"] "float" []
exprType _ (StringValue _) = Just $ TypeSpec ["wybe"] "string" []
exprType _ (CharValue _) = Just $ TypeSpec ["wybe"] "char" []
exprType typing (Var name _ _) = varType typing name
exprType _ (Typed _ ty _) = Just ty
exprType _ exp =
    shouldnt $ "Expression '" ++ show exp ++ "' left after flattening"


matchTypes :: (Placed Exp) -> (Placed Exp) -> OptPos -> Typing -> Typing
matchTypes parg1 parg2 pos typing =
    let arg1 = content parg1
        arg2 = content parg2
        ty1  = exprType typing arg1
        ty2  = exprType typing arg2
    in  case (ty1,ty2) of
      (Nothing,Nothing)  -> typing
      (Nothing,Just typ) -> enforceType arg1 typ arg1 arg2 pos typing
      (Just typ,Nothing) -> enforceType arg2 typ arg1 arg2 pos typing
      (Just t1,Just t2)  -> enforceType arg1 t2 arg1 arg2 pos
                            $ enforceType arg2 t1 arg1 arg2 pos typing


-- |Require the Exp to have the specified type
enforceType :: Exp -> TypeSpec -> Exp -> Exp -> OptPos -> Typing -> Typing
enforceType (Var name _ _) typespec arg1 arg2 pos typing =
    addOneType (ReasonEqual arg1 arg2 pos) name typespec typing
enforceType (Typed (Var name _ _) typespec1 _) typespec arg1 arg2 pos typing =
    let reason = ReasonEqual arg1 arg2 pos
    in case meetTypes typespec1 typespec of
      Nothing -> typeError reason typing
      Just ty -> addOneType reason name ty typing
enforceType _ _ _ _ _ typing = typing -- no variable to record the type of



----------------------------------------------------------------
--                         Type checking procs
----------------------------------------------------------------

-- |Type check one strongly connected component in the local call graph
--  of a module.  The call graph contains only procs in the one module,
--  because this is being done for type inference, and imported procs
--  must have had their types declared.  Returns True if the inferred
--  types are more specific than the old ones and some proc(s) in the
--  SCC depend on procs in the list of mods.  In this case, we will
--  have to rerun the typecheck after typechecking the other modules
--  on that list.
typecheckProcSCC :: ModSpec -> SCC ProcName -> Compiler ([TypeReason])
typecheckProcSCC m (AcyclicSCC name) = do
    -- A single pass is always enough for non-cyclic SCCs
    logTypes $ "Type checking non-recursive proc " ++ name
    (_,reasons) <- typecheckProcDecls m name
    return (reasons)
typecheckProcSCC m (CyclicSCC list) = do
    logTypes $ "**** Type checking recursive procs " ++
      intercalate ", " list
    (sccAgain,reasons) <-
        foldM (\(sccAgain,rs) name -> do
                    (sccAgain',reasons) <- typecheckProcDecls m name
                    return (sccAgain || sccAgain', reasons++rs))
        (False, []) list
    if sccAgain
    then typecheckProcSCC m $ CyclicSCC list
    else do
      logTypes $ "**** Completed checking of " ++
             intercalate ", " list ++
             " with " ++ show (length reasons) ++ " errors"
      return (reasons)


-- |Type check a list of procedure definitions and update the
--  definitions stored in the Compiler monad.  Returns a pair of
--  Bools, the first saying whether any defnition has been udpated,
--  and the second saying whether any public defnition has been
--  updated.
typecheckProcDecls :: ModSpec -> ProcName ->
                     Compiler (Bool,[TypeReason])
typecheckProcDecls m name = do
    logTypes $ "** Type checking " ++ name
    defs <- getModuleImplementationField
            (Map.findWithDefault (error "missing proc definition")
             name . modProcs)
    (revdefs,sccAgain,reasons) <-
        foldM (\(ds,sccAgain,rs) def -> do
                    (d,again,rs') <- typecheckProcDecl m def
                    return (d:ds,sccAgain || again,rs'++rs))
        ([],False,[]) defs
    updateModImplementation
      (\imp -> imp { modProcs = Map.insert name (reverse revdefs)
                                $ modProcs imp })
    logTypes $ "** New definition of " ++ name ++ ":"
    logTypes $ intercalate "\n" $ List.map (showProcDef 4) (reverse revdefs)
    -- XXX this shouldn't be necessary anymore, but keep it for now for safety
    unless (sccAgain || not (List.null reasons)) $ do
        mapM_ checkProcDefFullytyped revdefs
    return (sccAgain,reasons)


-- |Type check a single procedure definition.
typecheckProcDecl :: ModSpec -> ProcDef -> Compiler (ProcDef,Bool,[TypeReason])
typecheckProcDecl m pd = do
    let name = procName pd
    let proto = procProto pd
    let params = procProtoParams proto
    let resources = procProtoResources proto
    let (ProcDefSrc def) = procImpln pd
    let pos = procPos pd
    let vis = procVis pd
    if vis == Public && any ((==Unspecified). paramType) params
      then return (pd,False,[ReasonUndeclared name pos])
      else do
        typing <- foldM (addDeclaredType name pos (length params))
                  initTyping $ zip params [1..]
        typing' <- foldM (addResourceType name pos)
                   typing resources
        if validTyping typing'
          then do
            logTypes $ "** Type checking " ++ name ++
              ": " ++ show typing'
            logTypes $ "   with resources: " ++ show resources
            (typing'',def') <- typecheckProcDef m name pos typing' def
            logTypes $ "*resulting types " ++ name ++
              ": " ++ show typing''
            let params' = updateParamTypes typing'' params
            let proto' = proto { procProtoParams = params' }
            let pd' = pd { procProto = proto', procImpln = ProcDefSrc def' }
            let pd'' = pd'
            let sccAgain = pd'' /= pd
            logTypes $ "===== Definition is " ++
                   (if sccAgain then "" else "un") ++ "changed"
            when sccAgain
                 (logTypes $ "** check again " ++ name ++
                      "\n-----------------OLD:" ++ showProcDef 4 pd ++
                      "\n-----------------NEW:" ++ showProcDef 4 pd' ++ "\n")
            return (pd'',sccAgain,typingErrs typing'')
          else
            shouldnt $ "Inconsistent param typing for proc " ++ name


addDeclaredType :: ProcName -> OptPos -> Int -> Typing -> (Param,Int) ->
                   Compiler Typing
addDeclaredType procname pos arity typs (Param name typ flow _,argNum) = do
    typ' <- fmap (fromMaybe Unspecified) $ lookupType typ pos
    logTypes $ "    type of '" ++ name ++ "' is " ++ show typ'
    return $ addOneType (ReasonParam procname arity pos) name typ' typs


addResourceType :: ProcName -> OptPos -> Typing -> ResourceFlowSpec ->
                   Compiler Typing
addResourceType procname pos typs rfspec = do
    let rspec = resourceFlowRes rfspec
    resIface <- lookupResource rspec pos
    let (rspecs,types) = unzip $ maybe [] Map.toList resIface
    let names = List.map resourceName rspecs
    let typs' = List.foldr
                (\(n,t) typs ->
                     addOneType
                     (ReasonResource procname n pos) n t typs)
                typs $ zip names types
    return typs'


updateParamTypes :: Typing -> [Param] -> [Param]
updateParamTypes typing params =
    List.map (\p@(Param name typ fl afl) ->
               case varType typing name of
                   Nothing -> p
                   Just newTyp -> Param name newTyp fl afl)
    params


-- |Type check the body of a single proc definition by type checking
--  each clause in turn using the declared parameter typing plus the
--  typing of all parameters inferred from previous clauses.  We can
--  stop once we've found a contradiction.
typecheckProcDef :: ModSpec -> ProcName -> OptPos -> Typing ->
                     [Placed Stmt] -> Compiler (Typing,[Placed Stmt])
typecheckProcDef m name pos paramTypes body = do
    logTypes $ "\ntype checking: " ++ name
    typings <- typecheckBody m name paramTypes body
    logTypes $ "typings:  " ++
      intercalate "\n          " (List.map show typings) ++ "\n"
    case typings of
      [] -> do
        logTypes $ "   no valid type"
        -- XXX This is the wrong reason
        return (typeError (ReasonAmbig name pos []) initTyping, body)
      [typing] -> do
        logTypes $ "   final typing: " ++ show typing
        logTypes $ "   initial param typing: " ++ show paramTypes
        let typing' = projectTyping typing paramTypes
        logTypes $ "   projected typing: " ++ show typing'
        if validTyping typing
            then do
                logTypes $ "apply body typing" ++ showBody 4 body
                body' <- applyBodyTyping typing body
                logTypes $ "After body typing:" ++ showBody 4 body'
                return (typing',body')
            else do
                logTypes $ "invalid: no body typing" ++ showBody 4 body
                return (typing', body)
      typings -> do
          logTypes $ name ++ " has " ++ show (length typings) ++
            " typings, of which " ++
            show (length (List.filter validTyping typings)) ++
            " are valid"
          let typingSets = List.map (Map.map Set.singleton . typingDict) typings
          let merged = Map.filter ((>1).Set.size) $
                       Map.unionsWith Set.union typingSets
          let ambigs = List.map (\(v,ts) -> (v,Set.toAscList ts)) $ assocs merged
          return (typeError (ReasonAmbig name pos ambigs) initTyping, body)


-- |Like a monadic foldl over a list, where each application produces
--  a list of values, and for each element of the folded list, the
--  function is applied to every result from the previous element,
--  finally producing the list of all the results.
typecheckSequence :: (Typing -> t -> Compiler [Typing]) -> [Typing] -> [t] ->
                    Compiler [Typing]
typecheckSequence f typings [] = return typings
typecheckSequence f typings (t:ts) = do
    logTypes $ "Type checking " ++ show (1 + length ts) ++ " things with " ++
      show (length typings) ++ " typings, " ++
      show (length $ List.filter validTyping typings) ++ " of them valid"
    typings' <- mapM (flip f t) typings
    let typings'' = pruneTypings $ concat typings'
    if List.null typings'
      then return []
      else if List.null typings'' || not (validTyping $ List.head typings'')
              -- No point going further if it's already invalid
           then return [List.head $ concat typings']
           else typecheckSequence f typings'' ts


pruneTypings :: [Typing] -> [Typing]
pruneTypings [] = []
pruneTypings typings =
    let pruned = nub $ List.filter validTyping typings
    in  if List.null pruned
        then typings
        else pruned


typecheckBody :: ModSpec -> ProcName -> Typing -> [Placed Stmt] ->
                 Compiler [Typing]
typecheckBody m name typing body = do
    logTypes $ "Entering typecheckSequence from typecheckBody"
    typings' <- typecheckSequence (typecheckPlacedStmt m name)
                [typing] body
    logTypes $ "Body types: " ++ show typings'
    return typings'


-- |Type check a single placed primitive operation given a list of
--  possible starting typings and corresponding clauses up to this prim.
typecheckPlacedStmt :: ModSpec -> ProcName -> Typing -> Placed Stmt ->
                       Compiler [Typing]
typecheckPlacedStmt m caller typing pstmt = do
    typecheckStmt m caller (content pstmt) (place pstmt) typing


-- |Type check a single primitive operation, producing a list of
--  possible typings.
typecheckStmt :: ModSpec -> ProcName -> Stmt -> OptPos -> Typing ->
                 Compiler [Typing]
typecheckStmt m caller call@(ProcCall cm name id args) pos typing = do
    logTypes $ "Type checking call " ++ showStmt 4 call ++
      showMaybeSourcePos pos
    logTypes $ "   with types " ++ show typing
    procs <- case id of
        Nothing   -> callTargets cm name
        Just pid -> return [ProcSpec cm name pid] -- XXX check modspec
                                                  -- is valid; or just
                                                  -- ignore pid?
    logTypes $ "   potential procs: " ++
           List.intercalate ", " (List.map show procs)
    if List.null procs
      then if 1 == length args
           then return [typeError (ReasonUninit caller name pos) typing]
           else return [typeError (ReasonUndef caller name pos) typing]
      else do
        typList <- mapM (matchingArgFlows caller name args pos typing) procs
        let typList' = concat typList
        let typList'' = List.filter validTyping typList'
        let dups = snd $ List.foldr
                   (\elt (s,l) ->
                        if Set.member elt s
                        then (s,if List.elem elt l then l else elt:l)
                        else (Set.insert elt s,l))
                   (Set.empty,[]) typList''
        logTypes $ "Resulting valid types: " ++ show typList''
        if List.null dups
        then if List.null typList''
             then do
                logTypes $ "Type error detected:\n" ++
                    unlines (List.map show typList')
                return typList'
             else return typList''
        else return [typeError (ReasonOverload
                                   (List.map fst $
                                    List.filter
                                      (List.any (flip List.elem dups) . snd) $
                                    zip procs typList)
                                   pos) typing]
typecheckStmt _ _ call@(ForeignCall "llvm" "move" [] [a1,a2]) pos typing = do
  -- Ensure arguments have the same types
    logTypes $ "Type checking move instruction " ++ showStmt 4 call
    let typing' = matchTypes a1 a2 pos typing
    logTypes $ "Resulting typing = " ++ show typing'
    return [typing']
typecheckStmt _ _ call@(ForeignCall _ _ _ args) pos typing = do
    -- Pick up any output casts
    logTypes $ "Type checking foreign call " ++ showStmt 4 call
    let typing' = List.foldr noteOutputCast typing $ List.map content args
    logTypes $ "Resulting typing = " ++ show typing'
    return [typing']
typecheckStmt m caller (Test stmts exp) pos typing = do
    typings <- typecheckBody m caller typing stmts
    mapM (\t -> do
               typecheckArg' (content exp) (place exp) Unspecified
                   (TypeSpec ["wybe"] "bool" []) t (ReasonCond pos))
        typings
typecheckStmt _ _ Nop pos typing = return [typing]
typecheckStmt m caller (Cond test exp thn els) pos typing = do
    typings <- typecheckSequence (typecheckPlacedStmt m caller) [typing] test
    typings' <- mapM (\t -> do
                           typecheckArg' (content exp) (place exp) Unspecified
                             (TypeSpec ["wybe"] "bool" []) t (ReasonCond pos))
                typings
    typings'' <- typecheckSequence (typecheckPlacedStmt m caller) typings' thn
    typecheckSequence (typecheckPlacedStmt m caller) typings'' els
typecheckStmt m caller (Loop body) pos typing = do
    typecheckSequence (typecheckPlacedStmt m caller) [typing] body
typecheckStmt m caller (For itr gen) pos typing = do
    -- XXX must handle generator type
    return [typing]
typecheckStmt _ _ Break pos typing = return [typing]
typecheckStmt _ _ Next pos typing = return [typing]


matchingArgFlows :: ProcName -> ProcName -> [Placed Exp] -> OptPos -> Typing -> ProcSpec -> Compiler [Typing]
matchingArgFlows caller called args pos typing pspec = do
    params <- fmap (List.filter nonResourceParam) $ getParams pspec
    logTypes $ "checking flow of call to " ++ show pspec
        ++ " args " ++ show args
        ++ " against params " ++ show params ++ "..."
    case reconcileArgFlows params args of
      Just args' -> do
        logTypes $ "MATCHES; checking types: args = " ++ show args'
        typing <- foldM (typecheckArg pos params $ procSpecName pspec)
            typing $ zip3 [1..] params args'
        logTypes $ "Type check result = " ++ show typing
        return [typing]
      Nothing -> do
        logTypes "fails"
        return [typeError (ReasonArity caller called pos (length args)
                           (length  params))
                typing]

noteOutputCast :: Exp -> Typing -> Typing
noteOutputCast (Typed (Var name flow _) typ True) typing
  | flowsOut flow = addOneType ReasonShouldnt name typ typing
noteOutputCast _ typing = typing


-- |Match up params to args based only on flow, returning Nothing if
--  they don't match, and Just a possibly updated arglist if they
--  do.  The purpose is to handle passing an in-out argument pair
--  where only an output is expected.  This is permitted, and the
--  input half is just ignored.  This is performed after the code has
--  been flattened, so ParamInOut have already been turned into
--  adjacent pairs of ParamIn and ParamOut parameters.
reconcileArgFlows :: [Param] -> [Placed Exp] -> Maybe [Placed Exp]
reconcileArgFlows [] [] = Just []
reconcileArgFlows _ [] = Nothing
reconcileArgFlows [] _ = Nothing
reconcileArgFlows (Param _ _ ParamOut _:params)
  (arg1:arg2:args)
    | isHalfUpdate ParamIn (content arg1) &&
      isHalfUpdate ParamOut (content arg2)
    = fmap (arg2:) $ reconcileArgFlows params args
reconcileArgFlows (Param _ _ pflow _:params) (arg:args)
    = if pflow == expFlow (content arg)
      then fmap (arg:) $ reconcileArgFlows params args
      else Nothing


-- |Does this parameter *not* correspond to a resource?
nonResourceParam :: Param -> Bool
nonResourceParam (Param _ _ _ (Resource _)) = False
nonResourceParam _ = True


typecheckArg :: OptPos -> [Param] -> ProcName ->
                Typing -> (Int,Param,Placed Exp) -> Compiler Typing
typecheckArg pos params pname typing (argNum,param,arg) = do
    let reasonType = ReasonArgType pname argNum pos
    if not $ validTyping typing
      then return typing
      else do
      logTypes $ "type checking " ++ show arg ++ " against " ++ show param
      typecheckArg' (content arg) (place arg) Unspecified
        (paramType param) typing reasonType


typecheckArg' :: Exp -> OptPos -> TypeSpec -> TypeSpec -> Typing ->
                 TypeReason -> Compiler Typing
typecheckArg' (Typed exp typ cast) pos _ paramType typing reason = do
    typ' <- fmap (fromMaybe Unspecified) $ lookupType typ pos
    typecheckArg' exp pos (if cast then Unspecified else typ')
                  paramType typing reason
    -- typecheckArg' exp pos  typ'
    --               paramType typing reason
typecheckArg' (Var var _ _) _ declType paramType typing reason = do
    -- XXX should out flow typing be contravariant?
    logTypes $
        "Check Var " ++ var ++ ":" ++ show declType ++ " vs. " ++
        show paramType ++
        (if paramType `subtypeOf` declType then " succeeded" else " FAILED")
    if paramType `subtypeOf` declType
      then return $ addOneType reason var paramType typing
      else if paramType == Unspecified -- may be type checking recursion
           then return typing
           else return $ typeError reason typing
typecheckArg' (IntValue val) _ declType paramType typing reason = do
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "int" [])
      typing reason
typecheckArg' (FloatValue val) _ declType paramType typing reason = do
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "float" [])
      typing reason
typecheckArg' (StringValue val) _ declType paramType typing reason = do
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "string" [])
      typing reason
typecheckArg' (CharValue val) _ declType paramType typing reason = do
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "char" [])
      typing reason
typecheckArg' exp _ _ _ _ _ = do
    shouldnt $ "trying to type check expression " ++ show exp ++ "."


typecheckArg'' :: TypeSpec -> TypeSpec -> TypeSpec -> Typing -> TypeReason ->
                  Typing
typecheckArg'' callType paramType constType typing reason =
    let realType =
            if constType `subtypeOf` callType then constType else callType
    in -- trace ("check call type " ++ show callType ++ " against param type " ++ show paramType ++ " for const type " ++ show constType) $
       if paramType `subtypeOf` realType
       then typing
       else -- trace ("type error with constant: " ++ show realType ++ " vs. " ++ show paramType)
            typeError reason typing


firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (j@(Just _):_) = j
firstJust (Nothing:rest) = firstJust rest


listArity :: (t -> ArgFlowType) -> (t -> PrimFlow) -> [t] -> Int
listArity toFType toDirection lst =
    sum $ [if toFType e == HalfUpdate && toDirection e == FlowOut then 0 else 1
          | e <- lst]


applyBodyTyping :: Typing -> [Placed Stmt] -> Compiler [Placed Stmt]
applyBodyTyping typing body = do
    mapM (placedApplyM (applyStmtTyping typing)) $ body


applyStmtTyping :: Typing -> Stmt -> OptPos -> Compiler (Placed Stmt)
applyStmtTyping typing call@(ProcCall cm name id args) pos = do
    logTypes $ "typing call " ++ showStmt 4 call
    let args' = List.map (fmap $ applyExpTyping typing) args
    procs <- case id of
        Nothing   -> callTargets cm name
        Just n -> return [ProcSpec cm name n]
    logTypes $ "   " ++ show (length procs) ++ " potential procs: "
           ++ intercalate ", " (List.map show procs)
    matches <- fmap catMaybes $ mapM (matchProcType args') procs
    checkError ((show $ length matches) ++
                " matching procs (should be 1) for stmt "
                ++ showStmt 0 call)
      (1 /= length matches)
    let [(args'',proc)] = matches
    let call' = ProcCall (procSpecMod proc) (procSpecName proc)
                         (Just (procSpecID proc)) args''
    logTypes $ "typed call = " ++ showStmt 4 call'
    return $ maybePlace call' pos
applyStmtTyping typing call@(ForeignCall lang name flags args) pos = do
    logTypes $ "typing call " ++ showStmt 0 call
    let args' = List.map (fmap $ applyExpTyping typing) args
    let instr = ForeignCall lang name flags args'
    logTypes $ "typed call = " ++ showStmt 0 instr
    return $ maybePlace instr pos
applyStmtTyping typing (Test stmts exp) pos = do
    stmts' <- applyBodyTyping typing stmts
    let exp' = fmap (applyExpTyping typing) exp
    return $ maybePlace (Test stmts' exp') pos
applyStmtTyping typing (Cond test cond thn els) pos = do
    test' <- applyBodyTyping typing test
    let cond' = fmap (applyExpTyping typing) cond
    thn' <- applyBodyTyping typing thn
    els' <- applyBodyTyping typing els
    return $ maybePlace (Cond test' cond' thn' els') pos
applyStmtTyping typing (Loop body) pos = do
    body' <- applyBodyTyping typing body
    return $ maybePlace (Loop body') pos
applyStmtTyping typing (Nop) pos = return $ maybePlace Nop pos
applyStmtTyping typing (For itr gen) pos = do
    let itr' = fmap (applyExpTyping typing) itr
    let gen' = fmap (applyExpTyping typing) gen
    return $ maybePlace (For itr' gen') pos
applyStmtTyping typing (Break) pos = return $ maybePlace Break pos
applyStmtTyping typing (Next) pos = return $ maybePlace Next pos


applyExpTyping :: Typing -> Exp -> Exp
applyExpTyping _ exp@(IntValue _) =
    Typed exp (TypeSpec ["wybe"] "int" []) False
applyExpTyping _ exp@(FloatValue _) =
    Typed exp (TypeSpec ["wybe"] "float" []) False
applyExpTyping _ exp@(StringValue _) =
    Typed exp (TypeSpec ["wybe"] "string" []) False
applyExpTyping _ exp@(CharValue _) =
    Typed exp (TypeSpec ["wybe"] "char" []) False
applyExpTyping typing exp@(Var nm flow ftype) =
    case varType typing nm of
        Nothing -> shouldnt $ "type of variable '" ++ nm ++ "' unknown"
        Just typ -> Typed exp typ False
applyExpTyping typing typed@(Typed _ _ True) =
    typed
applyExpTyping typing (Typed exp _ False) =
    applyExpTyping typing exp
applyExpTyping _ exp =
    shouldnt $ "Expression '" ++ show exp ++ "' left after flattening"


matchProcType :: [Placed Exp] -> ProcSpec
              -> Compiler (Maybe ([Placed Exp], ProcSpec))
matchProcType args p = do
    params <- fmap (List.filter nonResourceParam) $ getParams p
    logTypes $ "   checking call to " ++
        show p ++ " args " ++
        show args ++ " against params " ++
        show params
    return $
        fmap (\as -> (as,p)) $
        checkMaybe (\as -> all (uncurry subtypeOf)
                           (zip (List.map
                                 (expType . content) as)
                            (List.map
                             paramType params))) $
        reconcileArgFlows params args


----------------------------------------------------------------
--                    Check that everything is typed
----------------------------------------------------------------

-- |Sanity check: make sure all args and params of all procs in the
-- current module are fully typed.  If not, report an internal error.
checkFullyTyped :: Compiler ()
checkFullyTyped = do
    procs <- getModuleImplementationField (concat . Map.elems . modProcs)
    mapM_ checkProcDefFullytyped procs


-- |Make sure all args and params in the specified proc def are typed.
checkProcDefFullytyped :: ProcDef -> Compiler ()
checkProcDefFullytyped def = do
    let name = procName def
    let pos = procPos def
    mapM_ (checkParamTyped name pos) $
      zip [1..] $ procProtoParams $ procProto def
    mapM_ (placedApplyM (checkStmtTyped name pos)) $
          procDefSrc $ procImpln def


procDefSrc :: ProcImpln -> [Placed Stmt]
procDefSrc (ProcDefSrc def) = def
procDefSrc (ProcDefPrim _ _) = shouldnt $ "procDefSrc applied to ProcDefPrim"
procDefSrc (ProcDefBlocks _ _ _) =
  shouldnt $ "procDefSrc applied to ProcDefBlocks"


expType :: Exp -> TypeSpec
expType (Typed _ typ _)     = typ
expType exp = shouldnt $ "expType of untyped expression " ++ show exp


checkParamTyped :: ProcName -> OptPos -> (Int,Param) -> Compiler ()
checkParamTyped name pos (num,param) = do
    when (Unspecified == paramType param) $
      reportUntyped name pos (" parameter " ++ show num)


checkStmtTyped :: ProcName -> OptPos -> Stmt -> OptPos -> Compiler ()
checkStmtTyped name pos (ProcCall pmod pname pid args) ppos = do
    when (isNothing pid || List.null pmod) $
         shouldnt $ "Call to " ++ pname ++ showMaybeSourcePos ppos ++
                  " left unresolved"
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped name pos (ForeignCall _ pname _ args) ppos = do
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped name pos (Test stmts exp) ppos = do
    mapM_ (placedApplyM (checkStmtTyped name pos)) stmts
    checkExpTyped name pos ("test" ++ showMaybeSourcePos ppos) $
                  content exp
checkStmtTyped name pos (Cond ifstmts cond thenstmts elsestmts) ppos = do
    mapM_ (placedApplyM (checkStmtTyped name pos)) ifstmts
    checkExpTyped name pos ("condition" ++ showMaybeSourcePos ppos) $
                  content cond
    mapM_ (placedApplyM (checkStmtTyped name pos)) thenstmts
    mapM_ (placedApplyM (checkStmtTyped name pos)) elsestmts
checkStmtTyped name pos (Loop stmts) ppos = do
    mapM_ (placedApplyM (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (For itr gen) ppos = do
    checkExpTyped name pos ("for iterator" ++ showMaybeSourcePos ppos) $
                  content itr
    checkExpTyped name pos ("for generator" ++ showMaybeSourcePos ppos) $
                  content itr
checkStmtTyped _ _ Nop _ = return ()
checkStmtTyped _ _ Break _ = return ()
checkStmtTyped _ _ Next _ = return ()


checkArgTyped :: ProcName -> OptPos -> ProcName -> OptPos ->
                 (Int, Exp) -> Compiler ()
checkArgTyped callerName callerPos calleeName callPos (n,arg) = do
    checkExpTyped callerName callerPos
                      ("in call to " ++ calleeName ++
                       showMaybeSourcePos callPos ++
                       ", arg " ++ show n) arg


checkExpTyped :: ProcName -> OptPos -> String -> Exp ->
                 Compiler ()
checkExpTyped _ _ _ (Typed _ _ _) = return ()
checkExpTyped callerName callerPos msg _ =
    reportUntyped callerName callerPos msg


reportUntyped :: ProcName -> OptPos -> String -> Compiler ()
reportUntyped procname pos msg = do
    liftIO $ putStrLn $ "Internal error: In " ++ procname ++
      showMaybeSourcePos pos ++ ", " ++ msg ++ " left untyped"


-- |Log a message, if we are logging type checker activity.
logTypes :: String -> Compiler ()
logTypes s = logMsg Types s

