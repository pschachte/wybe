--  File     : Types.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

-- |Support for type checking/inference.
module Types (validateModExportTypes, typeCheckMod, checkFullyTyped) where

import           Control.Arrow
import           AST
import           Control.Monad.State
import           Data.Graph
import           Data.List           as List
import           Data.Map            as Map
import           Data.Maybe          as Maybe
import           Data.Set            as Set
import           Options             (LogSelection (Types))
-- import           Resources
import           Util
import           Snippets
    
import           Debug.Trace


----------------------------------------------------------------
--           Validating Proc Parameter Type Declarations
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
    loggedFinishModule thisMod


loggedFinishModule :: ModSpec -> Compiler ()
loggedFinishModule thisMod = do
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
    ty' <- fromMaybe AnyType <$> lookupType ty ppos
    let param' = param { paramType = ty' }
    return param'


checkDeclIfPublic :: Ident -> OptPos -> Bool -> TypeSpec -> Compiler ()
checkDeclIfPublic pname ppos public ty =
    when (public && ty == AnyType) $
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
      intercalate "\n"
       (List.map (\scc -> "    " ++ intercalate ", "
                         (case scc of
                             AcyclicSCC name -> [name]
                             CyclicSCC list -> list)) ordered)
    errs <- mapM (typecheckProcSCC thisMod) ordered
    mapM_ (\e -> message Error (show e) Nothing) $ concat $ reverse errs
    loggedFinishModule thisMod


----------------------------------------------------------------
--                       Supporting Type Errors
----------------------------------------------------------------

-- |Either something or some type errors
data MaybeErr t = OK t | Err [TypeError]
    deriving (Eq,Show)


-- |Return a list of the errors in the supplied MaybeErr
errList :: MaybeErr t -> [TypeError]
errList (OK _) = []
errList (Err lst) = lst


-- |Return a list of the payloads of all the OK elements of the input list
catOKs :: [MaybeErr t] -> [t]
catOKs lst = let toMaybe (OK a) =  Just a
                 toMaybe (Err _) = Nothing
             in  Maybe.mapMaybe toMaybe lst


-- |The reason a variable is given a certain type
data TypeError = ReasonParam ProcName Int OptPos
                   -- ^Formal param type/flow inconsistent
               | ReasonResource ProcName Ident OptPos
                   -- ^Declared resource inconsistent
               | ReasonUndef ProcName ProcName OptPos
                   -- ^Call to unknown proc
               | ReasonUninit ProcName VarName OptPos
                   -- ^Use of uninitialised variable
               | ReasonArgType ProcName Int OptPos
                   -- ^Actual param type inconsistent
               | ReasonCond OptPos
                   -- ^Conditional expression not bool
               | ReasonArgFlow ProcName Int OptPos
                   -- ^Actual param flow inconsistent
               | ReasonOverload [ProcSpec] OptPos
                   -- ^Multiple procs with same types/flows
               | ReasonAmbig ProcName OptPos [(VarName,[TypeSpec])]
                   -- ^Proc defn has ambiguous types
               |  ReasonArity ProcName ProcName OptPos Int Int
                   -- ^Call to proc with wrong arity
               | ReasonUndeclared ProcName OptPos
                   -- ^Public proc with some undeclared types
               | ReasonEqual Exp Exp OptPos
                   -- ^Expression types should be equal
               | ReasonShouldnt
                   -- ^This error should never happen
               deriving (Eq, Ord)


instance Show TypeError where
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
        makeMessage pos
            "Conditional or test expression with non-boolean result"
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
    show ReasonShouldnt =
        makeMessage Nothing "Mysterious typing error"


-- |Construct the appropriate TypeError for a call to an undefined proc/func.
undefStmtErr :: Ident -> Placed Stmt -> TypeError
undefStmtErr caller pstmt =
    let pos = place pstmt
    in case content pstmt of
        ProcCall _ callee _ _ -> ReasonUndef caller callee pos
        other -> shouldnt $ "undefStmtErr with non-call stmt " ++ show other
    

----------------------------------------------------------------
--                           Type Assignments
----------------------------------------------------------------

-- | A type assignment for variables (symbol table), with a list of type errors
-- XXX Need to handle type unification properly by allowing a variable to
--     specify its type as whatever the type of another variable is.
--     This could be done by adding a variable reference alternative to the
--     TypeSpec type.
data Typing = Typing {
                  typingDict::Map VarName TypeSpec,
                  typingErrs::[TypeError]
                  }
            deriving (Show,Eq,Ord)


initTyping :: Typing
initTyping = Typing Map.empty []


validTyping :: Typing -> Bool
validTyping (Typing _ errs) = List.null errs


varType :: VarName -> Typing -> Maybe TypeSpec
varType var typing = Map.lookup var $ typingDict typing


setVarType :: VarName -> TypeSpec -> Typing -> Typing
setVarType var ty (Typing dict errs) = Typing (Map.insert var ty dict) errs


typeError :: TypeError -> Typing -> Typing
typeError err = typeErrors [err]


typeErrors :: [TypeError] -> Typing -> Typing
typeErrors newErrs (Typing dict errs) = Typing dict $ newErrs ++ errs


addOneType :: TypeError -> VarName -> TypeSpec -> Typing -> Typing
addOneType reason name typ typing =
    -- Be sure we insert AnyType if it's not already there, because
    -- it distinguishes a defined variable with unknown type from an
    -- undefined variable
    case varType name typing of
      Nothing -> setVarType name typ typing
      Just oldTyp
          -- the type we already have covers the new one:  keep it
          | oldTyp `subtypeOf` typ -> typing
          -- the new type is compatible but better:  substitute it
          | typ `properSubtypeOf` oldTyp -> setVarType name typ typing
          -- old and new types are incompatible:  report error
          | otherwise ->
              --trace ("addOneType " ++ name ++ ":" ++ show typ ++
              --       " vs. " ++ show oldTyp ++ " FAILED") $
              typeError reason typing


-- |Returns the first argument restricted to the variables appearing
--  in the second.
projectTyping :: Typing -> Typing -> Typing
projectTyping (Typing typing errs) (Typing interest _) =
    Typing (Map.filterWithKey (\k _ -> Map.member k interest) typing) errs
    

----------------------------------------------------------------
--                           The Type Lattice
----------------------------------------------------------------

-- Simple strict subtype relation for now; every type is a subtype of the
-- unspecified type, and the invalid type is a subtype of every other type.
-- XXX Extend to support actual subtypes
properSubtypeOf :: TypeSpec -> TypeSpec -> Bool
properSubtypeOf _ AnyType = True
properSubtypeOf InvalidType _ = True
properSubtypeOf (TypeSpec mod1 name1 params1) (TypeSpec mod2 name2 params2) =
    name1 == name2
    && (mod1 == mod2 || List.null mod2)
    && length params1 == length params2
    && List.all (uncurry subtypeOf) (zip params1 params2)
properSubtypeOf _ _ = False


-- |Non-strict subtype relation
subtypeOf :: TypeSpec -> TypeSpec -> Bool
subtypeOf sub super = sub `properSubtypeOf` super || sub == super


-- |Return the greatest lower bound of two TypeSpecs.  
meetTypes :: TypeSpec -> TypeSpec -> TypeSpec
meetTypes ty1 ty2
    | ty1 `subtypeOf` ty2       = ty1
    | ty2 `properSubtypeOf` ty1 = ty2
    | otherwise                 = InvalidType


localBodyProcs :: ModSpec -> ProcImpln -> [Ident]
localBodyProcs thisMod (ProcDefSrc body) =
    foldProcCalls (localCalls thisMod) (++) [] body
localBodyProcs thisMod (ProcDefPrim _ _) =
    shouldnt "Type checking compiled code"

localCalls :: ModSpec -> ModSpec -> Ident -> Maybe Int -> [Placed Exp]
           -> [Ident]
localCalls thisMod m name _ _
  | List.null m || m == thisMod = [name]
localCalls _ _ _ _ _ = []


expType :: Typing -> Placed Exp -> Compiler (Maybe TypeSpec)
expType typing = placedApply (expType' typing)


expType' _ (IntValue _) _ = return $ Just $ TypeSpec ["wybe"] "int" []
expType' _ (FloatValue _) _ = return $ Just $ TypeSpec ["wybe"] "float" []
expType' _ (StringValue _) _ = return $ Just $ TypeSpec ["wybe"] "string" []
expType' _ (CharValue _) _ = return $ Just $ TypeSpec ["wybe"] "char" []
expType' typing (Var name _ _) _ = return $ varType name typing
expType' _ (Typed _ typ _) pos = lookupType typ pos
expType' _ exp _ =
    shouldnt $ "Expression '" ++ show exp ++ "' left after flattening"


matchTypes :: Placed Exp -> Placed Exp -> OptPos -> Typing -> Compiler Typing
matchTypes parg1 parg2 pos typing = do
    let arg1 = content parg1
    let arg2 = content parg2
    maybety1 <- expType typing parg1
    maybety2 <- expType typing parg2
    logTypes $ "Matching types " ++ show maybety1 ++ " and " ++ show maybety2
    case (maybety1,maybety2) of
      (Nothing,Nothing)  -> return typing
      (Nothing,Just typ) -> return $ enforceType arg1 typ arg1 arg2 pos typing
      (Just typ,Nothing) -> return $ enforceType arg2 typ arg1 arg2 pos typing
      (Just typ1,Just typ2)  ->
        return $ enforceType arg1 typ2 arg1 arg2 pos
        $ enforceType arg2 typ1 arg1 arg2 pos typing


-- |Require the Exp to have the specified type
enforceType :: Exp -> TypeSpec -> Exp -> Exp -> OptPos -> Typing -> Typing
enforceType (Var name _ _) typespec arg1 arg2 pos typing =
    addOneType (ReasonEqual arg1 arg2 pos) name typespec typing
enforceType (Typed (Var name _ _) typespec1 _) typespec arg1 arg2 pos typing =
    let reason = ReasonEqual arg1 arg2 pos
    in case meetTypes typespec1 typespec of
      InvalidType -> typeError reason typing
      ty          -> addOneType reason name ty typing
enforceType _ _ _ _ _ typing = typing -- no variable to record the type of



-- |Update the typing to assign the specified type to the specified exp
setExpType :: Placed Exp -> TypeSpec -> Typing  -> Typing
setExpType pexp = setExpType' (content pexp)

setExpType' (IntValue _) _ typing = typing
setExpType' (FloatValue _) _ typing = typing
setExpType' (StringValue _) _ typing = typing
setExpType' (CharValue _) _ typing = typing
setExpType' (Var name _ _) typ typing = setVarType name typ typing
setExpType' (Typed exp _ _) typ typing = setExpType' exp typ typing
setExpType' otherExp _ _ = shouldnt $ "Invalid expr left after flattening "
                                     ++ show otherExp

----------------------------------------------------------------
--                         Type Checking Procs
----------------------------------------------------------------

-- |Type check one strongly connected component in the local call graph
--  of a module.  The call graph contains only procs in the one module,
--  because this is being done for type inference, and imported procs
--  must have had their types declared.  Returns True if the inferred
--  types are more specific than the old ones and some proc(s) in the
--  SCC depend on procs in the list of mods.  In this case, we will
--  have to rerun the typecheck after typechecking the other modules
--  on that list.
typecheckProcSCC :: ModSpec -> SCC ProcName -> Compiler [TypeError]
typecheckProcSCC m (AcyclicSCC name) = do
    -- A single pass is always enough for non-cyclic SCCs
    logTypes $ "Type checking non-recursive proc " ++ name
    (_,reasons) <- typecheckProcDecls m name
    return reasons
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
      return reasons


-- |Type check a list of procedure definitions and update the
--  definitions stored in the Compiler monad.  Returns a pair of
--  Bools, the first saying whether any defnition has been udpated,
--  and the second saying whether any public defnition has been
--  updated.
typecheckProcDecls :: ModSpec -> ProcName ->
                     Compiler (Bool,[TypeError])
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
    unless (sccAgain || not (List.null reasons)) $
        mapM_ checkProcDefFullytyped revdefs
    return (sccAgain,reasons)


----------------------------------------------------------------
--                       Resolving types and modes
--
-- This code resolves types and modes, including resolving overloaded
-- calls, handling implied modes, and appropriately ordering calls from
-- nested function application (which was not resolved during flattening).
-- We search for a valid resolution deterministically if possible.
--
-- To do this we first collect a list of all the calls in the proc body.
-- We process this maintaining 3 data structures:
--    * a typing:  a map from variable name to type;
--    * a resolution:  a mapping from original call to the selected proc spec;
--    * residue:  a list of unprocessed (delayed) calls with the list of
--      resolutions for each.
--
-- For each call, we collect the list of all possible resolutions, and
-- filter this down to the ones that match the argument types given the
-- current typing. If this is unique, we add it to the resolution mapping
-- and update the typing. If there are no matches, we check if there is a
-- unique resolution taking implied modes into account, and if so we select
-- it. If there are no resolutions at all, even allowing for implied modes,
-- then we can report a type error. If there are multiple matches, we add
-- this call to the residue and move on to the the call.
--
-- This process is repeated using the residue of the previous pass as the
-- input to the next one, repeating as long as the residue gets strictly
-- smaller.  Once it stops getting smaller, we select the remaining call
-- with the fewest resolutions and try selecting each resolution and then
-- processing the remainder of the residue with that "guess".  If only one
-- of the guesses leads to a valid typing, that is the correct typing;
-- otherwise we report a type error.


-- -- |A ProcSpec resolving a call together with it param types
-- data ProcAndParams = ProcAndParams { procSpec :: ProcSpec,
--                                      paramTypes :: [TypeSpec]}
--     deriving (Eq,Show)

-- -- |The resolutions of many proc calls
-- type StmtResolution = Map Stmt ProcSpec
-- 
-- emptyStmtResolution = Map.empty


-- |An individual proc and its argument types
data ProcInfo = ProcInfo {
  procInfoProc :: ProcSpec,
  procInfoArgs :: [TypeFlow]
  } deriving (Eq)


procInfoTypes :: ProcInfo -> [TypeSpec]
procInfoTypes call = typeFlowType <$> procInfoArgs call


-- |A single call statement together with a list of all the possible different
--  parameter list types (a list of types).  This type is used to narrow down
--  the possible call typings.
data StmtTypings = StmtTypings {typingStmt::Placed Stmt,
                                typingArgsTypes::[ProcInfo]}
    deriving (Eq)


-- |Type check a single procedure definition, including resolving overloaded
-- calls, handling implied modes, and appropriately ordering calls from
-- nested function application.  We search for a valid resolution
-- deterministically if possible.
typecheckProcDecl :: ModSpec -> ProcDef -> Compiler (ProcDef,Bool,[TypeError])
typecheckProcDecl m pdef = do
    let name = procName pdef
    let proto = procProto pdef
    let params = procProtoParams proto
    let resources = procProtoResources proto
    let (ProcDefSrc def) = procImpln pdef
    let pos = procPos pdef
    let vis = procVis pdef
    if vis == Public && any ((==AnyType) . paramType) params
      then return (pdef,False,[ReasonUndeclared name pos])
      else do
        paramTyping <- foldM (addDeclaredType name pos (length params))
                  initTyping $ zip params [1..]
        resourceTyping <- foldM (addResourceType name pos) paramTyping resources
        if validTyping resourceTyping
          then do
            logTypes $ "** Type checking " ++ name ++ ": "
                       ++ show resourceTyping
            logTypes $ "   with resources: " ++ show resources
            let (calls,preTyping) = runState (bodyCalls def) resourceTyping
            calls' <- zipWith StmtTypings calls <$> mapM callProcInfos calls
            let badCalls = List.map typingStmt
                           $ List.filter (List.null . typingArgsTypes) calls'
            if List.null badCalls
              then do
                typing <- typecheckCalls m name pos calls' preTyping [] False
                
                logTypes $ "Typing independent of mode = " ++ show typing
                -- (typing''',def') <- typecheckProcDef m name pos preTyping def
                -- logTypes $ "*resulting types " ++ name ++ ": " ++ show typing'''
                if validTyping typing
                  then do
                    maybeDef <- modecheckStmts m name pos typing []
                                Set.empty def
                    case maybeDef of
                        OK (def',_) -> do
                          let params' = updateParamTypes typing params
                          let proto' = proto { procProtoParams = params' }
                          let pdef' = pdef { procProto = proto',
                                             procImpln = ProcDefSrc def' }
                          let sccAgain = pdef' /= pdef
                          logTypes $ "===== Definition is " ++
                              (if sccAgain then "" else "un") ++ "changed"
                          when sccAgain
                              (logTypes $ "** check again " ++ name ++
                               "\n-----------------OLD:"
                               ++ showProcDef 4 pdef ++
                               "\n-----------------NEW:"
                               ++ showProcDef 4 pdef' ++ "\n")
                          return (pdef',sccAgain,[])
                        Err lst -> do
                          logTypes $ "==== modecheck error " ++ show lst
                          return (pdef,False,lst)
                  else
                    return (pdef,False,typingErrs typing)
              else
                return (pdef,False,
                           List.map (\pcall ->
                                         case content pcall of
                                             ProcCall _ callee _ _ ->
                                                 ReasonUndef name callee
                                                 $ place pcall
                                             _ -> shouldnt "typecheckProcDecl")
                           badCalls)
          else
            return (pdef,False,typingErrs resourceTyping)


addDeclaredType :: ProcName -> OptPos -> Int -> Typing -> (Param,Int) ->
                   Compiler Typing
addDeclaredType procname pos arity typs (Param name typ flow _,argNum) = do
    typ' <- fromMaybe AnyType <$> lookupType typ pos
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
updateParamTypes typing =
    List.map (\p@(Param name typ fl afl) ->
               case varType name typing of
                   Nothing -> p
                   Just newTyp -> Param name newTyp fl afl)


-- Return a list of the statements (recursively) in a body that can
-- constrain types, paired with all the possible resolutions.
bodyCalls :: [Placed Stmt] -> State Typing [Placed Stmt]
bodyCalls [] = return []
bodyCalls (pstmt:pstmts) = do
    rest <- bodyCalls pstmts
    let stmt = content pstmt
    let pos  = place pstmt
    case stmt of
        ProcCall{} -> return $ pstmt:rest
        ForeignCall{} -> return rest -- no type constraints
        Test nested exp -> do
          modify $ addOneType (ReasonCond pos) (expVar $ content exp) boolType
          nested' <- bodyCalls nested
          return $ nested' ++ rest
        Nop -> return rest
        Cond cond exp thn els -> do
          modify $ addOneType (ReasonCond pos) (expVar $ content exp) boolType
          cond' <- bodyCalls cond
          thn' <- bodyCalls thn
          els' <- bodyCalls els
          return $ cond' ++ thn' ++ els' ++ rest
        Loop nested -> do
          nested' <- bodyCalls nested
          return $ nested' ++ rest
        For _ _ -> shouldnt "bodyCalls: flattening left For stmt"
        Break -> return rest
        Next ->  return rest


callTypes :: Placed Stmt -> Compiler [[TypeSpec]]
callTypes pstmt = nub . (procInfoTypes <$>) <$> callProcInfos pstmt


callProcInfos :: Placed Stmt -> Compiler [ProcInfo]
callProcInfos pstmt =
    case content pstmt of
        ProcCall m name procId _ -> do
          procs <- case procId of
              Nothing   -> callTargets m name
              Just pid -> return [ProcSpec m name pid] -- XXX check modspec
                                                       -- validity?
          zipWith ProcInfo procs <$>
              mapM (fmap (List.map paramTypeFlow
                             . List.filter nonResourceParam)
                       . getParams)
              procs
        stmt ->
          shouldnt $ "callProcInfo with non-call statement " ++ showStmt 4 stmt


-- Return the variable name of the supplied exp.  In this context,
-- the exp will always be a variable.
expVar :: Exp -> VarName
expVar (Var name _ _) = name
expVar (Typed exp _ _) = expVar exp
expVar exp = shouldnt $ "expVar of non-variable exp " ++ show exp


-- |Type check a list of statement typings, resulting in a typing of all
--  variables.  Input is a list of statement typings plus a variable typing,
--  output is a final variable typing.  We thread through a residue
--  list of unresolved statement typings; when we reach the end of the
--  main list of statement typings, we reprocess the residue, providing
--  the last pass has resolved some statements.  Thus we make multiple
--  passes over the list of statement typings until it is empty.
--
--  If we complee a pass over the list without resolving any statements
--  and a residue remains, then we pick a statement with the fewest remaining
--  types and try all the types in turn.  If exactly one of these leads to
--  a valid typing, this is the correct one; otherwise it is a type error.
--
--  To handle a single call, we find the types of all arguments as determined
--  by the current typing, and match this list against each of the candidate
--  statement typings, filtering out invalid possibilities.  If a single
--  possibility remains, we commit to this.  If multiple possibilities remain,
--  we keep all of them as a residue and continue with other statements.  If
--  no possibilities remain, we determine that the statement typing is
--  inconsistent with the initial variable typing (a type error).
typecheckCalls :: ModSpec -> ProcName -> OptPos -> [StmtTypings]
    -> Typing -> [StmtTypings] -> Bool -> Compiler Typing
typecheckCalls m name pos [] typing [] _ = return typing
typecheckCalls m name pos [] typing residue True =
    typecheckCalls m name pos residue typing [] False
typecheckCalls m name pos [] typing residue False =
    -- XXX Propagation alone is not always enough to determine a unique type.
    -- Need code to try to find a mode by picking a residual call with the
    -- fewest possibilities and try all combinations to see if exactly one
    -- of them gives us a valid typing.  If not, it's a type error.
    return $ typeErrors (List.map overloadErr residue) typing
typecheckCalls m name pos (stmtTyping@(StmtTypings pstmt typs):calls) typing
        residue chg = do
    let (callee,pexps) = case content pstmt of
                             ProcCall _ callee' _ pexps' -> (callee',pexps')
                             noncall -> shouldnt
                                        $ "typecheckCalls with non-call stmt"
                                          ++ show noncall
    actualTypes <- catMaybes <$> mapM (expType typing) pexps
    let matches = List.map (matchTypeList name callee (place pstmt) actualTypes)
                  typs
    let validMatches = catOKs matches
    case validMatches of
        [] -> return $ typeErrors (concatMap errList matches) typing
        [match] -> do
          let typing' = List.foldr (uncurry setExpType) typing
                        $ zip pexps $ procInfoTypes match
          typecheckCalls m name pos calls typing' residue True
        _ -> let stmtTyping' = stmtTyping {typingArgsTypes = validMatches}
             in typecheckCalls m name pos calls typing (stmtTyping':residue)
                $ chg || validMatches == typs
    

-- XXX Needed?
-- filterTypeList :: Ident -> [TypeSpec] -> StmtTypings
--                -> Compiler (MaybeErr StmtTypings)
-- filterTypeList caller callTypes stmtTyping@(StmtTypings pstmt typs) = do
--     let (callee,pexps) = case content pstmt of
--                              ProcCall _ callee' _ pexps' -> (callee',pexps')
--                              noncall -> shouldnt
--                                         $ "typecheckCalls with non-call stmt"
--                                           ++ show noncall
--     matchTypeList caller callee (place pstmt) callTypes typs


-- |Match up the argument types of a call with the parameter types of the
-- callee, producing a list of the actual types.  If this list contains
-- InvalidType, then the call would be a type error.
matchTypeList :: Ident -> Ident -> OptPos -> [TypeSpec] -> ProcInfo
              -> MaybeErr ProcInfo
matchTypeList caller callee pos callTypes calleeInfo
    | sameLength callTypes calleeTypes =
      let matches = List.zipWith meetTypes callTypes calleeTypes
          mismatches = List.map fst $ List.filter ((==InvalidType) . snd)
                       $ zip [1..] matches
      in if List.null mismatches
         then OK $ calleeInfo
              {procInfoArgs = List.zipWith TypeFlow matches calleeFlows}
         else Err [ReasonArgType callee n pos | n <- mismatches]
    | otherwise = Err [ReasonArity caller callee pos
                       (length callTypes) (length calleeTypes)]
    where args = procInfoArgs calleeInfo
          calleeTypes = typeFlowType <$> args
          calleeFlows = typeFlowMode <$> args



overloadErr :: StmtTypings -> TypeError
overloadErr (StmtTypings call candidates) =
    -- XXX Need to give list of matching procs
    ReasonOverload [] $ place call


-- |Given type assignments to variables, resolve modes in a proc body,
--  building a revised, properly moded body, or indicate a mode error.
--  This must handle several cases:
--  * Flow direction for function calls are unspecified; they must be assigned,
--    and may need to be postponed if the use appears before the definition.
--  * Test statements must be handled, determining which stmts in a test
--    context are actually tests, and reporting an error for tests outside
--    a test context
--  * Implied modes:  in a test context, allow in mode where out mode is
--    expected by assigning a fresh temp variable and generating an =
--    test of the variable against the in value.
--  * Handle in-out call mode where an out-only argument is expected.
--  This code threads a set of assigned variables through, which starts as
--  the set of in parameter names.  It also threads through a list of
--  statements postponed because an unknown flow variable is not assigned yet.
modecheckStmts :: ModSpec -> ProcName -> OptPos -> Typing
                 -> [Placed Stmt] -> Set VarName -> [Placed Stmt]
                 -> Compiler (MaybeErr ([Placed Stmt], Set VarName))
modecheckStmts m name pos typing delayed assigned []
    | List.null delayed = return $ OK ([],assigned)
    | otherwise =
        shouldnt $ "modecheckStmts reached end of proc with delayed stmts"
                   ++ show delayed
modecheckStmts m name pos typing delayed assigned (pstmt:pstmts) = do
    maybePStmt <- placedApply
                  (modecheckStmt m name pos typing delayed assigned)
                  pstmt
    case maybePStmt of
        OK (pstmt',delayed',assigned') -> do
          maybePStmts <- modecheckStmts m name pos typing
                         delayed' assigned' pstmts
          case maybePStmts of
              OK (pstmts',assigned'') ->
                  return $ OK (pstmt'++pstmts',assigned'')
              errs -> return errs
        Err errs -> return $ Err errs


modecheckStmt :: ModSpec -> ProcName -> OptPos -> Typing
                 -> [Placed Stmt] -> Set VarName -> Stmt -> OptPos
                 -> Compiler (MaybeErr ([Placed Stmt],
                                        [Placed Stmt], Set VarName))
modecheckStmt m name defPos typing delayed assigned
    stmt@(ProcCall cmod cname cid args) pos = do
    callInfos <- callProcInfos $ maybePlace stmt pos
    actualTypes <- catMaybes <$> mapM (expType typing) args
    let matches = List.map (matchTypeList name cname pos actualTypes)
                  callInfos
    -- let validMatches = catOKs matches
    return $ OK ([maybePlace Break pos],delayed,assigned)
  
modecheckStmt m name defPos typing delayed assigned stmt pos =
    return $ OK ([maybePlace stmt pos],delayed,assigned)


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
        logTypes "   no valid type"
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
    typings' <- mapM (`f` t) typings
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
    logTypes "Entering typecheckSequence from typecheckBody"
    typings' <- typecheckSequence (typecheckPlacedStmt m name)
                [typing] body
    logTypes $ "Body types: " ++ show typings'
    return typings'


-- |Type check a single placed primitive operation given a list of
--  possible starting typings and corresponding clauses up to this prim.
typecheckPlacedStmt :: ModSpec -> ProcName -> Typing -> Placed Stmt ->
                       Compiler [Typing]
typecheckPlacedStmt m caller typing pstmt =
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
                        then (s,if elt `elem` l then l else elt:l)
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
                                      (List.any (`elem` dups) . snd) $
                                    zip procs typList)
                                   pos) typing]
typecheckStmt _ _ call@(ForeignCall "llvm" "move" [] [a1,a2]) pos typing = do
  -- Ensure arguments have the same types
    logTypes $ "Type checking move instruction " ++ showStmt 4 call
    typing' <- matchTypes a1 a2 pos typing
    logTypes $ "Resulting typing = " ++ show typing'
    return [typing']
typecheckStmt _ _ call@(ForeignCall _ _ _ args) pos typing = do
    -- Pick up any output casts
    logTypes $ "Type checking foreign call " ++ showStmt 4 call
    let typing' = List.foldr (noteOutputCast . content) typing args
    logTypes $ "Resulting typing = " ++ show typing'
    return [typing']
typecheckStmt m caller (Test stmts exp) pos typing = do
    typings <- typecheckBody m caller typing stmts
    mapM (\t -> typecheckArg' (content exp) (place exp) AnyType
                (TypeSpec ["wybe"] "bool" []) t (ReasonCond pos))
        typings
typecheckStmt _ _ Nop pos typing = return [typing]
typecheckStmt m caller (Cond test exp thn els) pos typing = do
    typings <- typecheckSequence (typecheckPlacedStmt m caller) [typing] test
    typings' <- mapM (\t -> typecheckArg' (content exp) (place exp) AnyType
                            (TypeSpec ["wybe"] "bool" []) t (ReasonCond pos))
                typings
    typings'' <- typecheckSequence (typecheckPlacedStmt m caller) typings' thn
    typecheckSequence (typecheckPlacedStmt m caller) typings'' els
typecheckStmt m caller (Loop body) pos typing =
    typecheckSequence (typecheckPlacedStmt m caller) [typing] body
typecheckStmt m caller (For itr gen) pos typing =
    -- XXX must handle generator type
    return [typing]
typecheckStmt _ _ Break pos typing = return [typing]
typecheckStmt _ _ Next pos typing = return [typing]


matchingArgFlows :: ProcName -> ProcName -> [Placed Exp] -> OptPos -> Typing -> ProcSpec -> Compiler [Typing]
matchingArgFlows caller called args pos typing pspec = do
    params <- List.filter nonResourceParam <$> getParams pspec
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
    = (arg2:) <$> reconcileArgFlows params args
reconcileArgFlows (Param _ _ pflow _:params) (arg:args)
    = let aflow = expFlow (content arg)
      in if pflow == aflow || aflow == FlowUnknown
      then (arg:) <$> reconcileArgFlows params args
      else Nothing


-- |Does this parameter correspond to a manifest argument?
-- XXX this needs to filter out the output introduced for a test proc, too.
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
      typecheckArg' (content arg) (place arg) AnyType
        (paramType param) typing reasonType


typecheckArg' :: Exp -> OptPos -> TypeSpec -> TypeSpec -> Typing ->
                 TypeError -> Compiler Typing
typecheckArg' texp@(Typed exp typ cast) pos _ paramType typing reason = do
    logTypes $ "Checking typed expr " ++ show texp
    typ' <- fromMaybe AnyType <$> lookupType typ pos
    logTypes $ "Determined type " ++ show typ'
    let typ'' = if cast then AnyType else typ'
    logTypes $ "Considering casting, type is " ++ show typ''
    typecheckArg' exp pos typ'' paramType typing reason
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
      else if paramType == AnyType -- may be type checking recursion
           then return typing
           else return $ typeError reason typing
typecheckArg' (IntValue val) _ declType paramType typing reason =
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "int" [])
      typing reason
typecheckArg' (FloatValue val) _ declType paramType typing reason =
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "float" [])
      typing reason
typecheckArg' (StringValue val) _ declType paramType typing reason =
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "string" [])
      typing reason
typecheckArg' (CharValue val) _ declType paramType typing reason =
    return $ typecheckArg'' declType paramType (TypeSpec ["wybe"] "char" [])
      typing reason
typecheckArg' exp _ _ _ _ _ =
    shouldnt $ "trying to type check expression " ++ show exp ++ "."


typecheckArg'' :: TypeSpec -> TypeSpec -> TypeSpec -> Typing -> TypeError ->
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
    sum [if toFType e == HalfUpdate && toDirection e == FlowOut then 0 else 1
        | e <- lst]


applyBodyTyping :: Typing -> [Placed Stmt] -> Compiler [Placed Stmt]
applyBodyTyping typing =
    mapM (placedApply (applyStmtTyping typing))


applyStmtTyping :: Typing -> Stmt -> OptPos -> Compiler (Placed Stmt)
applyStmtTyping typing call@(ProcCall cm name id args) pos = do
    logTypes $ "typing call " ++ showStmt 4 call
    let args' = List.map (fmap $ applyExpTyping typing) args
    procs <- case id of
        Nothing   -> callTargets cm name
        Just n -> return [ProcSpec cm name n]
    logTypes $ "   " ++ show (length procs) ++ " potential procs: "
           ++ intercalate ", " (List.map show procs)
    matches <- catMaybes <$> mapM (matchProcType typing args') procs
    checkError (show (length matches) ++
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
applyStmtTyping typing Nop pos = return $ maybePlace Nop pos
applyStmtTyping typing (For itr gen) pos = do
    let itr' = fmap (applyExpTyping typing) itr
    let gen' = fmap (applyExpTyping typing) gen
    return $ maybePlace (For itr' gen') pos
applyStmtTyping typing Break pos = return $ maybePlace Break pos
applyStmtTyping typing Next pos = return $ maybePlace Next pos


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
    case varType nm typing of
        Nothing -> shouldnt $ "type of variable '" ++ nm ++ "' unknown"
        Just typ -> Typed exp typ False
applyExpTyping typing typed@(Typed _ _ True) =
    typed
applyExpTyping typing (Typed exp _ False) =
    applyExpTyping typing exp
applyExpTyping _ exp =
    shouldnt $ "Expression '" ++ show exp ++ "' left after flattening"


matchProcType :: Typing -> [Placed Exp] -> ProcSpec
              -> Compiler (Maybe ([Placed Exp], ProcSpec))
matchProcType typing args p = do
    params <- List.filter nonResourceParam <$> getParams p
    logTypes $ "   checking call to " ++
        show p ++ " args " ++
        show args ++ " against params " ++
        show params
    case reconcileArgFlows params args of
        Nothing -> return Nothing
        Just as -> do
            argTypes <- catMaybes <$> mapM (expType typing) as
            if all (uncurry subtypeOf)
                (zip argTypes (List.map paramType params))
                then return $ Just (as,p)
                else return Nothing


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
    mapM_ (placedApply (checkStmtTyped name pos)) $
          procDefSrc $ procImpln def


procDefSrc :: ProcImpln -> [Placed Stmt]
procDefSrc (ProcDefSrc def) = def
procDefSrc (ProcDefPrim _ _) = shouldnt "procDefSrc applied to ProcDefPrim"


checkParamTyped :: ProcName -> OptPos -> (Int,Param) -> Compiler ()
checkParamTyped name pos (num,param) =
    when (AnyType == paramType param) $
      reportUntyped name pos (" parameter " ++ show num)


checkStmtTyped :: ProcName -> OptPos -> Stmt -> OptPos -> Compiler ()
checkStmtTyped name pos (ProcCall pmod pname pid args) ppos = do
    when (isNothing pid || List.null pmod) $
         shouldnt $ "Call to " ++ pname ++ showMaybeSourcePos ppos ++
                  " left unresolved"
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped name pos (ForeignCall _ pname _ args) ppos =
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped name pos (Test stmts exp) ppos = do
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
    checkExpTyped name pos ("test" ++ showMaybeSourcePos ppos) $ content exp
checkStmtTyped name pos (Cond ifstmts cond thenstmts elsestmts) ppos = do
    mapM_ (placedApply (checkStmtTyped name pos)) ifstmts
    checkExpTyped name pos ("condition" ++ showMaybeSourcePos ppos) $
                  content cond
    mapM_ (placedApply (checkStmtTyped name pos)) thenstmts
    mapM_ (placedApply (checkStmtTyped name pos)) elsestmts
checkStmtTyped name pos (Loop stmts) ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
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
checkArgTyped callerName callerPos calleeName callPos (n,arg) =
    checkExpTyped callerName callerPos
                      ("in call to " ++ calleeName ++
                       showMaybeSourcePos callPos ++
                       ", arg " ++ show n) arg


checkExpTyped :: ProcName -> OptPos -> String -> Exp ->
                 Compiler ()
checkExpTyped _ _ _ Typed{} = return ()
checkExpTyped callerName callerPos msg _ =
    reportUntyped callerName callerPos msg


reportUntyped :: ProcName -> OptPos -> String -> Compiler ()
reportUntyped procname pos msg =
    liftIO $ putStrLn $ "Internal error: In " ++ procname ++
      showMaybeSourcePos pos ++ ", " ++ msg ++ " left untyped"


-- |Log a message, if we are logging type checker activity.
logTypes :: String -> Compiler ()
logTypes = logMsg Types

