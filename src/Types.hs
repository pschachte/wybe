--  File     : Types.hs
--  Author   : Peter Schachte
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

-- |Support for type checking/inference.
module Types (validateModExportTypes, typeCheckMod, -- modeCheckMod,
              checkFullyTyped) where

import           AST
import           Control.Monad.State
import           Data.Graph
import           Data.List           as List
import           Data.Map            as Map
import           Data.Maybe          as Maybe
import           Data.Set            as Set
import           Data.Tuple.Select
import           Data.Foldable
import           Options             (LogSelection (Types))
-- import           Resources
import           Util
import           Snippets
import           Blocks              (llvmMapBinop, llvmMapUnop)

-- import           Debug.Trace


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
    reexitModule
    logTypes $ "**** Re-exiting module " ++ showModSpec thisMod
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
    logTypes $ "Checking type " ++ show ty ++ " of param " ++ show param
    ty' <- fromMaybe AnyType <$> lookupType ty ppos
    let param' = param { paramType = ty' }
    logTypes $ "Param is " ++ show param'
    return param'


checkDeclIfPublic :: Ident -> OptPos -> Bool -> TypeSpec -> Compiler ()
checkDeclIfPublic pname ppos public ty =
    when (public && ty == AnyType) $
         message Error ("Public proc '" ++ pname ++
                        "' with undeclared parameter or return type") ppos


-- |Type check a single module.  Since all public procs/functions must have
-- their types fully declared, no fixpoint across modules is needed.  Our type
-- inference is flow sensitive, that is, types flow from callees to callers, but
-- not vice versa.  Therefore we analyse bottom-up by intra-module potential
-- call graph SCCs.  Type and mode inference are responsible for resolving
-- overloading, which means that the SCCs inferred at this point include all
-- *potential* calls, which are a superset of the actual calls.
typeCheckMod :: ModSpec -> Compiler ()
typeCheckMod thisMod = do
    logTypes $ "**** Type checking module " ++ showModSpec thisMod
    reenterModule thisMod
    procs <- getModuleImplementationField (Map.toList . modProcs)
    let ordered =
            stronglyConnComp
            [(name, name,
              Set.elems $ Set.unions
              $ List.map (localBodyProcs thisMod . procImpln) procDefs)
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
               | ReasonOutputUndef ProcName Ident OptPos
                   -- ^Output param not defined by proc body
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
                   -- ^Input param with undefined argument variable
               | ReasonUndefinedFlow ProcName OptPos
                   -- ^Call argument flow does not match any definition
               | ReasonOverload [ProcSpec] OptPos
                   -- ^Multiple procs with same types/flows
               | ReasonAmbig ProcName OptPos [(VarName,[TypeRef])]
                   -- ^Proc defn has ambiguous types
               | ReasonArity ProcName ProcName OptPos Int Int
                   -- ^Call to proc with wrong arity
               | ReasonUndeclared ProcName OptPos
                   -- ^Public proc with some undeclared types
               | ReasonEqual Exp Exp OptPos
                   -- ^Expression types should be equal
               | ReasonDeterminism ProcSpec Determinism Determinism OptPos
                   -- ^Calling a proc in a more deterministic context
               | ReasonPurity String Impurity Impurity OptPos
                   -- ^Calling a proc or foreign in a more pure context
               | ReasonForeignLanguage String String OptPos
                   -- ^Foreign call with bogus language
               | ReasonForeignArgType String Int OptPos
                   -- ^Foreign call with unknown argument type
               | ReasonForeignArity String Int Int OptPos
                   -- ^Foreign call with wrong arity
               | ReasonBadForeign String String OptPos
                   -- ^Unknown foreign llvm/lpvm instruction
               | ReasonResourceUndef ProcName Ident OptPos
                   -- ^Output resource not defined in proc body
               | ReasonResourceUnavail ProcName Ident OptPos
                   -- ^Input resource not available in proc call
               | ReasonWrongFamily Ident Int TypeFamily OptPos
                   -- ^LLVM instruction expected different argument family
               | ReasonIncompatible Ident TypeRepresentation
                 TypeRepresentation OptPos
                   -- ^Inconsistent arguments to binary LLVM instruction
               | ReasonWrongOutput Ident TypeRepresentation
                 TypeRepresentation OptPos
                   -- ^Wrong output type representation to LLVM instruction
               | ReasonForeignArgRep Ident Int TypeRepresentation
                 String OptPos
                   -- ^Foreign call with wrong argument type
               | ReasonShouldnt
                   -- ^This error should never happen
               deriving (Eq, Ord)


instance Show TypeError where
    show (ReasonParam name num pos) =
        makeMessage pos $
            "Type/flow error in definition of " ++ name ++
            ", parameter " ++ show num
    show (ReasonOutputUndef proc param pos) =
        makeMessage pos $
        "Output parameter " ++ param ++ " not defined by proc " ++ show proc
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
            "Uninitialised argument in call to " ++ name
            ++ ", argument " ++ show num
    show (ReasonUndefinedFlow name pos) =
        makeMessage pos $
            "No matching mode in call to " ++ name
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
            "'" ++ callTo ++ "' unknown in "
            ++ if callFrom == ""
               then "top-level statement"
               else "'" ++ callFrom ++ "'"
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
        "Type of " ++ show exp2 ++ " incompatible with " ++ show exp1
    show (ReasonDeterminism proc stmtDetism contextDetism pos) =
        makeMessage pos $
        "Calling " ++ determinismFullName stmtDetism ++ " proc "
        ++ show proc ++ " in a " ++ determinismFullName contextDetism ++ " context"
    show (ReasonPurity descrip stmtPurity contextPurity pos) =
        makeMessage pos $
        "Calling " ++ impurityFullName stmtPurity ++ " " ++descrip
        ++ " in a " ++ impurityFullName contextPurity ++ " context"
    show (ReasonForeignLanguage lang instr pos) =
        makeMessage pos $
        "Foreign call '" ++ instr ++ "' with unknown language '" ++ lang ++ "'"
    show (ReasonForeignArgType instr argNum pos) =
        makeMessage pos $
        "Foreign call '" ++ instr ++ "' with unknown type in argument "
        ++ show argNum
    show (ReasonForeignArity instr actualArity expectedArity pos) =
        makeMessage pos $
        "Foreign call '" ++ instr ++ "' with arity " ++ show actualArity
        ++ "; should be " ++ show expectedArity
    show (ReasonBadForeign lang instr pos) =
        makeMessage pos $
        "Unknown " ++ lang ++ " instruction '" ++ instr ++ "'"
    show (ReasonResourceUndef proc res pos) =
        makeMessage pos $
        "Output resource " ++ res ++ " not defined by proc " ++ proc
    show (ReasonResourceUnavail proc res pos) =
        makeMessage pos $
        "Input resource " ++ res ++ " not available at call to proc " ++ proc
    show (ReasonWrongFamily instr argNum fam pos) =
        makeMessage pos $
        "LLVM instruction '" ++ instr ++ "' argument " ++ show argNum
        ++ ": expected " ++ show fam ++ " argument"
    show (ReasonIncompatible instr rep1 rep2 pos) =
        makeMessage pos $
        "LLVM instruction '" ++ instr ++ "' inconsistent arguments "
        ++ show rep1 ++ " and " ++ show rep2
    show (ReasonWrongOutput instr wrongRep rightRep pos) =
        makeMessage pos $
        "LLVM instruction '" ++ instr ++ "' wrong output "
        ++ show wrongRep ++ ", should be " ++ show rightRep
    show (ReasonForeignArgRep instr argNum wrongRep rightDesc pos) =
        makeMessage pos $
        "LLVM instruction '" ++ instr ++ "' argument " ++ show argNum
        ++ " is " ++ show wrongRep ++ ", should be " ++ rightDesc
    show ReasonShouldnt =
        makeMessage Nothing "Mysterious typing error"



----------------------------------------------------------------
--                           Type Assignments
----------------------------------------------------------------

-- | A variable type assignment (symbol table), with a list of type errors.
data Typing = Typing {
                  typingDict::Map VarName TypeRef,
                  typingErrs::[TypeError]
                  }
            deriving (Eq,Ord)

instance Show Typing where
  show (Typing dict errs) =
    "Typing " ++ showVarMap dict
    ++ if List.null errs
       then " with no errors"
       else " with errors: " ++ show errs


-- |The empty typing, assigning every var the type AnyType.
initTyping :: Typing
initTyping = Typing Map.empty []


-- |Does this typing have no type errors?
validTyping :: Typing -> Bool
validTyping (Typing _ errs) = List.null errs


-- |Follow a chain of TypeRefs to find the final IndirectType reference.
--  This code also sort-circuits all the keys along the path to the
--  ultimate reference, where possible, so future lookups will be faster.
ultimateRef :: VarName -> Typing -> (VarName,Typing)
ultimateRef var typing
    = let (var',dict') = ultimateRef' var $ typingDict typing
      in  (var', typing {typingDict = dict' })

ultimateRef' :: VarName -> Map VarName TypeRef
             -> (VarName,Map VarName TypeRef)
ultimateRef' var dict
    = case Map.lookup var dict of
          Just (IndirectType v) ->
            let (var',dict') = ultimateRef' v dict
            in (var', Map.insert var (IndirectType var') dict')
          _ -> (var,dict)


-- |Get the type associated with a variable; AnyType if no constraint has
--  been imposed on that variable.
varType :: VarName -> Typing -> TypeSpec
varType var Typing{typingDict=dict} = varType' var dict


-- |Get the type associated with a variable; AnyType if no constraint has
--  been imposed on that variable.
varType' :: VarName -> Map VarName TypeRef -> TypeSpec
varType' var dict
    = case Map.findWithDefault (DirectType AnyType) var dict of
          DirectType t -> t
          IndirectType v -> varType' v dict


-- |Constrain the type of the specified variable to be a subtype of the
--  specified type.  If this produces an invalid type, the specified type
--  error describes the error.
constrainVarType :: TypeError -> VarName -> TypeSpec -> Typing -> Typing
constrainVarType reason var ty typing
    = let (var',typing') = ultimateRef var typing
      in  case meetTypes ty $ varType var' typing' of
          InvalidType -> typeError reason typing'
          newType -> typing {typingDict =
                                  Map.insert var' (DirectType newType)
                                  $ typingDict typing' }


-- |Constrain the types of the two specified variables to be identical,
--  even following further constraints on the types of either of the vars.
unifyVarTypes :: VarName -> VarName -> OptPos -> Typing -> Typing
unifyVarTypes var1 var2 pos typing
    = let (v1,typing1) = ultimateRef var1 typing
          (v2,typing2) = ultimateRef var2 typing1
          vLow =  min v1 v2
          vHigh = max v1 v2
      in case meetTypes (varType vLow typing2) (varType vHigh typing2) of
          InvalidType -> typeError
                         (ReasonEqual (varGet var1) (varGet var2) pos)
                         typing2
          newType -> typing2 {typingDict =
                              Map.insert vLow (DirectType newType)
                              $ Map.insert vHigh (IndirectType vLow)
                              $ typingDict typing2 }


typeError :: TypeError -> Typing -> Typing
typeError err = typeErrors [err]


typeErrors :: [TypeError] -> Typing -> Typing
typeErrors newErrs (Typing dict errs) = Typing dict $ newErrs ++ errs


-- |Returns the first argument restricted to the variables appearing in the
--  second. This must handle cases where variable appearing in chains of
--  indirections (equivalence classes of variables) are projected away.
projectTyping :: Typing -> Typing -> Typing
projectTyping (Typing typing errs) (Typing interest _) =
    -- Typing (Map.filterWithKey (\k _ -> Map.member k interest) typing) errs
    Typing (projectTypingDict (Map.keys interest) typing Map.empty Map.empty)
    errs


-- |Return a map containing the types of the first input map projected onto
-- the supplied list of variables (which is in ascending alphabetical
-- order) and maintaining the equivalences of the original. The second map
-- argument holds the translation from the smallest equivalent variable
-- name in the input map to the same for the result.
--
-- This works by traversing the list of variable names, looking up each in
-- the input map.  I
projectTypingDict :: [VarName] -> Map VarName TypeRef -> Map VarName TypeRef
                  -> Map VarName VarName -> Map VarName TypeRef
projectTypingDict [] _ result _ = result
projectTypingDict (v:vs) dict result renaming
    = let (v',dict') = ultimateRef' v dict
          ty = varType' v' dict
      in  case Map.lookup v' renaming of
              Nothing -> projectTypingDict vs dict
                         (Map.insert v (DirectType ty) result)
                         (Map.insert v' v renaming)
              Just v'' -> projectTypingDict vs dict
                         (Map.insert v (IndirectType v'') result) renaming


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
    && sameLength params1 params2
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


localBodyProcs :: ModSpec -> ProcImpln -> Set Ident
localBodyProcs thisMod (ProcDefSrc body) =
    foldStmts (localCalls thisMod) const Set.empty body
localBodyProcs thisMod (ProcDefPrim _ _ _ _) =
    shouldnt "Type checking compiled code"

localCalls :: ModSpec -> Set Ident -> Stmt -> Set Ident
localCalls thisMod idents (ProcCall m name _ _ _ _)
  | List.null m || m == thisMod = Set.insert name idents
localCalls _ idents _ = idents


expType :: Typing -> Placed Exp -> Compiler TypeSpec
expType typing expr = do
    logTypes $ "Finding type of expr " ++ show expr
    ty <- placedApply (expType' typing) expr
    logTypes $ "  Type = " ++ show ty
    return ty


expType' :: Typing -> Exp -> OptPos -> Compiler TypeSpec
expType' _ (IntValue _) _ = return $ TypeSpec ["wybe"] "int" []
expType' _ (FloatValue _) _ = return $ TypeSpec ["wybe"] "float" []
expType' _ (StringValue _) _ = return $ TypeSpec ["wybe"] "string" []
expType' _ (CharValue _) _ = return $ TypeSpec ["wybe"] "char" []
expType' typing (Var name _ _) _ = return $ varType name typing
expType' _ (Typed _ typ _) pos = fromMaybe AnyType <$> lookupType typ pos
expType' _ expr _ =
    shouldnt $ "Expression '" ++ show expr ++ "' left after flattening"


-- |Works out the declared flow direction of an actual parameter, paired
-- with whether or not the actual value is in fact available (is a constant
-- or a previously assigned variable), and with whether the call this arg
-- appears in should be delayed until this argument variable is assigned.
expMode :: BindingState -> Placed Exp -> (FlowDirection,Bool,Maybe VarName)
expMode assigned pexp = expMode' assigned $ content pexp

expMode' :: BindingState -> Exp -> (FlowDirection,Bool,Maybe VarName)
expMode' _ (IntValue _) = (ParamIn, True, Nothing)
expMode' _ (FloatValue _) = (ParamIn, True, Nothing)
expMode' _ (StringValue _) = (ParamIn, True, Nothing)
expMode' _ (CharValue _) = (ParamIn, True, Nothing)
expMode' assigned (Var name FlowUnknown _)
    = if name `assignedIn` assigned
      then (ParamIn, True, Nothing)
      else (FlowUnknown, False, Just name)
expMode' assigned (Var name flow _) =
    (flow, name `assignedIn` assigned, Nothing)
expMode' assigned (Typed expr _ _) = expMode' assigned expr
expMode' _ expr =
    shouldnt $ "Expression '" ++ show expr ++ "' left after flattening"


-- |Update the typing to assign the specified type to the specified expr
setExpType :: Exp -> OptPos -> TypeSpec -> Int -> ProcName -> Typing -> Typing
setExpType (IntValue _) _ _ _ _ typing = typing
setExpType (FloatValue _) _ _ _ _ typing = typing
setExpType (StringValue _) _ _ _ _ typing = typing
setExpType (CharValue _) _ _ _ _ typing = typing
setExpType (Var var _ _) pos typ argnum procName typing
    = constrainVarType (ReasonArgType procName argnum pos) var typ typing
setExpType (Typed expr _ _) pos typ argnum procName typing
    = setExpType expr pos typ argnum procName typing
setExpType otherExp _ _ _ _ _
    = shouldnt $ "Invalid expr left after flattening " ++ show otherExp

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
--  definitions stored in the Compiler monad.  Returns a pair of a Bool,
--  the first saying whether any defnition has been udpated, and the
--  second listing the type errors detected.
typecheckProcDecls :: ModSpec -> ProcName -> Compiler (Bool,[TypeError])
typecheckProcDecls m name = do
    logTypes $ "** Type checking decl of proc " ++ name
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


-- |An individual proc, its formal parameter types and modes, and determinism
data ProcInfo = ProcInfo {
  procInfoProc    :: ProcSpec,
  procInfoArgs    :: [TypeFlow],
  procInfoDetism  :: Determinism,
  procInfoImpurity:: Impurity,
  procInfoInRes   :: Set ResourceName,
  procInfoOutRes  :: Set ResourceName
  } deriving (Eq,Show)


procInfoTypes :: ProcInfo -> [TypeSpec]
procInfoTypes call = typeFlowType <$> procInfoArgs call


-- |Check if ProcInfo is for a proc with a single Bool output as last arg,
--  and if so, return Just the ProcInfo for the equivalent test proc
boolFnToTest :: ProcInfo -> Maybe ProcInfo
boolFnToTest pinfo@ProcInfo{procInfoDetism=Det, procInfoArgs=args}
    | List.null args = Nothing
    | last args == TypeFlow boolType ParamOut =
        Just $ pinfo {procInfoArgs=init args, procInfoDetism=SemiDet}
    | otherwise = Nothing
boolFnToTest _ = Nothing


-- |Check if ProcInfo is for a test proc, and if so, return a ProcInfo for
--  the Det proc with a single Bool output as last arg
testToBoolFn :: ProcInfo -> Maybe ProcInfo
testToBoolFn pinfo@ProcInfo{procInfoDetism=SemiDet, procInfoArgs=args}
    = Just $ pinfo {procInfoDetism=Det
                   ,procInfoArgs=args ++ [TypeFlow boolType ParamOut]}
testToBoolFn _ = Nothing


-- |A single call statement together with the determinism context in which
--  the call appears and a list of all the possible different parameter
--  list types (a list of types). This type is used to narrow down the
--  possible call typings.
data StmtTypings = StmtTypings {typingStmt::Placed Stmt,
                                typingDetism::Determinism,
                                typingArgsTypes::[ProcInfo]}
    deriving (Eq,Show)


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
    let detism = procDetism pdef
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
            logTypes $ "** Type checking proc " ++ name ++ ": "
                       ++ show resourceTyping
            logTypes $ "   with resources: " ++ show resources
            let (calls,preTyping) =
                  runState (bodyCalls def detism) resourceTyping
            logTypes $ "   containing calls: " ++ showBody 8 (fst <$> calls)
            let procCalls = List.filter (isRealProcCall . content . fst) calls
            let unifs = List.concatMap foreignTypeEquivs
                        ((content . fst) <$> calls)
            unifTyping <- foldM (\t (e1,e2) -> unifyExprTypes pos e1 e2 t)
                          preTyping unifs
            calls' <- zipWith (\(call,detism) typs ->
                                   StmtTypings call detism typs) procCalls
                      <$> mapM (callProcInfos . fst) procCalls
            let badCalls = List.map typingStmt
                           $ List.filter (List.null . typingArgsTypes) calls'
            if List.null badCalls
              then do
                typing <- typecheckCalls m name pos calls' unifTyping [] False

                logTypes $ "Typing independent of mode = " ++ show typing
                if validTyping typing
                  then do
                    logTypes $ "Now mode checking proc " ++ name
                    let inParams = Set.fromList $ paramName <$>
                          List.filter (flowsIn . paramFlow) params
                    let outParams = Set.fromList $ paramName <$>
                          List.filter (flowsOut . paramFlow) params
                    let inResources =
                          Set.map (resourceName . resourceFlowRes)
                          $ Set.filter (flowsIn . resourceFlowFlow) resources
                    let outResources =
                          Set.map (resourceName . resourceFlowRes)
                          $ Set.filter (flowsIn . resourceFlowFlow) resources
                    let initialised
                            = addBindings (inParams `Set.union` inResources)
                              $ initBindingState pdef
                    logTypes $ "Initialised vars: " ++ show initialised
                    (def',assigned,modeErrs0) <-
                      modecheckStmts m name pos typing [] initialised detism def
                    logTypes $ "Vars defined by body: " ++ show assigned
                    logTypes $ "Output parameters   : "
                               ++ intercalate ", " (Set.toList outParams)
                    logTypes $ "Output resources    : "
                               ++ intercalate ", " (Set.toList outResources)
                    let modeErrs =
                          [ReasonResourceUndef name res pos
                          | res <- Set.toList
                                   $ missingBindings outResources assigned]
                          ++
                          [ReasonOutputUndef name param pos
                          | param <- Set.toList
                                     $ missingBindings outParams assigned]
                          ++ modeErrs0
                    let typing' = typeErrors modeErrs typing
                    let params' = updateParamTypes typing' params
                    let proto' = proto { procProtoParams = params' }
                    let pdef' = pdef { procProto = proto',
                                       procImpln = ProcDefSrc def' }
                    let sccAgain = validTyping typing' && pdef' /= pdef
                    logTypes $ "===== "
                               ++ (if sccAgain then "" else "NO ")
                               ++ "Need to check again."
                    when sccAgain
                        (logTypes $ "\n-----------------OLD:"
                                    ++ showProcDef 4 pdef
                                    ++ "\n-----------------NEW:"
                                    ++ showProcDef 4 pdef' ++ "\n")
                    typing'' <-
                      foldlM (placedApply1 validateForeign) typing'
                      (List.filter (isForeign . content) def')
                    return (pdef',sccAgain,typingErrs typing'')
                  else
                    return (pdef,False,typingErrs typing)
              else
                return (pdef,False,
                           List.map (\pcall ->
                                         case content pcall of
                                             ProcCall _ callee _ _ _ _ ->
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
    return $ constrainVarType (ReasonParam procname arity pos) name typ' typs


addResourceType :: ProcName -> OptPos -> Typing -> ResourceFlowSpec ->
                   Compiler Typing
addResourceType procname pos typs rfspec = do
    let rspec = resourceFlowRes rfspec
    resIface <- lookupResource rspec pos
    let (rspecs,types) = unzip $ maybe [] (Map.toList . snd) resIface
    let names = List.map resourceName rspecs
    let typs' = List.foldr
                (\(n,t) typs ->
                     constrainVarType
                     (ReasonResource procname n pos) n t typs)
                typs $ zip names types
    return typs'


updateParamTypes :: Typing -> [Param] -> [Param]
updateParamTypes typing =
    List.map (\p@(Param name typ fl afl) ->
                  Param name (varType name typing) fl afl)


-- |Return a list of the proc and foreign calls recursively in a list of
--  statements, paired with all the possible resolutions.
bodyCalls :: [Placed Stmt] -> Determinism
          -> State Typing [(Placed Stmt, Determinism)]
bodyCalls [] _ = return []
bodyCalls (pstmt:pstmts) detism = do
    rest <- bodyCalls pstmts detism
    let stmt = content pstmt
    let pos  = place pstmt
    case stmt of
        ProcCall{} -> return $  (pstmt,detism):rest
        -- need to handle move instructions:
        ForeignCall{} -> return $ (pstmt,detism):rest
        TestBool _ -> return rest
        And stmts -> bodyCalls stmts detism
        Or stmts _ -> bodyCalls stmts detism
        Not stmt -> bodyCalls [stmt] detism
        Nop -> return rest
        Cond cond thn els _ -> do
          -- modify $ constrainVarType (ReasonCond pos)
          --          (expVar $ content expr) boolType
          cond' <- bodyCalls [cond] SemiDet
          thn' <- bodyCalls thn detism
          els' <- bodyCalls els detism
          return $ cond' ++ thn' ++ els' ++ rest
        Loop nested _ -> do
          nested' <- bodyCalls nested detism
          return $ nested' ++ rest
        UseResources _ nested -> do
          nested' <- bodyCalls nested detism
          return $ nested' ++ rest
        -- For _ _ -> shouldnt "bodyCalls: flattening left For stmt"
        Break -> return rest
        Next ->  return rest


-- |The statement is a ProcCall
isRealProcCall :: Stmt -> Bool
isRealProcCall ProcCall{} = True
isRealProcCall _ = False


-- |The statement is a ForeignCall
isForeign :: Stmt -> Bool
isForeign ForeignCall{} = True
isForeign _ = False


foreignTypeEquivs :: Stmt -> [(Placed Exp,Placed Exp)]
foreignTypeEquivs (ForeignCall "llvm" "move" _ [v1,v2]) = [(v1,v2)]
foreignTypeEquivs (ForeignCall "lpvm" "mutate" _ [v1,v2,_,_,_,_,_]) = [(v1,v2)]
foreignTypeEquivs _ = []


-- |Get matching ProcInfos for the supplied statement (which must be a call)
callProcInfos :: Placed Stmt -> Compiler [ProcInfo]
callProcInfos pstmt =
    case content pstmt of
        ProcCall m name procId _ _ _ -> do
          procs <- case procId of
              Nothing   -> callTargets m name
              Just pid -> return [ProcSpec m name pid generalVersion]
          defs <- mapM getProcDef procs
          return [ ProcInfo proc typflow detism imp inResources outResources
                 | (proc,def) <- zip procs defs
                 , let params = procProtoParams $ procProto def
                 , let (resourceParams,realParams) =
                         List.partition resourceParam params
                 , let typflow = paramTypeFlow <$> realParams
                 , let inResources =
                         Set.fromList $ paramName <$>
                         List.filter (flowsIn . paramFlow) resourceParams
                 , let outResources =
                         Set.fromList $ paramName <$>
                         List.filter (flowsOut . paramFlow) resourceParams
                 , let detism = procDetism def
                 , let imp = procImpurity def
                 ]
        stmt ->
          shouldnt $ "callProcInfos with non-call statement "
                     ++ showStmt 4 stmt


-- |Return the variable name of the supplied expr.  In this context,
--  the expr will always be a variable.
expVar :: Exp -> VarName
expVar expr = fromMaybe
              (shouldnt $ "expVar of non-variable expr " ++ show expr)
              $ expVar' expr


-- |Return the variable name of the supplied expr, if there is one.
expVar' :: Exp -> Maybe VarName
expVar' (Typed expr _ _) = expVar' expr
expVar' (Var name _ _) = Just name
expVar' _expr = Nothing


-- |Return the "primitive" expr of the specified expr.  This unwraps Typed
--  wrappers, giving the internal exp.
ultimateExp :: Exp -> Exp
ultimateExp (Typed expr _ _) = ultimateExp expr
ultimateExp expr = expr


-- |Type check a list of statement typings, resulting in a typing of all
--  variables.  Input is a list of statement typings plus a variable typing,
--  output is a final variable typing.  We thread through a residue
--  list of unresolved statement typings; when we reach the end of the
--  main list of statement typings, we reprocess the residue, providing
--  the last pass has resolved some statements.  Thus we make multiple
--  passes over the list of statement typings until it is empty.
--
--  If we complete a pass over the list without resolving any statements
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
typecheckCalls m name pos (stmtTyping@(StmtTypings pstmt detism typs):calls)
        typing residue chg = do
    logTypes $ "Type checking call " ++ show pstmt
    logTypes $ "Calling context is " ++ show detism
    logTypes $ "Candidate types: " ++ show typs
    -- XXX Must handle reification of test as a bool
    let (callee,pexps) = case content pstmt of
                             ProcCall _ callee' _ _ _ pexps' -> (callee',pexps')
                             noncall -> shouldnt
                                        $ "typecheckCalls with non-call stmt"
                                          ++ show noncall
    actualTypes <- mapM (expType typing) pexps
    logTypes $ "Actual types: " ++ show actualTypes
    let matches = List.map
                  (matchTypeList name callee (place pstmt) actualTypes detism)
                  typs
    let validMatches = catOKs matches
    let validTypes = nub $ procInfoTypes <$> validMatches
    logTypes $ "Valid types = " ++ show validTypes
    logTypes $ "Converted types = " ++ show (boolFnToTest <$> typs)
    case validTypes of
        [] -> do
          logTypes "Type error: no valid types for call"
          return $ typeErrors (concatMap errList matches) typing
        [match] -> do
          let typing' = List.foldr
                        (\ (pexp,ty,argnum) ->
                           placedApply setExpType pexp ty argnum name)
                        typing
                        $ zip3 pexps match [1..]
          logTypes $ "Resulting typing = " ++ show typing'
          typecheckCalls m name pos calls typing' residue True
        _ -> do
          let stmtTyping' = stmtTyping {typingArgsTypes = validMatches}
          typecheckCalls m name pos calls typing (stmtTyping':residue)
              $ chg || validMatches /= typs


-- |Match up the argument types of a call with the parameter types of the
-- callee, producing a list of the actual types.  If this list contains
-- InvalidType, then the call would be a type error.
matchTypeList :: Ident -> Ident -> OptPos -> [TypeSpec] -> Determinism
              -> ProcInfo -> MaybeErr ProcInfo
matchTypeList caller callee pos callArgTypes detismContext calleeInfo
    | sameLength callArgTypes args
    = matchTypeList' callee pos callArgTypes calleeInfo
    -- Handle case of SemiDet context call to bool function as a proc call
    | detismContext == SemiDet && isJust testInfo
      && sameLength callArgTypes (procInfoArgs calleeInfo')
    = matchTypeList' callee pos callArgTypes calleeInfo'
    -- Handle case of reified test call
    | isJust detCallInfo
      && sameLength callArgTypes (procInfoArgs calleeInfo'')
    = matchTypeList' callee pos callArgTypes calleeInfo''
    | otherwise = Err [ReasonArity caller callee pos
                       (length callArgTypes) (length args)]
    where args = procInfoArgs calleeInfo
          testInfo = boolFnToTest calleeInfo
          calleeInfo' = fromJust testInfo
          detCallInfo = testToBoolFn calleeInfo
          calleeInfo'' = fromJust detCallInfo

matchTypeList' :: Ident -> OptPos -> [TypeSpec] -> ProcInfo -> MaybeErr ProcInfo
matchTypeList' callee pos callArgTypes calleeInfo =
    if List.null mismatches
    then OK $ calleeInfo
         {procInfoArgs = List.zipWith TypeFlow matches calleeFlows}
    else Err [ReasonArgType callee n pos | n <- mismatches]
    where args = procInfoArgs calleeInfo
          calleeTypes = typeFlowType <$> args
          calleeFlows = typeFlowMode <$> args
          matches = List.zipWith meetTypes callArgTypes calleeTypes
          mismatches = List.map fst $ List.filter ((==InvalidType) . snd)
                       $ zip [1..] matches


----------------------------------------------------------------
--                            Mode Checking
--
-- Once type checking is complete and a unique type for each variable is
-- determined, we select the proc invoked at each call, and check that the code
-- is mode-correct, determinism-correct, and Impurity-correct.  Rather than
-- inferring mode, determinism, and Impurity, and then reporting errors where they
-- conflict with the declarations, our approach to checking these things is, as
-- much as possible, to point out the call that violates the declared
-- characteristics.  This is possible because mode, determinism, and Impurity must
-- be declared, and because most of these things are non-decreasing over
-- statement sequences.  For example, code that is SemiDet will not meet a call
-- that will suddenly make the statement sequence Det, nor will Impure code meet
-- a call that makes it Pure.  That means we can check code by simply reporting
-- the first call that violates the declared characteristic.  The exception to
-- this is that code that is Det or SemiDet does become Failure or Terminal by
-- meeting a call that is; we handle this by keeping track of whether or not a
-- sequence has included a Failure or Terminal call, and reporting if this
-- aspect was violated at the end of the sequence.
----------------------------------------------------------------


-- | A binding state reflects whether execution will reach a given program
-- point, if so, whether execution can succeed or fail, and if it can reach
-- there in success, the set of variables that will definitely be defined
-- (bound).  It comprises a determinism, the set of variables that will
-- definitely be bound at that program point, and the set of variables that
-- will definitely reach the loop exit point.  For both sets of variables,
-- Nothing indicates the universal set.

data BindingState = BindingState {
        bindingDetism    :: Determinism,
        bindingImpurity  :: Impurity,
        bindingVars      :: Maybe (Set VarName),
        bindingBreakVars :: Maybe (Set VarName)
        }


-- | Nicely show a set, given the supplied fn to show each element
showSet :: (a -> String) -> Set a -> String
showSet showFn set =
    "{" ++ intercalate ", " (showFn <$> Set.toList set) ++ "}"


-- | Nicely show a Maybe set, given the supplied fn to show each element.
-- Nothing is treated as signifying the universal set.
showMaybeSet :: (a -> String) -> Maybe (Set a) -> String
showMaybeSet f Nothing = "Everything"
showMaybeSet f (Just set) = showSet f set


instance Show BindingState where
    show (BindingState detism impurity boundVars breakVars) =
        impurityFullName impurity ++ " "
        ++ determinismFullName detism ++ " computation binding "
        ++ showMaybeSet id boundVars ++ ", break set = "
        ++ showMaybeSet id breakVars


impurityFullName :: Impurity -> String
impurityFullName Pure = "pure"
impurityFullName PromisedPure = "promised pure"
impurityFullName impurity = impurityName impurity


-- | A determinism name suitable for user messages
determinismFullName :: Determinism -> String
determinismFullName Det = "normal (total)"
determinismFullName detism = determinismName detism

-- | Is this binding state guaranteed to succeed?
mustSucceed :: BindingState -> Bool
mustSucceed = (==Det) . bindingDetism


-- | Is this binding state guaranteed to fail?
mustFail :: BindingState -> Bool
mustFail = (==Failure) . bindingDetism


-- | Initial BindingState with nothing bound and no breaks seen
initBindingState :: ProcDef -> BindingState
initBindingState pdef =
    BindingState Det impurity (Just Set.empty) Nothing
    where impurity = expectedImpurity $ procImpurity pdef


-- | The intersection of two Maybe (Set a), where Nothing denotes the universal
-- set.
intersectMaybeSets :: Ord a => Maybe (Set a) -> Maybe (Set a) -> Maybe (Set a)
intersectMaybeSets Nothing mset = mset
intersectMaybeSets mset Nothing = mset
intersectMaybeSets (Just mset1) (Just mset2) =
    Just $ Set.intersection mset1 mset2


-- | the join of two BindingStates.
joinState :: BindingState -> BindingState -> BindingState
joinState (BindingState detism1 impurity1 boundVars1 breakVars1)
          (BindingState detism2 impurity2 boundVars2 breakVars2) =
          (BindingState detism  impurity  boundVars  breakVars )
  where detism    = determinismJoin detism1 detism2
        impurity    = max impurity1 impurity2
        breakVars = breakVars1 `intersectMaybeSets` breakVars2
        boundVars = boundVars1 `intersectMaybeSets` boundVars2


-- | Add some bindings to a BindingState
addBindings :: Set VarName -> BindingState -> BindingState
addBindings vars st@BindingState{bindingDetism=Terminal} = st
addBindings vars st@BindingState{bindingDetism=Failure}  = st
addBindings vars st@BindingState{bindingDetism=Det} =
    st {bindingVars=(vars `Set.union`) <$> bindingVars st}
addBindings vars st@BindingState{bindingDetism=SemiDet} =
    -- Was:  BindingState Det ((vars `Set.union`) <$> boundVars) breakVars: always force Det?
    st {bindingVars=(vars `Set.union`) <$> bindingVars st}


-- | Returns the deterministic version of the specified binding state.
forceDet :: BindingState -> BindingState
forceDet st =
    st {bindingDetism = bindingDetism st `determinismMeet` Det}


-- | Returns the definitely failing version of the specified binding state.
forceFailure :: BindingState -> BindingState
forceFailure st =
        st {bindingDetism = bindingDetism st `determinismMeet` Failure}


-- | Returns the binding state after a statement with the specified determinism that
--   definitely binds the specified variables.
bindingStateSeq :: Determinism -> Impurity -> Set VarName -> BindingState
                -> BindingState
bindingStateSeq stmtDetism impurity outputs st =
    st {bindingDetism=detism', bindingImpurity=impurity', bindingVars=vars'}
  where detism' = bindingDetism st `determinismSeq` stmtDetism
        impurity' = bindingImpurity st `impuritySeq` impurity
        vars'   = if determinismTerminal $ bindingDetism st 
                  then Nothing
                  else (outputs `Set.union`) <$> bindingVars st


-- | Returns the binding state after a statement with the specified determinism that
--   definitely binds the specified variables.
bindingStateAfterNext :: BindingState -> BindingState
bindingStateAfterNext st = st {bindingDetism=Terminal, bindingVars=Nothing}


-- | Returns the binding state after a statement with the specified determinism that
--   definitely binds the specified variables.
bindingStateAfterBreak :: BindingState -> BindingState
bindingStateAfterBreak st =
    st {bindingDetism=Terminal, bindingVars=Nothing, bindingBreakVars=bvars}
    where bvars = bindingVars st `intersectMaybeSets` bindingBreakVars st


-- | which of a set of expected bindings will be unbound if execution reach this
-- binding state
missingBindings :: Set VarName -> BindingState -> Set VarName
missingBindings vars st = maybe Set.empty (vars Set.\\) $ bindingVars st


-- | Is the specified variable defined in the specified binding state?
assignedIn :: VarName -> BindingState -> Bool
assignedIn var bstate = maybe True (var `elem`) $ bindingVars bstate


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if all actual arguments are instantiated
-- if the corresponding parameter is an input.
matchModeList :: [(FlowDirection,Bool,Maybe VarName)]
              -> ProcInfo -> Bool
matchModeList modes ProcInfo{procInfoArgs=typModes}
    -- Check that no param is in where actual is out
    = (ParamIn,ParamOut) `notElem` argModes
    where argModes = zip (typeFlowMode <$> typModes) (sel1 <$> modes)


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if the call mode exactly matches the
-- proc mode, treating a FlowUnknown argument as ParamOut.
exactModeMatch :: [(FlowDirection,Bool,Maybe VarName)]
               -> ProcInfo -> Bool
exactModeMatch modes ProcInfo{procInfoArgs=typModes}
    = all (\(formal,actual) -> formal == actual
                               || formal == ParamOut && actual == FlowUnknown)
      $ zip (typeFlowMode <$> typModes) (sel1 <$> modes)


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if the call mode exactly matches the
-- proc mode, treating a FlowUnknown argument as ParamOut.
delayModeMatch :: [(FlowDirection,Bool,Maybe VarName)]
               -> ProcInfo -> Bool
delayModeMatch modes ProcInfo{procInfoArgs=typModes}
    = all (\(formal,actual) -> formal == actual
                               || actual == FlowUnknown
                               && (formal == ParamIn || formal == ParamOut))
      $ zip (typeFlowMode <$> typModes) (sel1 <$> modes)


overloadErr :: StmtTypings -> TypeError
overloadErr StmtTypings{typingStmt=call,typingArgsTypes=candidates} =
    -- XXX Need to give list of matching procs
    ReasonOverload (procInfoProc <$> candidates) $ place call


-- |Given type assignments to variables, resolve modes in a proc body,
--  building a revised, properly moded body, or indicate a mode error.
--  This must handle several cases:
--  * Flow direction for function calls are unspecified; they must be assigned,
--    and may need to be delayed if the use appears before the definition.
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
                 -> [(Set VarName,Placed Stmt)] -> BindingState -> Determinism
                 -> [Placed Stmt]
                 -> Compiler ([Placed Stmt], BindingState, [TypeError])
modecheckStmts _ _ _ _ delayed assigned _ []
    | List.null delayed = return ([],assigned,[])
    | otherwise =
        shouldnt $ "modecheckStmts reached end of body with delayed stmts:\n"
                   ++ show delayed
modecheckStmts m name pos typing delayed assigned detism (pstmt:pstmts) = do
    logTypes $ "Mode check stmt " ++ showStmt 16 (content pstmt)
    (pstmt',delayed',assigned', errs') <-
      placedApply (modecheckStmt m name pos typing delayed assigned detism)
        pstmt
    logTypes $ "New errors   = " ++ show errs'
    logTypes $ "Now assigned = " ++ show assigned'
    logTypes $ "Now delayed  = " ++ show delayed'
    let (doNow,delayed'')
            = List.partition
              (Set.null . (`missingBindings` assigned') . fst)
              delayed'
    (pstmts',assigned'', errs) <-
      modecheckStmts m name pos typing delayed'' assigned' detism
        ((snd <$> doNow) ++ pstmts)
    return (pstmt'++pstmts',assigned'', errs'++errs)


-- |Mode check a single statement, returning a list of moded statements,
--  plus a list of delayed statements, a set of variables bound by this
--  statement, and a list of type (mode) errors.
--
--  We select a mode as follows:
--    0.  If some input arguments are not assigned, report an uninitialised
--        variable error.
--    1.  If there is an exact match for the current instantiation state
--        (treating any FlowUnknown args as ParamIn), select it.
--    2.  If this is a test context and there is a match for the current
--        instantiation state (treating any FlowUnknown args as ParamIn
--        and allowing ParamIn arguments where the parameter is ParamOut),
--        select it, and transform by replacing each non-identical flow
--        ParamIn argument with a fresh ParamOut variable, and adding a
--        = test call to test the fresh variable against the actual ParamIn
--        argument.
--    3.  If there is a match (possibly with some ParamIn args where
--        ParamOut is expected) treating any FlowUnknown args as ParamOut,
--        then select that mode but delay the call.
--    4.  Otherwise report a mode error.
--
--    In case there are multiple modes that match one of those criteria,
--    select the first that matches.
modecheckStmt :: ModSpec -> ProcName -> OptPos -> Typing
                 -> [(Set VarName,Placed Stmt)] -> BindingState -> Determinism
                 -> Stmt -> OptPos
                 -> Compiler ([Placed Stmt], [(Set VarName,Placed Stmt)],
                              BindingState, [TypeError])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(ProcCall cmod cname _ _ resourceful args) pos = do
    logTypes $ "Mode checking call   : " ++ show stmt
    logTypes $ "    with assigned    : " ++ show assigned
    callInfos <- callProcInfos $ maybePlace stmt pos
    actualTypes <- mapM (expType typing) args
    let actualModes = List.map (expMode assigned) args
    let flowErrs = [ReasonArgFlow cname num pos
                   | ((mode,avail,_),num) <- zip actualModes [1..]
                   , mode == ParamIn && not avail]
    if not $ List.null flowErrs -- Using undefined var as input?
        then do
            logTypes $ "Unpreventable mode errors: " ++ show flowErrs
            return ([],delayed,assigned,flowErrs)
        else do
            let typeMatches = catOKs
                      $ List.map
                        (matchTypeList name cname pos actualTypes detism)
                        callInfos
            -- All the possibly matching modes
            let modeMatches
                    = List.filter (matchModeList actualModes) typeMatches
            logTypes $ "Actual types         : " ++ show actualTypes
            logTypes $ "Actual call modes    : " ++ show actualModes
            logTypes $ "Type-correct modes   : " ++ show typeMatches
            logTypes $ "Possible mode matches: " ++ show modeMatches
            let exactMatches
                    = List.filter (exactModeMatch actualModes) modeMatches
            logTypes $ "Exact mode matches: " ++ show exactMatches
            case exactMatches of
                (match:_) -> do
                  let matchProc = procInfoProc match
                  let matchDetism = procInfoDetism match
                  let matchImpurity = procInfoImpurity match
                  let impurity = bindingImpurity assigned
                  let args' = List.zipWith setPExpTypeFlow
                              (procInfoArgs match) args
                  let stmt' = ProcCall (procSpecMod matchProc)
                              (procSpecName matchProc)
                              (Just $ procSpecID matchProc)
                              matchDetism resourceful args'
                  let errs =
                        -- XXX Should postpone detism errors until we see if we
                        -- can work out if the test is certain to succeed.
                        -- Perhaps add mutual exclusion inference to the mode
                        -- checker.
                        [ReasonDeterminism matchProc matchDetism detism pos
                        | not (matchDetism `determinismLEQ` detism)]
                        ++ [ReasonPurity ("proc " ++ show matchProc)
                            matchImpurity impurity pos
                           | not (matchImpurity <= impurity)]
                        ++ [ReasonResourceUnavail name res pos
                           | res <- Set.toList
                              $ missingBindings (procInfoInRes match) assigned]
                  let assigned' =
                        bindingStateSeq matchDetism matchImpurity
                        (pexpListOutputs args') assigned
                  return ([maybePlace stmt' pos],delayed,assigned',errs)
                [] -> if List.any (delayModeMatch actualModes) modeMatches
                      then do
                        logTypes $ "delaying call: " ++ ": " ++ show stmt
                        let vars = Set.fromList $ catMaybes
                                   $ sel3 <$> actualModes
                        let delayed' = (vars,maybePlace stmt pos):delayed
                        logTypes $ "delayed = " ++ show delayed'
                        return ([],delayed',assigned,[])
                      else do
                        logTypes $ "Mode errors in call:  " ++ show flowErrs
                        return ([],delayed,assigned,
                                [ReasonUndefinedFlow cname pos])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(ForeignCall lang cname flags args) pos = do
    logTypes $ "Mode checking foreign call " ++ show stmt
    logTypes $ "    with assigned " ++ show assigned
    actualTypes <- mapM (expType typing) args
    let actualModes = List.map (expMode assigned) args
    let flowErrs = [ReasonArgFlow ("foreign " ++ lang ++ " " ++ cname) num pos
                   | ((mode,avail,_yy),num) <- zip actualModes [1..]
                   , not avail && mode == ParamIn]
    if not $ List.null flowErrs -- Using undefined var as input?
        then do
            logTypes "delaying foreign call"
            return ([],delayed,assigned,flowErrs)
        else do
            let typeflows = List.zipWith TypeFlow actualTypes
                            $ sel1 <$> actualModes
            let actualImpurity = flagsImpurity flags
            let impurity = bindingImpurity assigned
            let errs = [ReasonPurity ("foreign " ++ cname)
                        actualImpurity impurity pos
                       | not (actualImpurity <= impurity)]
            let args' = List.zipWith setPExpTypeFlow typeflows args
            let stmt' = ForeignCall lang cname flags args'
            let assigned' = pexpListOutputs args'
            logTypes $ "New instr = " ++ show stmt'
            return ([maybePlace stmt' pos],delayed,
                    addBindings assigned' assigned,errs)
modecheckStmt _ _ _ _ delayed assigned _ Nop pos = do
    logTypes $ "Mode checking Nop"
    return ([maybePlace Nop pos], delayed, assigned,[])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(Cond tstStmt thnStmts elsStmts _) pos = do
    logTypes $ "Mode checking conditional " ++ show stmt
    (tstStmt', delayed', assigned1, errs1) <-
      placedApplyM (modecheckStmt m name defPos typing delayed assigned SemiDet)
      tstStmt
    logTypes $ "Assigned by test: " ++ show assigned1
    (thnStmts', assigned2, errs2) <-
      modecheckStmts m name defPos typing []
      (forceDet assigned1) detism thnStmts
    logTypes $ "Assigned by then branch: " ++ show assigned2
    (elsStmts', assigned3, errs3) <-
      modecheckStmts m name defPos typing [] assigned detism elsStmts
    logTypes $ "Assigned by else branch: " ++ show assigned3
    if mustSucceed assigned1 -- is condition guaranteed to succeed?
      then do
        logTypes $ "Assigned by succeeding conditional: " ++ show assigned2
        return (tstStmt'++thnStmts', delayed'++delayed, assigned2, errs1++errs2)
      else if mustFail assigned1 -- is condition guaranteed to fail?
      then do
        logTypes $ "Assigned by failing conditional: " ++ show assigned3
        return (tstStmt'++elsStmts', delayed'++delayed, assigned3, errs1++errs3)
      else do
        let finalAssigned = assigned2 `joinState` assigned3
        logTypes $ "Assigned by conditional: " ++ show finalAssigned
        let vars = Map.fromSet (`varType` typing) <$> bindingVars finalAssigned
        return
          ([maybePlace (Cond (seqToStmt tstStmt') thnStmts' elsStmts' vars)
            pos],
           delayed'++delayed, finalAssigned, errs1++errs2++errs3)
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(TestBool exp) pos = do
    logTypes $ "Mode checking test " ++ show exp
    let exp' = [maybePlace
                (TestBool (content
                           $ setPExpTypeFlow (TypeFlow boolType ParamIn)
                             (maybePlace exp pos)))
                 pos]
    case expIsConstant exp of
      Just (IntValue 0) -> return (exp', delayed, forceFailure assigned, [])
      Just (IntValue 1) -> return ([maybePlace Nop pos],
                                   delayed, assigned, [])
      _                  -> return (exp', delayed,
                                    bindingStateSeq SemiDet Pure Set.empty 
                                    assigned, [])
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(Loop stmts _) pos = do
    logTypes $ "Mode checking loop " ++ show stmt
    (stmts', assigned', errs') <-
      modecheckStmts m name defPos typing [] assigned detism stmts
    logTypes $ "Assigned by loop: " ++ show assigned'
    let break = bindingBreakVars assigned'
    let vars = Map.fromSet (`varType` typing) <$> break
    logTypes $ "Loop exit vars: " ++ show vars
    return ([maybePlace (Loop stmts' vars) pos],
            delayed, assigned', errs')
-- XXX Need to implement these:
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(UseResources resources stmts) pos = do
    logTypes $ "Mode checking use ... in stmt " ++ show stmt
    (stmts', assigned', errs') <-
      modecheckStmts m name defPos typing [] assigned detism stmts
    return ([maybePlace (UseResources resources stmts') pos],
            delayed, assigned', errs')
-- XXX Need to implement these:
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(And stmts) pos = do
    logTypes $ "Mode checking conjunction " ++ show stmt
    (stmts', assigned', errs') <-
      modecheckStmts m name defPos typing [] assigned detism stmts
    return ([maybePlace (And stmts') pos], delayed, assigned', errs')
modecheckStmt m name defPos typing delayed assigned detism
    stmt@(Or stmts _) pos = do
    logTypes $ "Mode checking disjunction " ++ show stmt
    -- XXX must mode check individually and join the resulting states
    (stmts', assigned', errs') <-
      modecheckStmts m name defPos typing [] assigned detism stmts
    let vars = Map.fromSet (`varType` typing) <$> bindingVars assigned'
    return ([maybePlace (Or stmts' vars) pos], delayed,
            assigned', errs')
modecheckStmt m name defPos typing delayed assigned detism
    (Not stmt) pos = do
    logTypes $ "Mode checking negation " ++ show stmt
    (stmt', delayed', _, errs') <-
      placedApplyM (modecheckStmt m name defPos typing [] assigned detism) stmt
    return ([maybePlace (Not (seqToStmt stmt')) pos],
            delayed'++delayed, assigned, errs')
-- modecheckStmt m name defPos typing delayed assigned detism
--     stmt@(For gen stmts) pos = nyi "mode checking For"
modecheckStmt m name defPos typing delayed assigned detism
    Break pos = do
    logTypes $ "Mode checking break with assigned=" ++ show assigned
    return ([maybePlace Break pos],delayed,bindingStateAfterBreak assigned,[])
modecheckStmt m name defPos typing delayed assigned detism
    Next pos = do
    logTypes $ "Mode checking continue with assigned=" ++ show assigned
    return ([maybePlace Next pos],delayed,bindingStateAfterNext assigned,[])


selectMode :: [ProcInfo] -> [(FlowDirection,Bool,Maybe VarName)]
           -> ProcInfo
selectMode (procInfo:_) _ = procInfo
selectMode _ _ = shouldnt "selectMode with empty list of modes"


-- |Ensure the two exprs have the same types; if both are variables, this
--  means unifying their types.
unifyExprTypes :: OptPos -> Placed Exp -> Placed Exp -> Typing
               -> Compiler Typing
unifyExprTypes pos a1 a2 typing = do
    let args = [a1,a2]
    let call = ForeignCall "llvm" "move" [] args
    logTypes $ "Type checking foreign instruction unifying arguments "
               ++ show a1 ++ " and " ++ show a2
    let typing' = List.foldr (noteOutputCast . content) typing args
    let a1Content = content a1
    case expVar' $ content a2 of
        -- XXX Need new error for move to non-variable
        Nothing -> return
                   $ typeError (shouldnt $ "move to non-variable" ++ show call)
                     typing'
        Just toVar ->
          case ultimateExp a1Content of
              Var fromVar _ _ -> do
                let typing'' = unifyVarTypes fromVar toVar pos typing'
                logTypes $ "Resulting typing = " ++ show typing''
                return typing''
              _ -> do
                ty <- expType typing' (Unplaced a1Content)
                logTypes $ "constraining var " ++ show toVar
                           ++ " to type " ++ show ty
                return $ constrainVarType
                         (ReasonEqual a1Content (content a2) (place a2))
                         toVar ty typing'


noteOutputCast :: Exp -> Typing -> Typing
noteOutputCast (Typed (Var name flow _) typ True) typing
  | flowsOut flow = constrainVarType ReasonShouldnt name typ typing
noteOutputCast _ typing = typing


-- |Does this parameter correspond to a manifest argument?
resourceParam :: Param -> Bool
resourceParam (Param _ _ _ (Resource _)) = True
resourceParam _ = False


----------------------------------------------------------------
--                    Check foreign calls
----------------------------------------------------------------

-- | Add the specified type error if the specified test fails
reportErrorUnless :: TypeError -> Bool -> Typing -> Typing
reportErrorUnless err False typing = typeError err typing
reportErrorUnless err True typing = typing


-- | Make sure a foreign call is valid; otherwise report an error
validateForeign :: Typing -> Stmt -> OptPos -> Compiler Typing
validateForeign typing stmt@(ForeignCall lang name tags args) pos = do
    argTypes <- mapM (expType typing) args
    maybeReps <- mapM lookupTypeRepresentation argTypes
    let numberedMaybes = zip maybeReps [1..]
    let untyped = snd <$> List.filter (isNothing . fst) numberedMaybes
    if List.null untyped
      then do
        let argReps = List.filter (not . repIsPhantom)
                      $ trustFromJust "validateForeign" <$> maybeReps
        logTypes $ "Type checking foreign " ++ lang ++ " call "
                   ++ unwords (name:tags)
                   ++ "(" ++ intercalate ", " (show <$> argReps) ++ ")"
        validateForeignCall lang name tags argReps stmt pos typing
      else
        return $ typeErrors
                 (flip (ReasonForeignArgType name) pos <$> untyped)
                 typing
validateForeign typing stmt _ =
    shouldnt $ "validateForeign of non-foreign stmt " ++ showStmt 4 stmt


-- | Make sure a foreign call is valid; otherwise report an error
-- XXX Check that the outputs of LLVM instructions are correct, after
--     considering casting.
validateForeignCall :: String -> ProcName -> [String] -> [TypeRepresentation]
                    -> Stmt -> OptPos -> Typing -> Compiler Typing
-- just assume C calls are OK
validateForeignCall "c" _ _ _ _ _ typing = return typing
-- A move with no non-phantom arguments:  all OK
validateForeignCall "llvm" "move" _ [] stmt pos typing = return typing
validateForeignCall "llvm" "move" _ [inRep,outRep] stmt pos typing
  | inRep == outRep = return typing
  | otherwise       = return
                      $ typeError (ReasonWrongOutput "move" outRep inRep pos)
                        typing
validateForeignCall "llvm" "move" _ argReps stmt pos typing =
    return $ typeError (ReasonForeignArity "move" (length argReps) 2 pos) typing
validateForeignCall "llvm" name flags argReps stmt pos typing = do
    let arity = length argReps
    return $
      case argReps of
        [inRep1,inRep2,outRep] ->
          case Map.lookup name llvmMapBinop of
             Just (_,fam,outTy) ->
               reportErrorUnless (ReasonWrongFamily name 1 fam pos)
               (fam == typeFamily inRep1)
               $ reportErrorUnless (ReasonWrongFamily name 2 fam pos)
                 (fam == typeFamily inRep2)
               $ reportErrorUnless (ReasonIncompatible name inRep1 inRep2 pos)
                 (compatibleReps inRep1 inRep2)
               typing
             Nothing ->
               if isJust $ Map.lookup name llvmMapUnop
               then typeError (ReasonForeignArity name arity 2 pos) typing
               else typeError (ReasonBadForeign "llvm" name pos) typing
        [inRep,outRep] ->
          case Map.lookup name llvmMapUnop of
             Just (_,famIn,famOut) ->
               reportErrorUnless (ReasonWrongFamily name 1 famIn pos)
               (famIn == typeFamily inRep)
               typing
             Nothing ->
               if isJust $ Map.lookup name llvmMapBinop
               then typeError (ReasonForeignArity name arity 3 pos) typing
               else typeError (ReasonBadForeign "llvm" name pos) typing
        _ -> if isJust $ Map.lookup name llvmMapBinop
             then typeError (ReasonForeignArity name arity 3 pos) typing
             else if isJust $ Map.lookup name llvmMapUnop
                  then typeError (ReasonForeignArity name arity 2 pos) typing
                  else typeError (ReasonBadForeign "llvm" name pos) typing
validateForeignCall "lpvm" name flags argReps stmt pos typing =
    return $ checkLPVMArgs name flags argReps stmt pos typing
validateForeignCall lang name flags argReps stmt pos typing =
    return $ typeError (ReasonForeignLanguage lang name pos) typing


-- | Are two types compatible for use as inputs to a binary LLVM op?
--   Used for type checking LLVM instructions.
compatibleReps :: TypeRepresentation -> TypeRepresentation -> Bool
compatibleReps Address           Address           = True
compatibleReps Address           (Bits wordSize)   = True
compatibleReps Address           (Signed wordSize) = True
compatibleReps Address           (Floating _)      = False
compatibleReps (Bits wordSize)   Address           = True
compatibleReps (Bits m)          (Bits n)          = m == n
compatibleReps (Bits m)          (Signed n)        = m == n
compatibleReps (Bits _)          (Floating _)      = False
compatibleReps (Signed wordSize) Address           = True
compatibleReps (Signed m)        (Bits n)          = m == n
compatibleReps (Signed m)        (Signed n)        = m == n
compatibleReps (Signed _)        (Floating _)      = False
compatibleReps (Floating _)      Address           = False
compatibleReps (Floating _)      (Bits _)          = False
compatibleReps (Floating _)      (Signed _)        = False
compatibleReps (Floating m)      (Floating n)      = m == n


-- | Check arg types of an LPVM instruction
checkLPVMArgs :: String -> [String] -> [TypeRepresentation] -> Stmt -> OptPos
              -> Typing -> Typing
-- XXX must check arg type representations
checkLPVMArgs "alloc" _ [Bits _,Address] stmt pos typing = typing
checkLPVMArgs "alloc" _ [Signed _,Address] stmt pos typing = typing
checkLPVMArgs "alloc" _ [sz,struct] stmt pos typing =
    reportErrorUnless (ReasonForeignArgRep "alloc" 1 sz "integer" pos)
    (integerTypeRep sz)
    $ reportErrorUnless (ReasonForeignArgRep "alloc" 2 struct "address" pos)
      (struct == Address)
      typing
checkLPVMArgs "alloc" _ args stmt pos typing =
    typeError (ReasonForeignArity "alloc" (length args) 2 pos) typing
checkLPVMArgs "access" _ [struct,offset,size,startOffset,val] stmt pos typing =
    reportErrorUnless (ReasonForeignArgRep "access" 1 struct "address" pos)
    (struct == Address)
    $ reportErrorUnless (ReasonForeignArgRep "access" 2 offset "integer" pos)
      (integerTypeRep offset)
    $ reportErrorUnless
      (ReasonForeignArgRep "access" 3 startOffset "integer" pos)
      (integerTypeRep startOffset)
    $ reportErrorUnless (ReasonForeignArgRep "access" 4 size "integer" pos)
      (integerTypeRep size)
    typing
checkLPVMArgs "access" _ args stmt pos typing =
    typeError (ReasonForeignArity "access" (length args) 5 pos) typing
checkLPVMArgs "mutate" _ [old,new,offset,destr,sz,start,val] stmt pos typing =
    reportErrorUnless (ReasonForeignArgRep "mutate" 1 old "address" pos)
    (old == Address)
    $ reportErrorUnless (ReasonForeignArgRep "mutate" 2 new "address" pos)
      (new == Address)
    $ reportErrorUnless (ReasonForeignArgRep "mutate" 3 offset "integer" pos)
      (integerTypeRep offset)
    $ reportErrorUnless (ReasonForeignArgRep "mutate" 4 destr "Boolean" pos)
      (integerTypeRep destr)
    $ reportErrorUnless (ReasonForeignArgRep "mutate" 5 sz "integer" pos)
      (integerTypeRep sz)
    $ reportErrorUnless (ReasonForeignArgRep "mutate" 6 start "integer" pos)
      (integerTypeRep start)
      typing
checkLPVMArgs "mutate" _ args stmt pos typing =
    typeError (ReasonForeignArity "mutate" (length args) 7 pos) typing
-- XXX do we still need a cast instruction?
checkLPVMArgs "cast" _ [old,new] stmt pos typing = typing
checkLPVMArgs "cast" _ [] stmt pos typing = typing
checkLPVMArgs "cast" _ args stmt pos typing =
    typeError (ReasonForeignArity "cast" (length args) 2 pos) typing
checkLPVMArgs name _ args stmt pos typing =
    typeError (ReasonBadForeign "lpvm" name pos) typing

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
procDefSrc (ProcDefPrim _ _ _ _) = shouldnt "procDefSrc applied to ProcDefPrim"


checkParamTyped :: ProcName -> OptPos -> (Int,Param) -> Compiler ()
checkParamTyped name pos (num,param) =
    when (AnyType == paramType param) $
      reportUntyped name pos (" parameter " ++ show num)


checkStmtTyped :: ProcName -> OptPos -> Stmt -> OptPos -> Compiler ()
checkStmtTyped name pos (ProcCall pmod pname pid _ _ args) ppos = do
    when (isNothing pid || List.null pmod) $
         shouldnt $ "Call to " ++ pname ++ showMaybeSourcePos ppos ++
                  " left unresolved"
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped name pos (ForeignCall _ pname _ args) ppos =
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped _ _ (TestBool _) _ = return ()
checkStmtTyped name pos (And stmts) _ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos stmt@(Or stmts exitVars) _ppos = do
    when (isNothing exitVars) $
         shouldnt $ "exit vars of disjunction undetermined: " ++ showStmt 4 stmt
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (Not stmt) _ppos =
    placedApply (checkStmtTyped name pos) stmt
checkStmtTyped name pos stmt@(Cond tst thenstmts elsestmts exitVars) _ppos = do
    when (isNothing exitVars) $
         shouldnt $ "exit vars of conditional undetermined: " ++ showStmt 4 stmt
    placedApply (checkStmtTyped name pos) tst
    mapM_ (placedApply (checkStmtTyped name pos)) thenstmts
    mapM_ (placedApply (checkStmtTyped name pos)) elsestmts
checkStmtTyped name pos stmt@(Loop stmts exitVars) _ppos = do
    when (isNothing exitVars) $
         shouldnt $ "exit vars of loop undetermined: " ++ showStmt 4 stmt
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (UseResources _ stmts) _ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
-- checkStmtTyped name pos (For itr gen) ppos = do
--     checkExpTyped name pos ("for iterator" ++ showMaybeSourcePos ppos) $
--                   content itr
--     checkExpTyped name pos ("for generator" ++ showMaybeSourcePos ppos) $
--                   content itr
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
checkExpTyped callerName callerPos msg (Typed expr ty _)
    | ty /= AnyType = checkExpModed callerName callerPos msg expr
checkExpTyped callerName callerPos msg _ =
    reportUntyped callerName callerPos msg


checkExpModed :: ProcName -> OptPos -> String -> Exp
              -> Compiler ()
checkExpModed callerName callerPos msg (Var _ FlowUnknown _)
    = liftIO $ putStrLn $ "Internal error: In " ++ callerName ++
      showMaybeSourcePos callerPos ++ ", " ++ msg ++ " left with FlowUnknown"
checkExpModed _ _ _ _ = return ()



reportUntyped :: ProcName -> OptPos -> String -> Compiler ()
reportUntyped procname pos msg =
    liftIO $ putStrLn $ "Internal error: In " ++ procname ++
      showMaybeSourcePos pos ++ ", " ++ msg ++ " left untyped"


-- |Log a message, if we are logging type checker activity.
logTypes :: String -> Compiler ()
logTypes = logMsg Types
