--  File     : Types.hs
--  Author   : Peter Schachte
--  Purpose  : Type checker/inferencer for Wybe
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE TupleSections #-}

-- |Support for type checking/inference.
module Types (validateModExportTypes, typeCheckModSCC) where


import           AST
import           Debug.Trace
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Extra (ifM)
import           Data.Graph
import           Data.List           as List
import           Data.Map            as Map
import           Data.Maybe          as Maybe
import           Data.Either         as Either
import           Data.Set            as Set
import           UnivSet             as USet
import           Data.Tuple.Select
import           Data.Foldable
import           Data.Bifunctor
import           Data.Functor        ((<&>))
import           Data.Function       (on)
import           Options             (LogSelection (Types))
import           Resources
import           Util
import           Config
import           Snippets
import           Blocks              (llvmMapBinop, llvmMapUnop)
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
    params' <- mapM (updatePlacedM $ validateParamType name pos public) params
    return $ def { procProto = proto { procProtoParams = params' }}


validateParamType :: Ident -> OptPos -> Bool -> Param -> Compiler Param
validateParamType pname ppos public param = do
    let ty = paramType param
    checkDeclIfPublic pname ppos public ty
    logTypes $ "Checking type " ++ show ty ++ " of param " ++ show param
    ty' <- lookupType "proc declaration" ppos ty
    let param' = param { paramType = ty' }
    logTypes $ "Param is " ++ show param'
    return param'


checkDeclIfPublic :: Ident -> OptPos -> Bool -> TypeSpec -> Compiler ()
checkDeclIfPublic pname ppos public ty =
    when (public && ty == AnyType) $
         message Error ("Public proc '" ++ pname ++
                        "' with undeclared parameter or return type") ppos


----------------------------------------------------------------
-- BEGIN MAJOR DOC
-- ###                 Type Checking Module SCCs
--
-- Our type inference is flow sensitive, that is, types flow from callees to
-- callers, but not vice versa.  Therefore, types must be uniquely determined by
-- proc definitions.
--
-- Because submodules in a file automatically have access to all items (even
-- private ones) in their supermodule, submodules in that file are considered to
-- depend on their supermodules.  Likewise, supermodules automatically import
-- everything exported by their submodules in the same file, so supermodules
-- depend on their submodules. This means all modules in a given file are always
-- in the same module dependency SCC.  Since SCCs are type checked in
-- topological order, this ensures that all proc calls can only refer to procs
-- that have already been type checked or are defined in the current SCC.
--
-- Type checking is responsible for overloading resolution, therefore during
-- type checking, there may be multiple possible procs that could be referenced
-- by an individual call.  To support this, we use a type RoughProcSpec which
-- represents a proc as best we are able to identify it.  This is only used
-- during type checking to determine potential call graph SCCs.  Type
-- checking/inference is then performed bottom-up by potential call graph SCC.
--
-- Handling of resources here is a little tricky, because resources in lower
-- SCCs will have been transformed into parameters, but resources in the current
-- SCC will not have been transformed.  This problem is unavoidable because types
-- must be determined (so that overloading can be resolved) before resources can
-- be transformed.  Therefore, type checking must be prepared to handle both
-- calls that have had resources transformed to parameters and calls that
-- haven't.

-- END MAJOR DOC
----------------------------------------------------------------

-- |Specify as much as we know about the proc referred to by a proc call
data RoughProcSpec = RoughProc {
    roughModule  :: ModSpec,   -- the module specified in the call
    roughName    :: ProcName   -- the proc name specified in the call
} deriving (Eq,Ord)

instance Show RoughProcSpec where
    show (RoughProc mod name) = maybeModPrefix mod ++ name


-- |Type check a single module dependency SCC.
typeCheckModSCC :: [ModSpec] -> Compiler ()
typeCheckModSCC scc = do
    logTypes $ "**** Type checking modules " ++ showModSpecs scc
    procs <- concat <$> mapM modProcsDefs scc
    let unresolved = [(spec, spec,
              Set.elems $ Set.unions
              $ List.map (localBodyProcs . procImpln) procDefs)
             | (spec,procDefs) <- procs]
    resolutions <- mapM (resolveCalls $ Set.fromList scc) unresolved
    let ordered = stronglyConnComp resolutions
    logTypes $ "**** Strongly connected components:\n" ++
      intercalate "\n"
       (List.map (("    " ++) . intercalate ", " . List.map show . sccElts)
       ordered)
    errs <- concat <$> mapM typecheckProcSCC ordered
    mapM_ (queueMessage . typeErrorMessage) errs


-- |Return the module, name, and defn of all procs in the specified module
modProcsDefs :: ModSpec -> Compiler [(RoughProcSpec,[ProcDef])]
modProcsDefs mod =
    List.map (first (RoughProc mod)) <$>
    (getModuleImplementationField (Map.toList . modProcs) `inModule` mod)


-- |Work out all the possible resolutions of all the calls in dependency triple.
resolveCalls :: Set ModSpec -> (RoughProcSpec,RoughProcSpec,[RoughProcSpec])
             -> Compiler (RoughProcSpec,RoughProcSpec,[RoughProcSpec])
resolveCalls mods (spec,spec2,deps) = do
    let m = roughModule spec
    deps' <- concat <$> mapM (callResolutions m mods) deps
    return (spec,spec2,deps')


-- |Find all rough procs that a call could be referring to, given the module in
-- which the call appears, filtered to include only procs in the specified list
-- of modules, all of which are imported into the context module.  The
-- RoughProcSpec of the call may not include a module spec, but the specified
-- context will be a proper ModSpec.
callResolutions :: ModSpec -> Set ModSpec -> RoughProcSpec
                -> Compiler [RoughProcSpec]
callResolutions context mods (RoughProc m name) = do
    pspecs <- callTargets m name `inModule` context
    return [RoughProc m name
           | ProcSpec m name _ _ <- pspecs
           , m `Set.member` mods
           ]


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
data TypeError = ReasonMessage Message
                   -- ^Error originating from Message
               | ReasonParam ProcName Int OptPos
                   -- ^Formal param type/flow inconsistent
               | ReasonOutputUndef ProcName Ident OptPos
                   -- ^Output param not defined by proc body
               | ReasonUndef ProcName ProcName OptPos
                   -- ^Call to unknown proc
               | ReasonArgType Bool ProcName Int OptPos
                   -- ^Actual param type inconsistent
               | ReasonCond OptPos
                   -- ^Conditional expression not bool
               | ReasonArgFlow ProcName Int OptPos
                   -- ^Input param with undefined argument variable
               | ReasonUndefinedFlow ProcName OptPos
                   -- ^Call argument flow does not match any definition
               | ReasonOverload [String] OptPos
                   -- ^Multiple procs with same types/flows
               | ReasonWarnMultipleMatches CallInfo [CallInfo] OptPos
                   -- ^Warn multiple procs with same types/flows
                   -- XXX remove when handling multiple matches is better defined
               | ReasonAmbig ProcName OptPos [(VarName,[TypeSpec])]
                   -- ^Proc defn has ambiguous types
               | ReasonArity ProcName ProcName OptPos Int Int
                   -- ^Call to proc with wrong arity
               | ReasonUndeclared ProcName OptPos
                   -- ^Public proc with some undeclared types
               | ReasonEqual Exp Exp OptPos
                   -- ^Expression types should be equal
               | ReasonExpType Exp TypeSpec OptPos
                   -- ^Expression should have a Boolean type
               | ReasonHigher ProcName ProcName OptPos
                   -- ^ Expression does not have correct higher type
               | ReasonHigherFlow ProcName ProcName Int FlowDirection FlowDirection OptPos
                   -- ^ Expression does not have correct higher type
               | ReasonPartialFlow ProcName ProcName Int FlowDirection OptPos
                   -- ^ ProcSpec does not have the correct type, in context
               | ReasonDeterminism String Determinism Determinism OptPos
                   -- ^Calling a proc in a more deterministic context
               | ReasonWeakDetism String Determinism Determinism OptPos
                   -- ^Actual determinism of proc body weaker than declared
               | ReasonPurity String Impurity Impurity OptPos
                   -- ^Calling a proc or foreign in a more pure context
               | ReasonLooksPure ProcName Impurity OptPos
                   -- ^Calling a not-pure proc without ! marker
               | ReasonForeignLanguage String String OptPos
                   -- ^Foreign call with bogus language
               | ReasonForeignArgType String Int OptPos
                   -- ^Foreign call with unknown argument type
               | ReasonForeignArity String Int Int OptPos
                   -- ^Foreign call with wrong arity
               | ReasonBadForeign String String OptPos
                   -- ^Unknown foreign llvm/lpvm instruction
               | ReasonBadMove Exp OptPos
                   -- ^Instruction moves value to a non-variable
               | ReasonResourceDef ProcName ResourceSpec OptPos
                   -- ^Declared resource inconsistent
               | ReasonResourceUndef ProcName Ident OptPos
                   -- ^Output resource not defined in proc body
               | ReasonResourceUnavail ProcName Ident OptPos
                   -- ^Input resource not available in proc call
               | ReasonResourceOutOfScope ProcName ResourceSpec OptPos
                   -- ^Resource not in scope in proc call
               | ReasonUseType ResourceSpec OptPos
                   -- ^Type of resource in use stmt inconsistent with other use
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
               | ReasonBadCast Ident Ident Int OptPos
                   -- ^Cast operation appearing in non-foreign call argument
               | ReasonBadConstraint Ident Ident Int Exp TypeSpec OptPos
                   -- ^Type constraint on exp is invalid
               | ReasonShouldnt
                   -- ^This error should never happen
               | ReasonActuallyPure ProcName Impurity OptPos
                   -- ^Calling a pure proc with unneeded ! marker
            --    | ReasonUndeclaredTerminal ProcName OptPos
            --        -- ^The proc is terminal but not declared so
               | ReasonUnnreachable ProcName OptPos
                   -- ^Statement following a terminal statement
               deriving (Eq, Ord)


instance Show TypeError where
    show = show . typeErrorMessage


-- |Produce a Message to be stored from a TypeError.
typeErrorMessage :: TypeError -> Message
typeErrorMessage (ReasonMessage msg) = msg
typeErrorMessage (ReasonParam name num pos) =
    Message Error pos $
        "Type/flow error in definition of " ++ showProcName name ++
        ", parameter " ++ show num
typeErrorMessage (ReasonOutputUndef proc param pos) =
    Message Error pos $
        "Output parameter " ++ param ++ " not defined by proc "
        ++ showProcName proc
typeErrorMessage (ReasonArgType isPartial name num pos) =
    Message Error pos $
        "Type error in " ++
        (if isPartial then "partial application of " else "call to ")
        ++ name ++ ", argument " ++ show num
typeErrorMessage (ReasonCond pos) =
    Message Error pos
        "Conditional or test expression with non-boolean result"
typeErrorMessage (ReasonArgFlow name num pos) =
    Message Error pos $
        "Uninitialised argument in call to " ++ name
        ++ ", argument " ++ show num
typeErrorMessage (ReasonUndefinedFlow name pos) =
    Message Error pos $
        "No matching mode in call to " ++ name
typeErrorMessage (ReasonOverload infos pos) =
    Message Error pos $
        "Ambiguous overloading: call could refer to:" ++
        List.concatMap ("\n    "++) (reverse infos)
typeErrorMessage (ReasonWarnMultipleMatches match rest pos) =
    Message Warning pos $
        "Multiple procedures match this call's types and flows:" ++
        List.concatMap (("\n    "++) . show)
                       (fiProc <$> (match:rest))
        ++ "\nDefaulting to: " ++ show (fiProc match)
typeErrorMessage (ReasonAmbig procName pos varAmbigs) =
    Message Error pos $
        "Type ambiguity in defn of " ++ procName ++ ":" ++
        concat ["\n    Variable '" ++ v ++ "' could be: " ++
                intercalate ", " (List.map show typs)
                | (v,typs) <- varAmbigs]
typeErrorMessage (ReasonUndef callFrom callTo pos) =
    Message Error pos $
        "'" ++ callTo ++ "' unknown in " ++ showProcName callFrom
typeErrorMessage (ReasonArity callFrom callTo pos callArity procArity) =
    Message Error pos $
        "Call from " ++ showProcName callFrom
        ++ " to " ++ callTo ++ " with " ++
        (if callArity == procArity
            then "unsupported argument flow"
            else show callArity ++ " argument(s), expected " ++ show procArity)
typeErrorMessage (ReasonUndeclared name pos) =
    Message Error pos $
        "Public definition of '" ++ name ++ "' with some undeclared types."
typeErrorMessage (ReasonEqual exp1 exp2 pos) =
    Message Error pos $
        "Type of " ++ show exp2 ++ " incompatible with " ++ show exp1
typeErrorMessage (ReasonExpType exp ty pos) =
    Message Error pos $
        "Type of " ++ show exp ++ " incompatible with " ++ show ty
typeErrorMessage (ReasonHigher callFrom callTo pos) =
    Message Error pos $
        "Higher order call to " ++ showProcName callTo ++ " in "
        ++ showProcName callFrom ++ " has a type/flow error."
typeErrorMessage (ReasonHigherFlow callFrom callTo idx flow expected pos) =
    Message Error pos $
        "Higher order call to " ++ showProcName callTo ++ " in "
        ++ showProcName callFrom ++ " has "
        ++ showFlowName flow ++ " flow for argument "
        ++ show idx ++ ", but expects "
        ++ showFlowName expected ++ " flow."
typeErrorMessage (ReasonPartialFlow from to idx flow pos) =
    Message Error pos $
        "Partial application of " ++ to ++ " in "
        ++ showProcName from ++ " has flow " ++ flowPrefix flow
        ++ " but should be an input."
typeErrorMessage (ReasonDeterminism name stmtDetism contextDetism pos) =
    Message Error pos $
        "Calling " ++ determinismFullName stmtDetism ++ " " ++ name
        ++ " in a " ++ determinismFullName contextDetism ++ " context"
typeErrorMessage (ReasonWeakDetism name actualDetism expectedDetism pos) =
    Message Error pos $
        name ++ " has " ++ determinismFullName actualDetism
        ++ " determinism, but declared " ++ determinismFullName expectedDetism
typeErrorMessage (ReasonPurity descrip stmtPurity contextPurity pos) =
    Message Error pos $
        "Calling " ++ impurityFullName stmtPurity ++ " " ++ descrip
        ++ ", expecting at least " ++ impurityFullName contextPurity
typeErrorMessage (ReasonLooksPure name impurity pos) =
    Message Error pos $
        "Calling " ++ impurityFullName impurity ++ " " ++ name
        ++ " without ! non-purity marker"
typeErrorMessage (ReasonForeignLanguage lang instr pos) =
    Message Error pos $
        "Foreign call '" ++ instr ++ "' with unknown language '" ++ lang ++ "'"
typeErrorMessage (ReasonForeignArgType instr argNum pos) =
    Message Error pos $
        "Foreign call '" ++ instr ++ "' with unknown type in argument "
        ++ show argNum
typeErrorMessage (ReasonForeignArity instr actualArity expectedArity pos) =
    Message Error pos $
        "Foreign call '" ++ instr ++ "' with arity " ++ show actualArity
        ++ "; should be " ++ show expectedArity
typeErrorMessage (ReasonBadForeign lang instr pos) =
    Message Error pos $
        "Unknown " ++ lang ++ " instruction '" ++ instr ++ "'"
typeErrorMessage (ReasonBadMove dest pos) =
    Message Error pos $
        "Instruction moves result to non-variable expression " ++ show dest
typeErrorMessage (ReasonResourceDef name res pos) =
    Message Error pos $
        "Type/flow error in definition of " ++ showProcName name ++
        ", resource " ++ show res
typeErrorMessage (ReasonResourceUndef proc res pos) =
    Message Error pos $
        "Output resource " ++ res ++ " not defined by proc " ++ proc
typeErrorMessage (ReasonResourceUnavail proc res pos) =
    Message Error pos $
        "Input resource " ++ res ++ " not available at call to proc " ++ proc
typeErrorMessage (ReasonResourceOutOfScope proc res pos) =
    Message Error pos $
        "Resource " ++ show res ++ " not in scope at call to proc " ++ proc
typeErrorMessage (ReasonUseType res pos) =
    Message Error pos $
        "Inconsistent type of resource " ++ show res ++ " in use statement"
typeErrorMessage (ReasonWrongFamily instr argNum fam pos) =
    Message Error pos $
        "LLVM instruction '" ++ instr ++ "' argument " ++ show argNum
        ++ ": expected " ++ show fam ++ " argument"
typeErrorMessage (ReasonIncompatible instr rep1 rep2 pos) =
    Message Error pos $
        "LLVM instruction '" ++ instr ++ "' inconsistent arguments "
        ++ show rep1 ++ " and " ++ show rep2
typeErrorMessage (ReasonWrongOutput instr wrongRep rightRep pos) =
    Message Error pos $
        "LLVM instruction '" ++ instr ++ "' wrong output "
        ++ show wrongRep ++ ", should be " ++ show rightRep
typeErrorMessage (ReasonForeignArgRep instr argNum wrongRep rightDesc pos) =
    Message Error pos $
        "LLVM instruction '" ++ instr ++ "' argument " ++ show argNum
        ++ " is " ++ show wrongRep ++ ", should be " ++ rightDesc
typeErrorMessage (ReasonBadCast caller callee argNum pos) =
    Message Error pos $
        "Type cast (:!) in call from " ++ showProcName caller
        ++ " to non-foreign " ++ callee ++ ", argument " ++ show argNum
typeErrorMessage (ReasonBadConstraint caller callee argNum exp ty pos) =
    Message Error pos $
        "Type constraint (:" ++ show ty ++ ") in call from " ++ showProcName caller
        ++ " to " ++ callee ++ ", argument " ++ show argNum
        ++ ", is incompatible with expression " ++ show exp
typeErrorMessage ReasonShouldnt =
    Message Error Nothing "Mysterious typing error"
typeErrorMessage (ReasonActuallyPure name impurity pos) =
    Message Warning pos $
        "Calling " ++ showProcName name ++ " with unneeded ! marker"
-- XXX These won't work until we better infer terminalness
-- typeErrorMessage (ReasonUndeclaredTerminal name pos) =
--     Message Warning pos $
--         "Proc " ++ name ++ " should be declared terminal"
typeErrorMessage (ReasonUnnreachable name pos) =
    Message Warning pos $
        "In " ++ showProcName name ++ ", this statement is unreachable"


-- | Get the position from a type error
typeErrorPos :: TypeError -> OptPos
typeErrorPos (ReasonMessage (Message _ pos _)) = pos
typeErrorPos (ReasonParam _ _ pos) = pos
typeErrorPos (ReasonOutputUndef _ _ pos) = pos
typeErrorPos (ReasonUndef _ _ pos) = pos
typeErrorPos (ReasonArgType _ _ _ pos) = pos
typeErrorPos (ReasonCond pos) = pos
typeErrorPos (ReasonArgFlow _ _ pos) = pos
typeErrorPos (ReasonUndefinedFlow _ pos) = pos
typeErrorPos (ReasonOverload _ pos) = pos
typeErrorPos (ReasonWarnMultipleMatches _ _ pos) = pos
typeErrorPos (ReasonAmbig _ pos _) = pos
typeErrorPos (ReasonArity _ _ pos _ _) = pos
typeErrorPos (ReasonUndeclared _ pos) = pos
typeErrorPos (ReasonEqual _ _ pos) = pos
typeErrorPos (ReasonExpType _ _ pos) = pos
typeErrorPos (ReasonHigher _ _ pos) = pos
typeErrorPos (ReasonHigherFlow _ _ _ _ _ pos) = pos
typeErrorPos (ReasonPartialFlow _ _ _ _ pos) = pos
typeErrorPos (ReasonDeterminism _ _ _ pos) = pos
typeErrorPos (ReasonWeakDetism _ _ _ pos) = pos
typeErrorPos (ReasonPurity _ _ _ pos) = pos
typeErrorPos (ReasonLooksPure _ _ pos) = pos
typeErrorPos (ReasonForeignLanguage _ _ pos) = pos
typeErrorPos (ReasonForeignArgType _ _ pos) = pos
typeErrorPos (ReasonForeignArity _ _ _ pos) = pos
typeErrorPos (ReasonBadForeign _ _ pos) = pos
typeErrorPos (ReasonBadMove _ pos) = pos
typeErrorPos (ReasonResourceDef _ _ pos) = pos
typeErrorPos (ReasonResourceUndef _ _ pos) = pos
typeErrorPos (ReasonResourceUnavail _ _ pos) = pos
typeErrorPos (ReasonResourceOutOfScope _ _ pos) = pos
typeErrorPos (ReasonUseType _ pos) = pos
typeErrorPos (ReasonWrongFamily _ _ _ pos) = pos
typeErrorPos (ReasonIncompatible _ _ _ pos) = pos
typeErrorPos (ReasonWrongOutput _ _ _ pos) = pos
typeErrorPos (ReasonForeignArgRep _ _ _ _ pos) = pos
typeErrorPos (ReasonBadCast _ _ _ pos) = pos
typeErrorPos (ReasonBadConstraint _ _ _ _ _ pos) = pos
typeErrorPos ReasonShouldnt = Nothing
typeErrorPos (ReasonActuallyPure _ _ pos) = pos
typeErrorPos (ReasonUnnreachable _ pos) = pos


----------------------------------------------------------------
--                       The Typed Monad
----------------------------------------------------------------

-- |The Typed monad is a state transformer monad carrying the
--  typing state over the compiler monad.
type Typed = StateT Typing Compiler


-- | A variable type assignment (symbol table), with a list of type errors. Also
--   records bindings of type variables, and contains a counter for generating
--   new type variables.
data Typing = Typing {
                  typingDict::VarDict                -- ^variable types
                , tvarDict::Map TypeVarName TypeSpec -- ^type variable types
                , typeVarCounter::Int                -- ^for renumbering tvars
                , typingErrs::[TypeError]            -- ^type errors seen
                , tyTmpCtr::Int                      -- ^temp variable counter
                } deriving (Eq, Ord)


instance Show Typing where
  show (Typing dict tvardict _ errs _) =
    "Typing " ++ showVarMap dict ++ "; " ++ showVarMap (Map.mapKeys show tvardict)
    ++ if List.null errs
       then " (with no errors)"
       else " with errors: " ++ show errs


-- |Find the definition of the specified type visible from the current module.
-- TypeErrors are reported in the case the lookup reports an error
lookupTyped :: String -> OptPos -> TypeSpec -> Typed TypeSpec
lookupTyped context pos ty = do
    (msgs, ty') <- lift $ lookupType' context pos ty
    mapM_ (typeError . ReasonMessage) msgs
    ultimateType ty'


-- |Follow type variables to fully recursively resolve a type.
ultimateType  :: TypeSpec -> Typed TypeSpec
ultimateType ty@TypeVariable{typeVariableName=tvar} = do
    ty' <- gets $ Map.lookup tvar . tvarDict
    logTyped $ "Type variable " ++ show tvar ++ " is bound to " ++ show ty'
    maybe (return ty) ultimateType ty'
ultimateType (TypeSpec mod name args) =
    TypeSpec mod name <$> mapM ultimateType args
ultimateType ty@HigherOrderType{higherTypeParams=typeFlows} = do
    types <- mapM (ultimateType . typeFlowType) typeFlows
    return ty{higherTypeParams=zipWith TypeFlow types (typeFlowMode <$> typeFlows)}
ultimateType ty = return ty


-- |Bind all type variables in chain to specified type.  Make sure we don't bind
-- a type variable to itself.
bindTypeVariables :: TypeSpec -> TypeSpec -> Typed ()
bindTypeVariables ty1@TypeVariable{typeVariableName=var} ty2
 | ty1 /= ty2 = do
    nxt <- gets $ Map.lookup var . tvarDict
    modify $ \t -> t { tvarDict = Map.insert var ty2 $ tvarDict t }
    when (isJust nxt) $ bindTypeVariables (fromJust nxt) ty2
bindTypeVariables _ _ = return ()


-- |The empty typing, assigning every var the type AnyType.
initTyping :: Typing
initTyping = Typing Map.empty Map.empty 0 [] $ shouldnt "unititialised counter"


-- | Apply the monadic action with the given temp counter, returning the 
-- action's value and the new tempt counter
withCounter :: Int -> Typed m -> Typed (Int, m)
withCounter tmpCtr action = do
    oldTmpCtr <- gets tyTmpCtr
    modify $ \s -> s{tyTmpCtr=tmpCtr}
    m <- action
    tmpCtr' <- gets tyTmpCtr
    modify $ \s -> s{tyTmpCtr=oldTmpCtr}
    return (tmpCtr', m)


-- |Does the current typing have no errors?
validTyping :: Typed Bool
validTyping = gets $ List.null . typingErrs


-- |Get the ultimate type of variable.  If the type of the variable is
-- completely unknown, a type variable will be assigned, so this will never
-- return AnyType as a type.  It will also follow type variable bindings to get
-- the ultimate type of the variable.
ultimateVarType :: VarName -> Typed TypeSpec
ultimateVarType var = do
    ty <- varType var >>= ultimateType
    case ty of
        AnyType -> do
            ty' <- freshTypeVar
            setVarType var ty'
            return ty'
        _ -> return ty


-- |Get the type associated with a variable; AnyType if no constraint has
--  been imposed on that variable.  Does not follow type variable chains.
varType :: VarName -> Typed TypeSpec
varType var = gets $ Map.findWithDefault AnyType var . typingDict


-- |Set the type associated with a variable; does not check that the type is
-- consistent.
setVarType :: VarName -> TypeSpec -> Typed ()
setVarType var ty =
    modify (\t -> t { typingDict=Map.insert var ty $ typingDict t } )


-- |Constrain the type of the specified variable to be a subtype of the
--  specified type.  If this produces an invalid type, the specified type
--  error describes the error.
constrainVarType :: TypeError -> VarName -> TypeSpec -> Typed ()
constrainVarType reason var ty = do
    ty' <- varType var
    ty'' <- unifyTypes reason ty ty'
    logTyped $ "Variable " ++ var ++ " type constrained to " ++ show ty''
    setVarType var ty''


constrainType :: TypeError -> (TypeRepresentation -> Bool) -> TypeSpec -> Typed ()
constrainType reason constraint ty = do
    ty' <- lookupTyped "type constraint" (typeErrorPos reason) ty
    typeRep <- trustFromJust "constrainType"
           <$> lift (lookupTypeRepresentation ty')
    reportErrorUnless reason (constraint typeRep)


-- |Unify two types, returning a type that describes all instances of both input
-- types.  If this produces an invalid type, the specified type error describes
-- the error.  Unifying types may have the effect of binding variables.
unifyTypes :: TypeError -> TypeSpec -> TypeSpec -> Typed TypeSpec
unifyTypes reason t1 t2 = do
    let pos = typeErrorPos reason
    t1' <- lookupTyped "unification" pos t1
    t2' <- lookupTyped "unification" pos t2
    logTyped $ "Unifying types " ++ show t1 ++ " (-> " ++ show t1'
               ++ ") and " ++ show t2 ++ " (-> " ++ show t2' ++ ")"
    t <- unifyTypes' reason t1' t2'
    logTyped $ "  Unification yields " ++ show t
    bindTypeVariables t1 t
    bindTypeVariables t2 t
    return t


-- | Find the type that matches both specified type specs.  If there is no such
-- type, report the specified type error and return InvalidType.  If either or
-- both arguments are type variables, this need not bind them, as unifyTypes
-- will do that.
unifyTypes' :: TypeError -> TypeSpec -> TypeSpec -> Typed TypeSpec
unifyTypes' reason ty1 ty2
  | occursCheck ty1 ty2 = invalidTypeError reason
unifyTypes' reason InvalidType _ = return InvalidType
unifyTypes' reason _ InvalidType = return InvalidType
unifyTypes' reason AnyType ty    = return ty
unifyTypes' reason ty AnyType    = return ty
unifyTypes' reason ty1@(TypeVariable RealTypeVar{}) ty2@(TypeVariable RealTypeVar{})
    | ty1 == ty2 = return ty1
    | otherwise  = invalidTypeError reason
unifyTypes' reason ty1@TypeVariable{} ty2@TypeVariable{} = return $ min ty1 ty2
unifyTypes' reason (TypeVariable RealTypeVar{}) _  = invalidTypeError reason
unifyTypes' reason (TypeVariable FauxTypeVar{}) ty = return ty
unifyTypes' reason _  (TypeVariable RealTypeVar{}) = invalidTypeError reason
unifyTypes' reason ty (TypeVariable FauxTypeVar{}) = return ty
unifyTypes' reason ty1@Representation{} ty2@Representation{}
    | ty1 == ty2 = return ty1
    | otherwise  = invalidTypeError reason
unifyTypes' reason ty1@(Representation rep1) ty2@TypeSpec{} = do
    rep2 <- lift $ lookupTypeRepresentation ty2
    if Just rep1 == rep2
    then return ty2
    else invalidTypeError reason
unifyTypes' reason ty1@TypeSpec{} ty2@(Representation rep2) = do
    rep1 <- lift $ lookupTypeRepresentation ty1
    if rep1 == Just rep2
    then return ty1
    else invalidTypeError reason
unifyTypes' reason ty1@(TypeSpec m1 n1 ps1) ty2@(TypeSpec m2 n2 ps2)
    | n1 == n2 && modsMatch && sameLength ps1 ps2 =
        TypeSpec m n1 <$> zipWithM (unifyTypes reason) ps1 ps2
    | otherwise = invalidTypeError reason
  where (modsMatch, m)
          | m1 `isSuffixOf` m2 = (True,  m2)
          | m2 `isSuffixOf` m1 = (True,  m1)
          | otherwise          = (False, [])
unifyTypes' reason (HigherOrderType mods1 ps1) (HigherOrderType mods2 ps2)
    | sameLength ps1Tys ps2Tys
            && mods1' == mods2'
            && and (zipWith (==) ps1Fls ps2Fls) = do
        logTyped $ "Unifying higher types " ++ show ps1Tys ++ "; " ++ show ps2Tys
        HigherOrderType mods1' . zipWith (flip TypeFlow) ps1Fls <$>
            zipWithM (unifyTypes reason) ps1Tys ps2Tys
    | otherwise =
        typeError reason >> return InvalidType
    where
        (mods1', (ps1Tys, ps1Fls)) = typeFlowsToSemiDet mods1 ps1 ps2
        (mods2', (ps2Tys, ps2Fls)) = typeFlowsToSemiDet mods2 ps2 ps1
unifyTypes' reason _ _ = typeError reason >> return InvalidType

invalidTypeError :: TypeError -> Typed TypeSpec
invalidTypeError reason = typeError reason >> return InvalidType


-- | Checks if two types' are cyclic.
-- That is if one type variable is contained in the other
occursCheck :: TypeSpec -> TypeSpec -> Bool
occursCheck TypeVariable{} TypeVariable{} = False
occursCheck ty1@TypeVariable{typeVariableName=nm} ty2
  = containsTypeVar nm ty2
occursCheck ty1 ty2@TypeVariable{typeVariableName=nm}
  = containsTypeVar nm ty1
occursCheck _ _ = False


-- | Checks if the given TypeVarName is contained within the TypeSpec.
-- Does not hold for a TypeVariable
containsTypeVar :: TypeVarName -> TypeSpec -> Bool
containsTypeVar nm TypeVariable{typeVariableName=nm'} = nm == nm'
containsTypeVar nm TypeSpec{typeParams=tys} = any (containsTypeVar nm) tys
containsTypeVar nm HigherOrderType{higherTypeParams=params}
  = any (containsTypeVar nm . typeFlowType) params
containsTypeVar _ _ = False


-- |Generate a unique fresh type variable.
freshTypeVar :: Typed TypeSpec
freshTypeVar = do
    next <- gets typeVarCounter
    modify $ \st -> st { typeVarCounter = next+1 }
    return $ TypeVariable $ FauxTypeVar next


-- |Record a type error in the current typing.
typeError :: TypeError -> Typed ()
typeError = typeErrors . (:[])


-- |Record a list of type errors in the current typing.
typeErrors :: [TypeError] -> Typed ()
typeErrors errs = do
    unless (List.null errs) $ logTyped $ "Recording error(s): " ++ show errs
    modify $ \t -> t { typingErrs=errs ++ typingErrs t }


localBodyProcs :: ProcImpln -> Set RoughProcSpec
localBodyProcs (ProcDefSrc body) =
    foldStmts localCalls (const . const) Set.empty body
localBodyProcs ProcDefPrim{} =
    shouldnt "Type checking compiled code"

localCalls :: Set RoughProcSpec -> Stmt -> OptPos -> Set RoughProcSpec
localCalls idents (ProcCall (First m name _) _ _ _) _
  = Set.insert (RoughProc m name) idents
localCalls idents _ _ = idents


-- |Return the ultimate type of an expression.
expType :: Placed Exp -> Typed TypeSpec
expType expr = do
    logTyped $ "Finding type of expr " ++ show expr
    ty <- placedApply expType' expr
    logTyped $ "  Type = " ++ show ty
    return ty


expType' :: Exp -> OptPos -> Typed TypeSpec
expType' (IntValue _) _               = return $ TypeSpec ["wybe"] "int" []
expType' (FloatValue _) _             = return $ TypeSpec ["wybe"] "float" []
expType' (StringValue _ WybeString) _ = return $ TypeSpec ["wybe"] "string" []
expType' (StringValue _ CString) _    = return $ TypeSpec ["wybe"] "c_string" []
expType' (CharValue _) _              = return $ TypeSpec ["wybe"] "char" []
expType' (AnonProc mods params pstmts _ _) _ = do
    mapM_ ultimateVarType $ paramName <$> params
    params' <- updateParamTypes $ Unplaced <$> params
    return $ HigherOrderType mods $ paramTypeFlow . content <$> params'
expType' (Closure pspec closed) _ = do
    ProcDef _ (ProcProto _ params res) _ _ _ _ _ _ detism _ impurity _ _
        <- lift $ getProcDef pspec
    let params' = List.filter ((==Ordinary) . paramFlowType . content) params
    let typeFlows = paramTypeFlow . content <$> params'
    let pTypes = typeFlowType <$> typeFlows
    let pFlows = typeFlowMode <$> typeFlows
    let nClosed = length closed
    let (closedFlows, freeFlows) = List.splitAt nClosed pFlows
    if nClosed <= length params' && replicate nClosed ParamIn == closedFlows
    then do
        pTypes' <- refreshTypes pTypes
        closedTypes <- mapM expType closed
        zipWithM_ (unifyTypes ReasonShouldnt) pTypes' closedTypes
        freeTypes <- mapM ultimateType (List.drop nClosed pTypes')
        let resful = not $ Set.null res
        return $ HigherOrderType
                    (normaliseModifiers
                        $ ProcModifiers detism MayInline
                            impurity RegularProc resful)
                    $ zipWith TypeFlow freeTypes freeFlows
    else do
        typeError ReasonShouldnt
        return InvalidType
expType' (Var name _ _) _             = ultimateVarType name
expType' (Typed _ typ _) pos          =
    lookupTyped "typed expression" pos typ
expType' expr _ =
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
expMode' _ (StringValue _ _) = (ParamIn, True, Nothing)
expMode' _ (CharValue _) = (ParamIn, True, Nothing)
expMode' _ (Closure _ _) = (ParamIn, True, Nothing)
expMode' _ AnonProc{} = (ParamIn, True, Nothing)
expMode' assigned (Var name flow _) =
    (flow, name `assignedIn` assigned, Nothing)
expMode' assigned (Typed expr _ _) = expMode' assigned expr
expMode' _ expr =
    shouldnt $ "Expression '" ++ show expr ++ "' left after flattening"


-- | Transform gievn ProcModifiers and TypeFlows to SemiDet, transforming a
-- Det modified list of TypeFlows ending in an out flowing boolean typed into
-- SemiDet
typeFlowsToSemiDet :: ProcModifiers -> [TypeFlow] -> [TypeFlow]
                   -> (ProcModifiers, ([TypeSpec], [FlowDirection]))
typeFlowsToSemiDet mods@ProcModifiers{modifierDetism=Det} tfs@(_:_) others
    | test == TypeFlow boolType ParamOut
      && sameLength others semiTFs = (normaliseModifiers mods{modifierDetism=SemiDet},
                                      unzipTypeFlows semiTFs)
  where
    semiTFs = init tfs
    test = last tfs
typeFlowsToSemiDet mods tfs _ = (normaliseModifiers mods, unzipTypeFlows tfs)

normaliseModifiers :: ProcModifiers -> ProcModifiers
normaliseModifiers mods@ProcModifiers{modifierImpurity=imp}
    = mods{modifierInline=MayInline,
           modifierImpurity=max imp Pure,
           modifierVariant=RegularProc}

----------------------------------------------------------------
--                         Type Checking Procs
----------------------------------------------------------------

-- |Type check one strongly connected component in the call graph.  Returns True
--  if the inferred types are more specific than the old ones.  In this case, we
--  will have to rerun the typecheck after typechecking the other modules on
--  that list.
typecheckProcSCC :: SCC RoughProcSpec -> Compiler [TypeError]
typecheckProcSCC (AcyclicSCC proc) = do
    -- A single pass is always enough for non-cyclic SCCs
    logTypes $ "Type checking non-recursive proc " ++ show proc
    (_,reasons) <- typecheckProcDecl proc
    return reasons
typecheckProcSCC (CyclicSCC list) = do
    logTypes $ "**** Type checking recursive procs " ++
      intercalate ", " (List.map show list)
    (sccAgain,reasons) <-
        foldM (\(sccAgain,rs) proc -> do
                    (sccAgain',reasons) <- typecheckProcDecl proc
                    return (sccAgain || sccAgain', reasons++rs))
        (False, []) list
    if sccAgain
    then typecheckProcSCC $ CyclicSCC list
    else do
      logTypes $ "**** Completed checking of " ++
             intercalate ", " (show <$> list) ++
             " with " ++ show (length reasons) ++ " errors"
      return reasons


-- |Type check a list of procedure definitions and update the definitions stored
--  in the Compiler monad.  Returns a pair of a Bool saying whether any
--  defnition has been udpated, and a list of the type errors detected.
typecheckProcDecl :: RoughProcSpec -> Compiler (Bool,[TypeError])
typecheckProcDecl (RoughProc m name) = do
    logTypes $ "** Type checking decl of proc " ++ name
    reenterModule m
    defs <- getModuleImplementationField
            (Map.findWithDefault (error "missing proc definition")
             name . modProcs)
    logTypes $ "found " ++ (show . length) defs ++ " definition(s)"
    (revdefs,sccAgain,reasons) <-
        foldM (\(ds,sccAgain,rs) def -> do
                ((d,again),st) <- runStateT (typecheckProcDecl' m def) initTyping
                return (d:ds, sccAgain || again, typingErrs st++rs))
        ([],False,[]) defs
    updateModImplementation
      (\imp -> imp { modProcs = Map.insert name (reverse revdefs)
                                $ modProcs imp })
    logTypes $ "** New definition of " ++ name ++ ":"
    logTypes $ intercalate "\n" $ List.map (showProcDef 4) (reverse revdefs)
    -- XXX this shouldn't be necessary anymore, but keep it for now for safety
    unless (sccAgain || not (List.null reasons)) $
        mapM_ checkProcDefFullytyped revdefs
    reexitModule
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


-- |An individual call, and information that is related to this call
data CallInfo
    = FirstInfo {
        fiProc         :: ProcSpec
      , fiTypes        :: [TypeSpec]
      , fiFlows        :: [FlowDirection]
      , fiDetism       :: Determinism
      , fiImpurity     :: Impurity
      , fiInRes        :: Set ResourceSpec
      , fiOutRes       :: Set ResourceSpec
      , fiNeedsResBang :: Bool
      , fiPartial      :: Bool
    } | HigherInfo {
        hiFunc :: Exp
    } | TestInfo {
        tiVar :: Exp
    }
   deriving (Eq, Ord)


instance Show CallInfo where
    show (FirstInfo procSpec tys flows detism impurity inRes outRes _ partial) =
        (if partial then "partial application of " else "")
        ++ showProcModifiers' (ProcModifiers detism MayInline impurity
                                RegularProc False)
        ++ show procSpec
        ++ "(" ++ intercalate "," (zipWith ((show .) . TypeFlow) tys flows) ++ ")"
        ++ if Set.null inRes && Set.null outRes
            then ""
            else " use "
                 ++ intercalate ", "
                    ((resourceName <$> Set.toList inRes)
                     ++ (('?':) . resourceName <$> Set.toList outRes))
    show (HigherInfo fn) = "higher " ++ show fn
    show (TestInfo exp) = "test " ++ show exp


callInfoTypes :: CallInfo -> Maybe [TypeSpec]
callInfoTypes FirstInfo{fiTypes=tys} = Just tys
callInfoTypes HigherInfo{} = Nothing
callInfoTypes TestInfo{} = Nothing


-- |Check if a FirstInfo is for a proc with a single Bool output as last arg,
--  and if so, return Just the FirstInfo for the equivalent test proc
-- Higher order reification of bool fns to tests is handled in `matchTypes'
boolFnToTest :: CallInfo -> Maybe CallInfo
boolFnToTest info@FirstInfo{fiDetism=Det,
                            fiPartial=False,
                            fiTypes=tys,
                            fiFlows=flows}
    | List.null tys = Nothing
    | last tys == boolType && last flows == ParamOut =
        Just $ info {fiDetism=SemiDet,
                     fiTypes=init tys,
                     fiFlows=init flows}
    | otherwise = Nothing
boolFnToTest _ = Nothing


-- |Check if ProcInfo is for a test proc, and if so, return a ProcInfo for
--  the Det proc with a single Bool output as last arg
-- Higher order reification of tests bool fns is handled in `matchTypes'
testToBoolFn :: CallInfo -> Maybe CallInfo
testToBoolFn info@FirstInfo{fiDetism=SemiDet,
                            fiPartial=False,
                            fiTypes=tys,
                            fiFlows=flows}
    = Just $ info {fiDetism=Det,
                   fiTypes=tys ++ [boolType],
                   fiFlows=flows ++ [ParamOut]}
testToBoolFn _ = Nothing


-- |Check if ProcInfo can be transformed into a partial application, given a
-- list of FlowDirections. This returns Just if the final FlowDirection is ParamOut
-- if the call has an arity lower than expected or, in the case of a resourceful
-- call where the call does not have a ! prefix, at most 1 more than the expected
-- arity. The Bool returned indicates if the call should have a ! or not
procToPartial :: [FlowDirection] -> Bool -> CallInfo -> (Maybe CallInfo, Bool)
procToPartial callFlows hasBang info@FirstInfo{fiPartial=False,
                                               fiTypes=tys,
                                               fiFlows=flows,
                                               fiInRes=inRes,
                                               fiOutRes=outRes,
                                               fiNeedsResBang=resful,
                                               fiDetism=detism,
                                               fiImpurity=impurity}
    | not hasBang && not (List.null callFlows) && last callFlows == ParamOut
                  && (length callFlows < length tys
                      || length callFlows <= length tys + 1 && usesResources)
        = (Just info{fiPartial=True,
                     fiTypes=closedTys ++ [higherTy],
                     fiFlows=closedFls ++ [ParamOut]}, needsBang)
  where
    nClosed = length callFlows - 1
    (closedTys, higherTys) = List.splitAt nClosed tys
    (closedFls, higherFls) = List.splitAt nClosed flows
    usesResources = not (Set.null inRes) || not (Set.null outRes)
    needsBang = resful || impurity > Pure
    higherTy = HigherOrderType (normaliseModifiers
                                $ ProcModifiers detism MayInline
                                    impurity RegularProc resful)
                    $ zipWith TypeFlow higherTys higherFls
procToPartial _ _ _ = (Nothing, False)


-- |A single call statement together with the determinism context in which
--  the call appears and a list of all the possible different parameter
--  list types (a list of types). This type is used to narrow down the
--  possible call typings.
data StmtTypings
    = StmtTypings {
            typingStmt::Placed Stmt,
            typingInfos::[CallInfo]
        }
    deriving (Eq,Show)


-- |Type check a single procedure definition, including resolving overloaded
-- calls, handling implied modes, and appropriately ordering calls from
-- nested function application.  We search for a valid resolution
-- deterministically if possible.
typecheckProcDecl' :: ModSpec -> ProcDef -> Typed (ProcDef,Bool)
typecheckProcDecl' m pdef = do
    let name = procName pdef
    logTyped $ "Type checking " ++ showProcName name
    let proto = procProto pdef
    let posParams = procProtoParams proto
    let params = content <$> posParams
    let resources = procProtoResources proto
    let tmpCount = procTmpCount pdef
    let (ProcDefSrc def) = procImpln pdef
    let detism = procDetism pdef
    let pos = procPos pdef
    let vis = procVis pdef
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
    let inputs = Set.union inParams inResources
    when (vis == Public && any ((==AnyType) . paramType) params)
        $ typeError $ ReasonUndeclared name pos
    ifOK pdef $ do
        logTyping $ "** Type checking " ++ showProcName name ++ ": "
        logTyped $ "   with resources: " ++ show resources
        calls <- bodyCallsConstraints False def
        logTyped $ "   containing calls: " ++ showBody 8 calls
        -- logTyped $ "   inner resources: " ++ show (fst <$> bodyRes)
        let assignedVars =
                foldStmts
                    (const . const)
                    (\outs exp _ ->
                        outs `Set.union` (expOutputs exp `Set.difference` expInputs exp))
                    inputs def
        logTyped $ "   with assigned vars: " ++ show assignedVars
        logTyped $ "Recording parameter types: "
                   ++ intercalate ", " (show <$> params)
        mapM_ (addDeclaredType name pos (length params)) $ zip params [1..]
        logTyped $ "Recording resource types: "
                   ++ intercalate ", " (show <$> Set.toList resources)
        mapM_ (uncurry $ addResourceType (ReasonResourceDef name))
            $ (, pos) . resourceFlowRes <$> Set.toList resources
        ifOK pdef $ do
            mapM_ (placedApply (recordCasts name)) calls
            logTyping "*** Before calls "
            let procCalls = List.filter (isRealProcCall . content) calls
            -- let unifs = List.concatMap foreignTypeEquivs
            --             (content . fst <$> calls)
            -- mapM_ (uncurry $ unifyExprTypes pos) unifs
            calls' <- mapM (callInfos assignedVars) procCalls
            logTyping $ "  With calls:\n  " ++ intercalate "\n    " (show <$> calls')
            let badCalls = List.map typingStmt
                         $ List.filter (List.null . typingInfos) calls'
            mapM_ (\pcall -> case content pcall of
                    ProcCall (First _ callee _) _ _ _ ->
                        typeError $ ReasonUndef name callee $ place pcall
                    _ -> shouldnt "typecheckProcDecl'"
                  ) badCalls
            ifOK pdef $ do
                typecheckCalls m name pos calls' [] False
                    $ List.filter (isForeign . content) calls
                ifOK pdef $ do
                    logTyped $ "Now mode checking proc " ++ name
                    let bound = addBindings inputs
                                $ initBindingState pdef
                                  $ Set.map resourceFlowRes resources
                    logTyped $ "bound vars: " ++ show bound
                    (tmpCount', (def',assigned) )
                        <- withCounter tmpCount
                            $ modecheckStmts m name pos bound detism True def
                    logTyped $ "Mode checked body   : " ++ show def'
                    logTyped $ "Vars defined by body: " ++ show assigned
                    logTyped $ "Output parameters   : "
                               ++ intercalate ", " (Set.toList outParams)
                    logTyped $ "Output resources    : "
                               ++ intercalate ", " (Set.toList outResources)
                    let modeErrs =
                          [ReasonResourceUndef name res pos
                          | res <- Set.toList
                                   $ missingBindings outResources assigned]
                          ++
                          [ReasonOutputUndef name param pos
                          | param <- Set.toList
                                     $ missingBindings outParams assigned]
                    typeErrors modeErrs
                    params' <- updateParamTypes posParams
                    let proto' = proto { procProtoParams = params' }
                    let pdef' = pdef { procProto = proto',
                                       procTmpCount = tmpCount',
                                       procImpln = ProcDefSrc def' }
                    sccAgain <- (&& params' /= posParams) <$> validTyping
                    logTyped $ "===== "
                               ++ (if sccAgain then "" else "NO ")
                               ++ "Need to check again."
                    when sccAgain
                        (logTyped $ "\n-----------------OLD:"
                                    ++ showProcDef 4 pdef
                                    ++ "\n-----------------NEW:"
                                    ++ showProcDef 4 pdef' ++ "\n")
                    return (pdef',sccAgain)


-- | If no type errors have been recorded, execute the enclosed code; otherwise
-- just return the specified proc definition.  This is probably only useful in
-- defining typecheckProcDecl'.

ifOK :: ProcDef -> Typed (ProcDef,Bool) -> Typed (ProcDef,Bool)
ifOK pdef body = do
    allGood <- validTyping
    if allGood then body else return (pdef,False)

-- | Get the TypingState of a given action, along with the result.
-- Does not modify the underlying Typing state
getTyping :: Typed a -> Typed (a, Typing)
getTyping action = do
    typing0 <- get
    result <- action
    typing <- get
    put typing0
    return (result, typing)


addDeclaredType :: ProcName -> OptPos -> Int -> (Param,Int) -> Typed ()
addDeclaredType procname pos arity (Param name typ flow _,argNum) = do
    typ' <- lookupTyped "proc declaration" pos typ
    logTyped $ "    type of '" ++ name ++ "' is " ++ show typ'
    constrainVarType (ReasonParam procname arity pos) name typ'


-- | Record the types of available resources as local variables
addResourceType :: (ResourceSpec -> OptPos -> TypeError)
                -> ResourceSpec -> OptPos  -> Typed ()
addResourceType errFn rspec pos = do
    resDef <- lift $ lookupResource rspec
    let (rspecs,implns) = unzip $ maybe [] Map.toList resDef
    zipWithM_ (liftM2 constrainVarType (`errFn` pos) resourceName)
          rspecs (resourceType <$> implns)



-- | Register variable types coming from explicit type constraints and type
-- casts.  Casts are only permitted on foreign call arguments, and only specify
-- the type of the receiving variable, while type constraints can appear
-- anywhere and constrain the type of both the source and destination
-- expressions.
recordCasts :: ProcName -> Stmt -> OptPos -> Typed ()
recordCasts caller instr@(ForeignCall "llvm" "move" _ [v1,v2]) pos = do
    logTyped $ "Recording casts in " ++ show instr
    recordCast (Just "llvm") caller "move" v1 1
    recordCast (Just "llvm") caller "move" v2 2
    logTyped $ "Unifying move argument types " ++ show v1 ++ " and " ++ show v2
    t1 <- expType v1
    t2 <- expType v2
    void $ unifyTypes (ReasonEqual (content v1) (content v2) pos)
           t1 t2
recordCasts caller instr@(ForeignCall lang callee _ args) pos = do
    logTyped $ "Recording casts in " ++ show instr
    mapM_ (uncurry $ recordCast (Just lang) caller callee) $ zip args [1..]
recordCasts caller instr@(ProcCall (First _ callee _) _ _ args) pos = do
    logTyped $ "Recording casts in " ++ show instr
    mapM_ (uncurry $ recordCast Nothing caller callee) $ zip args [1..]
recordCasts caller instr@(ProcCall (Higher fn) _ _ args) _ = do
    logTyped $ "Recording casts in " ++ show instr
    mapM_ (uncurry $ recordCast Nothing caller $ show $ content fn) $ zip (fn:args) [0..]
recordCasts caller stmt _ =
    shouldnt $ "recordCasts of non-call statement " ++ show stmt


-- | Record the constraints on the contents of a single type constraint or type
-- cast.  Note that the Typed wrapper gives the type of the expression itself,
-- so this only needs to record the type of the variable inside the Typed
-- constructor.
recordCast :: Maybe Ident -> ProcName -> Ident -> Placed Exp -> Int -> Typed ()
recordCast mbLang caller callee pexp argNum =
    case content pexp of
        (Typed _ _ (Just _)) | isNothing mbLang
            -> typeError $ ReasonBadCast caller callee argNum pos
        (Typed exp ty Nothing)
            -> recordCast' mbLang caller callee argNum ty exp pos
        (Typed exp _ (Just ty))
            -> recordCast' mbLang caller callee argNum ty exp pos
        _   -> return ()
    where pos = place pexp

recordCast' :: Maybe Ident -> ProcName -> Ident -> Int -> TypeSpec -> Exp -> OptPos -> Typed ()
recordCast' _ caller callee argNum ty (Var name _ _) pos
    = constrainVarType (ReasonArgType False callee argNum pos) name ty
-- ignore all non-variable casts in foreigns, except for llvm moves
recordCast' (Just lang) _ callee _ _ _ _
    | not (lang == "llvm" && callee == "move") = return ()
recordCast' _ caller callee argNum ty exp@(IntValue _) pos
    = constrainType (ReasonBadConstraint caller callee argNum exp ty pos)
         integerTypeRep ty
recordCast' _ caller callee argNum ty exp@(CharValue _) pos
    = constrainType (ReasonBadConstraint caller callee argNum exp ty pos)
         integerTypeRep ty
recordCast' _ caller callee argNum ty exp@(FloatValue _) pos
    = constrainType (ReasonBadConstraint caller callee argNum exp ty pos)
        ((==FloatFamily) . typeFamily) ty
recordCast' _ caller callee argNum ty exp pos = do
    ty' <- expType (exp `maybePlace` pos)
    void $ unifyTypes (ReasonBadConstraint caller callee argNum exp ty pos) ty' ty


updateParamTypes :: [Placed Param] -> Typed [Placed Param]
updateParamTypes =
    mapM $ updatePlacedM (\p -> do
                            ty <- ultimateVarType (paramName p)
                            return p{paramType=ty})


-- |Return a list of the proc and foreign calls recursively in a list of
-- statements, along with the resources that occur in `use` blocks.
bodyCallsConstraints :: Bool -> [Placed Stmt] -> Typed [Placed Stmt]
bodyCallsConstraints nested stmts =
    concat <$> mapM (bodyCallsConstraints' nested) stmts

bodyCallsConstraints' :: Bool -> Placed Stmt -> Typed [Placed Stmt]
bodyCallsConstraints' nested pstmt = do
    calls <- bodyCalls'' nested (content pstmt) (place pstmt)
    if nested
    then return calls
    else do
        let expCalls = foldStmts (const . const) expStmts [] [pstmt]
        expCalls' <- mapM (bodyCallsConstraints True) expCalls
        return $ calls ++ concat expCalls'

bodyCalls'' :: Bool -> Stmt -> OptPos -> Typed [Placed Stmt]
bodyCalls'' _ stmt@ProcCall{} pos = return [stmt `maybePlace` pos]
bodyCalls'' _ stmt@ForeignCall{} pos = return [stmt `maybePlace` pos]
bodyCalls'' nested (And stmts) _ = bodyCallsConstraints nested stmts
bodyCalls'' nested (Or stmts _ _) _ = bodyCallsConstraints nested stmts
bodyCalls'' nested (Not stmt) _ = bodyCallsConstraints nested [stmt]
bodyCalls'' nested (Cond cond thn els _ _ _) _ = do
    cond' <- bodyCallsConstraints nested [cond]
    thn' <- bodyCallsConstraints nested thn
    els' <- bodyCallsConstraints nested els
    return $ cond' ++ thn' ++ els'
bodyCalls'' nested (Loop stmts _ _) _ = bodyCallsConstraints nested stmts
bodyCalls'' nested (UseResources res _ stmts) pos = do
    mapM_ (flip (addResourceType ReasonUseType) pos) res
    bodyCallsConstraints nested stmts
bodyCalls'' _ For{} _ = shouldnt "bodyCalls: flattening left For stmt"
bodyCalls'' _ Case{} _ = shouldnt "bodyCalls: flattening left Case stmt"
bodyCalls'' _ (TestBool exp) pos = do
    ty <- expType $ exp `maybePlace` pos
    unifyTypes (ReasonExpType exp boolType pos) ty boolType
    return []
bodyCalls'' _ Nop _ = return []
bodyCalls'' _ Fail _ = return []
bodyCalls'' _ Break _ = return []
bodyCalls'' _ Next _ = return []


expStmts :: [[Placed Stmt]] -> Exp -> OptPos -> [[Placed Stmt]]
expStmts ss (AnonProc _ _ ls _ _) _ = ls:ss
expStmts ss _ _ = ss


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


-- |Get matching CallInfos for the supplied statement (which must be a call)
callInfos :: Set VarName -> Placed Stmt -> Typed StmtTypings
callInfos vars pstmt = do
    let stmt = content pstmt
    case stmt of
        ProcCall (First m name procId) d resful args -> do
            varTy <- varType name >>= ultimateType
            let couldBeVar = List.null m && isNothing procId
                           && name `Set.member` vars
                couldBeHigher = isHigherOrder varTy || varTy == AnyType
                couldBeTest   = (boolType == varTy || varTy == AnyType)
                             && List.null args && not resful
            if couldBeVar && (couldBeHigher || couldBeTest)
            then let var = varGet name 
                 in return $ StmtTypings pstmt $ [HigherInfo var | couldBeHigher]
                                              ++ [TestInfo var | couldBeTest]
            else do
                procs <- case procId of
                    Nothing  -> lift $ callTargets m name
                    Just pid -> return [ProcSpec m name pid generalVersion]
                defs <- lift $ mapM getProcDef procs
                firstInfos <- zipWithM firstInfo defs procs
                return $ StmtTypings pstmt firstInfos
        ProcCall (Higher fn) _ _ _ -> 
            return $ StmtTypings pstmt [HigherInfo $ content fn]
        _ ->
          shouldnt $ "callProcInfos with non-call statement "
                     ++ showStmt 4 stmt

firstInfo :: ProcDef -> ProcSpec -> Typed CallInfo
firstInfo def proc = do
    let proto = procProto def
        params = content <$> procProtoParams proto
        resources = Set.elems $ procProtoResources proto
        realParams = List.filter ((==Ordinary) . paramFlowType) params
        typeFlows = paramTypeFlow <$> realParams
        types = typeFlowType <$> typeFlows
        flows = typeFlowMode <$> typeFlows
        inResources = Set.fromList
                        $ resourceFlowRes <$>
                            List.filter (flowsIn . resourceFlowFlow) resources
        outResources = Set.fromList
                        $ resourceFlowRes <$>
                            List.filter (flowsOut . resourceFlowFlow) resources
        needsResBang = not (List.null resources) || any isResourcefulHigherOrder types
        detism = procDetism def
        imp = procImpurity def
    types' <- refreshTypes types
    return $ FirstInfo proc types' flows detism imp inResources outResources needsResBang False


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
               -> [StmtTypings] -> Bool -> [Placed Stmt] -> Typed ()
typecheckCalls m name pos [] [] _ foreigns =
    mapM_ (placedApply validateForeign) foreigns
typecheckCalls m name pos [] residue True foreigns =
    typecheckCalls m name pos residue [] False foreigns
typecheckCalls m name pos [] residue False foreigns = do
    let (typings@StmtTypings{typingInfos=infos},rest) = findMinimumTyping residue
    logTyped $ "Recursively checking types with " ++ show typings
    typings' <- mapM (getTyping . typecheckCallWithInfo m name pos typings rest foreigns) infos
    case List.filter (List.null . typingErrs) $ snd <$> typings' of
        [typing] -> put typing
        _ -> do
            typeErrors $ overloadErr <$> residue
            typecheckCalls m name pos [] [] False foreigns
typecheckCalls m name pos (stmtTyping@(StmtTypings pstmt typs):calls)
        residue chg foreigns = do
    logTyped $ "Type checking call " ++ show pstmt
    logTyped $ "Candidate types:\n    " ++ intercalate "\n    " (show <$> typs)
    let (stmt, stmtPos) = unPlace pstmt
    let (mod, callee, pexps, resful)
            = case stmt of
                ProcCall (First mod callee _) _ resful pexps ->
                    (mod, callee, pexps, resful)
                ProcCall (Higher fn) _ resful pexps ->
                    ([], show $ content fn, pexps, resful)
                noncall -> shouldnt $ "typecheckCalls with non-call stmt"
                                        ++ show noncall
    actualTypes <- mapM expType pexps
    let actualModes = flattenedExpFlow . content <$> pexps
    logTyped $ "Actual types: " ++ show actualTypes
    matches <- mapM
               (matchTypes name callee stmtPos resful actualTypes actualModes)
               typs
    let canonMatches = ap (,) (fmap (canonicalise 0) . callInfoTypes . fst)
                    <$> catOKs matches
    let validTypes = fst <$> nubBy ((==) `on` snd) canonMatches
    logTyped $ "Valid types = " ++ show (snd <$> validTypes)
    let matchErrs = concatMap errList matches
    case validTypes of
        [] -> case (mod, callee, content <$> pexps, actualTypes) of
            -- special case for assigment
            ([], "=", [arg1, arg2], [ty1, ty2]) -> do
                logTyped "Trying to check = call as assignment"
                void $ unifyTypes (ReasonEqual arg1 arg2 stmtPos) ty1 ty2
                ifM validTyping
                    (typecheckCalls m name pos calls residue True foreigns)
                    (typeErrors matchErrs)
            _ -> do
                nameTy <- varType callee
                case (mod, pexps) of
                    -- special case for bool test
                    ([], []) | not resful && (nameTy == boolType || nameTy == AnyType) -> do
                        constrainVarType
                            (ReasonExpType (Var callee ParamIn Ordinary) boolType stmtPos)
                            callee boolType
                        typecheckCalls m name pos calls residue True foreigns
                    _ -> do
                        logTyped "Type error: no valid types for call"
                        typeErrors matchErrs
        [(_,typing)] -> do
            put typing
            logTyping "Resulting typing = "
            typecheckCalls m name pos calls residue True foreigns
        _ -> do
            let matchProcInfos = fst <$> validTypes
            let stmtTyping' = stmtTyping {typingInfos = matchProcInfos}
            typecheckCalls m name pos calls (stmtTyping':residue)
                (chg || matchProcInfos /= typs) foreigns


-- | Find the StmtTypings with the least number of possibile typingInfos,
-- returning the "minimum" StmtTyping and all others
findMinimumTyping :: [StmtTypings] -> (StmtTypings, [StmtTypings])
findMinimumTyping [] = shouldnt "findMinimumTyping"
findMinimumTyping (typing:typings) = findMinimumTyping' typings typing []


findMinimumTyping' :: [StmtTypings] -> StmtTypings -> [StmtTypings]
                   -> (StmtTypings, [StmtTypings])
findMinimumTyping' [] typing' acc = (typing', acc)
findMinimumTyping' (typing:rest) typing' acc
    | length (typingInfos typing) < length (typingInfos typing')
    = findMinimumTyping' rest typing (typing':acc)
    | otherwise
    = findMinimumTyping' rest typing' (typing:acc)


-- | Perform type checks replacing the typingInfos of the supplied StmtTypings
-- with the supplied Info
typecheckCallWithInfo :: ModSpec -> ProcName -> OptPos -> StmtTypings
                      -> [StmtTypings] -> [Placed Stmt] -> CallInfo -> Typed ()
typecheckCallWithInfo m name pos typings rest fs info = do
    typecheckCalls m name pos (typings{typingInfos=[info]}:rest) [] False fs


-- |Match up the argument types of a call with the parameter types of the
-- callee, producing a list of the actual types.  If this list contains
-- InvalidType, then the call would be a type error.
matchTypes :: Ident -> Ident -> OptPos -> Bool -> [TypeSpec] -> [FlowDirection]
           -> CallInfo -> Typed (MaybeErr (CallInfo,Typing))
matchTypes caller callee pos hasBang callTypes callFlows
        calleeInfo@FirstInfo{fiTypes=tys}
    -- Handle case whre call should have a ! but doesnt, and the call
    -- can be made partial
    | not hasBang && needsBang && isJust partialCallInfo
    = matchTypeList callee pos callTypes calleeInfo'''
    -- Handle case where call arity is correct
    | sameLength callTypes tys
    = matchTypeList callee pos callTypes calleeInfo
    -- Handle case of SemiDet context call to bool function as a proc call
    | isJust testInfo && sameLength callTypes (fiTypes calleeInfo')
    = matchTypeList callee pos callTypes calleeInfo'
    -- Handle case of reified test call
    | isJust detCallInfo && sameLength callTypes (fiTypes calleeInfo'')
    = matchTypeList callee pos callTypes calleeInfo''
    -- Handle case where the call is partial
    | isJust partialCallInfo
    = matchTypeList callee pos callTypes calleeInfo'''
    -- Else, we must have an arity error
    | otherwise = return $ Err [ReasonArity caller callee pos
                                (length callTypes) (length tys)]
    where testInfo = boolFnToTest calleeInfo
          calleeInfo' = fromJust testInfo
          detCallInfo = testToBoolFn calleeInfo
          calleeInfo'' = fromJust detCallInfo
          (partialCallInfo, needsBang) = procToPartial callFlows hasBang calleeInfo
          calleeInfo''' = fromJust partialCallInfo
matchTypes caller callee pos _ callTypes callFlows
        calleeInfo@(HigherInfo fn) = do
    let callTFs = zipWith TypeFlow callTypes callFlows
    fnTy <- expType (Unplaced fn) >>= ultimateType
    logTyped $ "Checking higher call " ++ show fn ++ ":" ++ show fnTy
            ++ " with type " ++ show callTFs
    typing <-
        getTyping $ case fnTy of
            HigherOrderType mods tfs -> 
                -- This handles the reification of higher order tests <-> bool fns
                -- For first order cases, see `boolFnToTest' and `testToBoolFn'
                let nCallTFs = length callTFs
                    nTFs = length tfs
                    tfs' | nCallTFs == nTFs - 1
                           && last tfs == TypeFlow boolType ParamOut
                           && modifierDetism mods == Det -- reified tesst
                         = init tfs
                         | nCallTFs == nTFs + 1
                           && last callTFs == TypeFlow boolType ParamOut
                           && modifierDetism mods == SemiDet -- de-reified test
                         = tfs ++ [last callTFs]
                         | otherwise = tfs
                in if nCallTFs == length tfs'
                then do
                    unifyTypeList' callee pos callTypes (typeFlowType <$> tfs')
                    zipWith3M_ (\f1 f2 i -> 
                        unless (f1 == f2)
                            $ typeError $ ReasonHigherFlow caller callee i f1 f2 pos)
                        (typeFlowMode <$> callTFs) (typeFlowMode <$> tfs) [1..]
                else typeError $ ReasonArity caller callee pos nCallTFs (length tfs')
            _ ->
                void $ unifyTypes (ReasonHigher caller callee pos)
                        fnTy $ HigherOrderType defaultProcModifiers callTFs
    let typing' = snd typing
    let errs = typingErrs typing'
    return $ if List.null errs
    then OK (calleeInfo, typing')
    else Err errs
matchTypes caller calleee pos _ _ _
        calleeInfo@(TestInfo exp) = do
    ty <- expType $ Unplaced exp
    typing <- snd <$> getTyping (unifyTypes (ReasonExpType exp boolType pos)
                                    boolType ty)
    let errs = typingErrs typing
    return $ if List.null errs
    then OK (calleeInfo, typing)
    else Err errs


matchTypeList :: Ident -> OptPos -> [TypeSpec] -> CallInfo
               -> Typed (MaybeErr (CallInfo,Typing))
matchTypeList callee pos callTypes
        calleeInfo@FirstInfo{fiPartial=partial,
                             fiTypes=calleeTypes} = do
    logTyped $ "Matching types " ++ show callTypes
               ++ " with " ++ show calleeInfo
    (matches, typing)
        <- getTyping $ unifyTypeList' callee pos callTypes calleeTypes
    let mismatches = List.map fst $ List.filter (invalidType . snd)
                       $ zip [1..] matches
    return $ if List.null mismatches
    then OK (calleeInfo{fiTypes=matches}, typing)
    else Err $ [ReasonArgType partial callee n pos | n <- mismatches]
            ++ typingErrs typing
matchTypeList _ _ _ info = shouldnt $ "matchTypeList on " ++ show info



unifyTypeList' :: ProcName -> OptPos -> [TypeSpec] -> [TypeSpec] -> Typed [TypeSpec]
unifyTypeList' callee pos callerTypes calleeTypes
    = zipWith3M (unifyTypes . flip (ReasonArgType False callee) pos)
                        [1..] callerTypes calleeTypes


invalidType :: TypeSpec -> Bool
invalidType InvalidType = True
invalidType (TypeSpec _ _ params) = any invalidType params
invalidType (HigherOrderType _ tfs) = any (invalidType . typeFlowType) tfs
invalidType _ = False


-- | Canonicalise a list of types, with type variables starting from the
-- supplied Int
canonicalise :: Int -> [TypeSpec] -> ([TypeSpec],Int)
canonicalise ctr tys = fst $ canonicaliseList Map.empty ctr tys


canonicaliseList :: Map TypeVarName TypeSpec -> Int -> [TypeSpec]
                 -> (([TypeSpec], Int), Map TypeVarName TypeSpec)
canonicaliseList tyMap ctr [] = (([],ctr), tyMap)
canonicaliseList tyMap ctr (ty:tys) =
    let ((ty', ctr'), tyMap') = canonicaliseSingle tyMap ctr ty
        ((tys', ctr''), tyMap'') = canonicaliseList tyMap' ctr' tys
    in ((ty':tys', ctr''), tyMap'')


canonicaliseSingle :: Map TypeVarName TypeSpec -> Int -> TypeSpec
                   -> ((TypeSpec, Int), Map TypeVarName TypeSpec)
canonicaliseSingle tyMap ctr (TypeVariable ty) =
    case Map.lookup ty tyMap of
        Nothing ->
            let ty' = TypeVariable $ FauxTypeVar ctr
            in ((ty', ctr + 1),Map.insert ty ty' tyMap)
        Just ty' -> ((ty', ctr),tyMap)
canonicaliseSingle tyMap ctr ty@TypeSpec{typeParams=tys} =
    let ((tys', ctr'), tyMap') = canonicaliseList tyMap ctr tys
    in ((ty{typeParams=tys'}, ctr'), tyMap')
canonicaliseSingle tyMap ctr ty@HigherOrderType{higherTypeParams=tfs} =
    let tys = typeFlowType <$> tfs
        ((tys', ctr'), tyMap') = canonicaliseList tyMap ctr tys
    in ((ty{higherTypeParams=zipWith TypeFlow tys' $ typeFlowMode <$> tfs}, ctr'), tyMap')
canonicaliseSingle tyMap ctr ty = ((ty, ctr), tyMap)


-- | Refresh all type variables in a list of TypeSpecs.
-- Does not modify the underlying Typing, excluding the typeVarCounter
refreshTypes :: [TypeSpec] -> Typed [TypeSpec]
refreshTypes tys = do
    tyVarCount <- gets typeVarCounter
    let (tys', tyVarCount') = canonicalise tyVarCount tys
    modify (\s -> s{typeVarCounter=tyVarCount'})
    when (tys /= tys')
        $ logTyped $ "Refreshed types " ++ show tys ++ " with " ++ show tys'
    return tys'


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
        -- | The determinism context in which this stmt appears
        bindingDetism    :: Determinism,
        -- | The purity context in which this stmt appears
        bindingImpurity  :: Impurity,
        -- | The resources in scope where this stmt appears
        bindingResources :: Set ResourceSpec,
        -- | The variables defined when this stmt appears
        bindingVars      :: UnivSet VarName,
        -- | The variables defined at the current loop exit
        bindingBreakVars :: UnivSet VarName
        }


instance Show BindingState where
    show (BindingState detism impurity resources boundVars breakVars) =
        impurityFullName impurity ++ " " ++ determinismFullName detism
        ++ " computation binding " ++ showUnivSet id boundVars
        ++ ", break set = " ++ showUnivSet id breakVars
        ++ ", with resources " ++ showSet show resources


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
initBindingState :: ProcDef -> Set ResourceSpec -> BindingState
initBindingState pdef resources =
    BindingState Det impurity resources emptyUnivSet UniversalSet
    where impurity = expectedImpurity $ procImpurity pdef


-- | BindingState for a failing computation (every possible variable is bound if
-- this succeeds, but it won't succeed).
failingBindingState :: BindingState -> BindingState
failingBindingState state =
    BindingState Failure Pure (bindingResources state) UniversalSet UniversalSet


-- | BindingState at the top of a loop, based on state before the loop.
-- Variables can't disappear during a loop, so the variables at the loop head
-- will always be exactly those defined before the loop.  The variables
-- available at the loop exit will be the intersection of the sets of variables
-- defined at all loop breaks, so we initialise the set of break variables to
-- the universal set.
loopEntryBindingState :: BindingState -> BindingState
loopEntryBindingState before =
    before {bindingBreakVars = UniversalSet}


-- | BindingState after a loop, based on the state before loop entry and the
-- binding state at the end of processing the loop.  The determinism after the
-- loop will be the same as before; the bound variables will the intersection of
-- the variables defined at all breaks.  If this is a nested loop, then we
-- restore the set of variables from before entering the inner loop.
postLoopBindingState :: BindingState -> BindingState -> BindingState
postLoopBindingState before loop =
    loop {bindingDetism = bindingDetism before
         ,bindingVars = bindingBreakVars loop
         ,bindingBreakVars = bindingBreakVars before}


-- | The intersection of two Maybe (Set a), where Nothing denotes the universal
-- set.
intersectMaybeSets :: Ord a => Maybe (Set a) -> Maybe (Set a) -> Maybe (Set a)
intersectMaybeSets Nothing mset = mset
intersectMaybeSets mset Nothing = mset
intersectMaybeSets (Just mset1) (Just mset2) =
    Just $ Set.intersection mset1 mset2


-- | the join of two BindingStates.
joinState :: BindingState -> BindingState -> BindingState
joinState (BindingState detism1 impurity1 resources1 boundVars1 breakVars1)
          (BindingState detism2 impurity2 resources2 boundVars2 breakVars2) =
           BindingState detism  impurity  resources  boundVars  breakVars
  where detism    = determinismJoin detism1 detism2
        impurity  = max impurity1 impurity2
        resources = resources1 `Set.intersection` resources2
        breakVars = breakVars1 `USet.intersection` breakVars2
        boundVars = boundVars1 `USet.intersection` boundVars2


-- | Add some bindings to a BindingState
addBindings :: Set VarName -> BindingState -> BindingState
addBindings vars st@BindingState{bindingDetism=Terminal} = st
addBindings vars st@BindingState{bindingDetism=Failure}  = st
addBindings vars st@BindingState{bindingDetism=Det} =
    st {bindingVars=FiniteSet vars `USet.union` bindingVars st}
addBindings vars st@BindingState{bindingDetism=SemiDet} =
    st {bindingVars=FiniteSet vars `USet.union` bindingVars st}


-- | Returns the deterministic version of the specified binding state.
forceDet :: BindingState -> BindingState
forceDet st =
    st {bindingDetism = determinismSucceed $ bindingDetism st}


-- | Returns the definitely failing version of the specified binding state.
forceFailure :: BindingState -> BindingState
forceFailure st =
        st {bindingVars = UniversalSet,
            bindingDetism = determinismFail $ bindingDetism st}


-- | Returns the binding state after a statement with the specified determinism that
--   definitely binds the specified variables.
bindingStateSeq :: Determinism -> Impurity -> Set VarName -> BindingState
                -> BindingState
bindingStateSeq stmtDetism impurity outputs st =
    st {bindingDetism=detism', bindingImpurity=impurity', bindingVars=vars'}
  where detism' = bindingDetism st `determinismSeq` stmtDetism
        impurity' = bindingImpurity st `impuritySeq` impurity
        vars'   = if determinismProceding detism'
                  then FiniteSet outputs `USet.union` bindingVars st
                  else UniversalSet


-- | Returns the binding state after a next statement entered in the specified
-- binding state.
bindingStateAfterNext :: BindingState -> BindingState
bindingStateAfterNext st = st {bindingDetism=Terminal, bindingVars=UniversalSet}


-- | Returns the binding state after a break statement entered in the specified
-- binding state.
bindingStateAfterBreak :: BindingState -> BindingState
bindingStateAfterBreak st =
    st { bindingDetism=Terminal, bindingVars=UniversalSet
       , bindingBreakVars=bindingVars st `USet.intersection` bindingBreakVars st
       }


-- | which of a set of expected bindings will be unbound if execution reach this
-- binding state
missingBindings :: Set VarName -> BindingState -> Set VarName
missingBindings vars st = vars `subtractUnivSet` bindingVars st


-- | Is the specified variable defined in the specified binding state?
assignedIn :: VarName -> BindingState -> Bool
assignedIn var bstate = var `USet.member` bindingVars bstate


-- |Return a list of (actual,formal) argument mode pairs.
actualFormalModes :: [(FlowDirection,Bool,Maybe VarName)] -> CallInfo
                  -> [(FlowDirection,FlowDirection)]
actualFormalModes modes FirstInfo{fiFlows=flows} =
    zip flows (sel1 <$> modes)
actualFormalModes _ info = shouldnt $ "actualFormalModes on " ++ show info


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if all actual arguments are instantiated
-- if the corresponding parameter is an input.
matchModeList :: [(FlowDirection,Bool,Maybe VarName)]
              -> CallInfo -> Bool
matchModeList modes info@FirstInfo{fiPartial=False}
    -- Check that no param is in where actual is out
    = (ParamIn,ParamOut) `notElem` actualFormalModes modes info
matchModeList _ _ = False


-- |Match up the argument modes of a call with the available parameter
-- modes of the callee.  Determine if the call mode exactly matches the
-- proc mode.
exactModeMatch :: [(FlowDirection,Bool,Maybe VarName)]
               -> CallInfo -> Bool
exactModeMatch modes info@FirstInfo{fiPartial=False}
    = all (uncurry (==)) $ actualFormalModes modes info
exactModeMatch modes info@FirstInfo{fiPartial=True}
    = all (==(ParamIn,ParamIn)) (init formalModes)
        && last formalModes == (ParamOut, ParamOut)
    where formalModes = actualFormalModes modes info
exactModeMatch _ HigherInfo{} = True
exactModeMatch _ TestInfo{} = True

overloadErr :: StmtTypings -> TypeError
overloadErr StmtTypings{typingStmt=call,typingInfos=candidates} =
    -- XXX Need to give list of matching procs
    ReasonOverload (infoDescription <$> candidates) $ place call

infoDescription :: CallInfo -> String
infoDescription FirstInfo{fiProc=pspec, fiPartial=partial} =
    show pspec ++ (if partial then " (partial)" else "")
infoDescription info = show info


-- |Given type assignments to variables, resolve modes in a proc body, building
--  a revised, properly moded body, or indicate a mode error. This must handle
--  several cases:
--  * Test statements must be handled, determining which stmts in a test context
--    are actually tests, and reporting an error for tests outside a test
--    context
--  * Implied modes:  in a test context, allow in mode where out mode is
--    expected by assigning a fresh temp variable and generating an = test of
--    the variable against the in value.
--  * Handle in-out call mode where an out-only argument is expected.
--  * Reaching the end of a Terminal or Failure statement sequence with a weaker
--    determinism.
--  This code threads a set of assigned variables through, which starts as
--  the set of in parameter names.
modecheckStmts :: ModSpec -> ProcName -> OptPos -> BindingState -> Determinism
               -> Bool -> [Placed Stmt] -> Typed ([Placed Stmt],BindingState)
modecheckStmts _ name pos assigned detism final [] = do
    logTyped $ "Mode check end of " ++ show detism ++ " proc '" ++ name ++ "'"
    when final
        $ typeErrors $ detismCheck name pos detism $ bindingDetism assigned
    return ([],assigned)
modecheckStmts m name pos assigned detism final (pstmt:pstmts) = do
    logTyped $ "Mode check stmt " ++ showStmt 16 (content pstmt)
    when (bindingDetism assigned == Terminal)
        $ typeErrors [ReasonUnnreachable name (place pstmt)]
    let final' = final && List.null pstmts
    (pstmt',assigned') <-
        placedApply (modecheckStmt m name pos assigned detism final') pstmt
    logTyped $ "Now assigned = " ++ show assigned'
    (pstmts',assigned'')
        <- modecheckStmts m name pos assigned' detism final pstmts
    return (pstmt'++pstmts',assigned'')


-- |Mode check a single statement, returning a list of moded statements, plus a
--  set of variables bound by this statement, and a list of errors.  When this
--  is called, all variable and type variable types have already been
--  established in the Typed monad.
--
--  We select a mode as follows:
--    0.  If some input arguments are not assigned, report an uninitialised
--        variable error.
--    1.  If there is an exact match for the current instantiation state, select
--        it.
--    2.  If this is a test context and there is a match for the current
--        instantiation state (allowing ParamIn arguments where the parameter is
--        ParamOut), select it, and transform by replacing each non-identical
--        flow ParamIn argument with a fresh ParamOut variable, and adding an =
--        test call to test the fresh variable against the actual ParamIn
--        argument.
--    3.  If there is a match (possibly with some ParamIn args where ParamOut is
--        expected), then select that mode but delay the call.
--    4.  Otherwise report a mode error.
--
--    In case there are multiple modes that match one of those criteria, select
--    the first that matches.

modecheckStmt :: ModSpec -> ProcName -> OptPos -> BindingState -> Determinism
              -> Bool -> Stmt -> OptPos -> Typed ([Placed Stmt],BindingState)
modecheckStmt m name defPos assigned detism final
    stmt@(ProcCall (First cmod cname pid) d resourceful args) pos = do
    logTyped $ "Mode checking call   : " ++ show stmt
    logTyped $ "    with assigned    : " ++ show assigned

    -- Find arg types and expand type variables
    args' <- modeCheckExps m name defPos assigned detism args
    assignedVars <- gets (Map.keysSet . typingDict)
    x <- callInfos assignedVars (maybePlace stmt pos)
    infos <- callInfos assignedVars (maybePlace stmt pos) <&> typingInfos
    actualTypes <- mapM (expType >=> ultimateType) args'
    logTyped $ "    actual types     : " ++ show actualTypes
    let actualModes = List.map (expMode assigned) args'
    logTyped $ "    actual modes     : " ++ show actualModes
    checkFlowErrors False False cname pos actualModes ([],assigned) $ do
        typeMatches <- catOKs <$> mapM
                    (matchTypes name cname pos resourceful actualTypes (sel1 <$> actualModes))
                    infos
        logTyped $ "Type-correct modes   : " ++ show typeMatches
        -- All the possibly matching modes
        let modeMatches
                = List.filter (matchModeList actualModes . fst) typeMatches
        logTyped $ "Possible mode matches: " ++ show modeMatches
        let exactMatches
                = List.filter (exactModeMatch actualModes . fst) typeMatches
        logTyped $ "Exact mode matches: " ++ show exactMatches
        let stmt' = ProcCall (First cmod cname pid) d resourceful args'
        case (exactMatches,modeMatches) of
            ((match,typing):rest, _) -> do
                put typing
                unless (List.null rest) $
                    typeError $ ReasonWarnMultipleMatches match (fst <$> rest) pos
                finaliseCall m name defPos assigned detism resourceful
                            final pos args' match stmt'
            ([], (match,typing):rest) -> do
                put typing
                unless (List.null rest) $
                    typeError $ ReasonWarnMultipleMatches match (fst <$> rest) pos
                finaliseCall m name defPos assigned detism resourceful
                            final pos args' match stmt'
            ([],[]) -> do
                case (cmod, cname, actualModes, args) of
                    -- Special cases to handle = as assignment when one argument is
                    -- known to be defined and the other is an output or unknown.
                    ([], "=", [(ParamIn,True,_),(ParamOut,_,_)],[arg1,arg2]) ->
                        modecheckStmt m name defPos assigned detism final
                            (ForeignCall "llvm" "move" [] [arg1, arg2]) pos
                    ([], "=", [(ParamOut,_,_),(ParamIn,True,_)],[arg1,arg2]) ->
                        modecheckStmt m name defPos assigned detism final
                            (ForeignCall "llvm" "move" [] [arg2, arg1]) pos
                    _ -> do
                        logTyped $ "Mode errors in call"
                        typeError $ ReasonUndefinedFlow cname pos
                        return ([],assigned)
modecheckStmt m name defPos assigned detism final
  stmt@(ProcCall (Higher fn) d resourceful args) pos = do
    logTyped $ "Mode checking higher : " ++ show stmt
    logTyped $ "    with assigned    : " ++ show assigned
    fnArgs' <- modeCheckExps m name defPos assigned detism (fn:args)
    actualTypes@(fnTy:_) <- mapM (expType >=> ultimateType) fnArgs'
    logTyped $ "    actual types     : " ++ show actualTypes
    let actualModes = List.map (expMode assigned) fnArgs'
    logTyped $ "    actual modes     : " ++ show actualModes
    checkFlowErrors False True (show $ innerExp $ content fn)
                    pos actualModes ([],assigned)
      $ do
        let typeflows = List.zipWith TypeFlow actualTypes
                      $ sel1 <$> actualModes
        let (fn':args') = List.zipWith setPExpTypeFlow typeflows fnArgs'
        case fnTy of
            HigherOrderType mods fnTyFlows -> do
                let detism' = case on compare length (tail typeflows) fnTyFlows of
                        LT -> SemiDet -- de-reified test
                        GT -> Det     -- reified test
                        EQ -> modifierDetism mods
                    imp = modifierImpurity mods
                    assigned' = bindingStateSeq detism' imp (pexpListOutputs fnArgs') assigned
                typeErrors
                    $ detismPurityErrors pos "higher-order term" (show $ innerExp $ content fn)
                        detism (bindingImpurity assigned) resourceful
                        detism' imp (modifierResourceful mods)
                return ([maybePlace (ProcCall (Higher fn') detism' resourceful args') pos],
                        assigned')
            _ -> shouldnt $ "modecheckStmt on higher typed " ++ show fnTy
modecheckStmt m name defPos assigned detism final
    stmt@(ForeignCall lang cname flags args) pos = do
    logTyped $ "Mode checking foreign call " ++ show stmt
    logTyped $ "    with assigned " ++ show assigned
    args' <- modeCheckExps m name defPos assigned detism args
    actualTypes <- mapM (expType >=> ultimateType) args'
    let actualModes = List.map (expMode assigned) args'
    checkFlowErrors True False ("foreign " ++ lang ++ " " ++ cname)
                    pos actualModes ([],assigned)
      $ do
            let typeflows = List.zipWith TypeFlow actualTypes
                            $ sel1 <$> actualModes
            logTyped $ "    types and modes = " ++ show typeflows
            let actualImpurity = flagsImpurity flags
            let impurity = bindingImpurity assigned
            let stmtDetism = flagsDetism flags
            let foreignIdent = "foreign " ++ cname
            let errs = [ReasonDeterminism foreignIdent stmtDetism detism pos
                       | Det `determinismLEQ` detism
                         && not (stmtDetism `determinismLEQ` detism)]
                       ++ [ReasonPurity foreignIdent actualImpurity impurity pos
                          | actualImpurity > impurity]
            typeErrors errs
            let args'' = zipWith setPExpTypeFlow typeflows args'
            let stmt' = ForeignCall lang cname flags args''
            let vars = pexpListOutputs args''
            let nextDetism = determinismSeq (bindingDetism assigned) stmtDetism
            let assigned' = assigned {bindingDetism=nextDetism}
            logTyped $ "New instr = " ++ show stmt'
            return ([maybePlace stmt' pos],
                    bindingStateSeq stmtDetism impurity vars assigned)
modecheckStmt _ _ _ assigned _ final Nop pos = do
    logTyped "Mode checking Nop"
    return ([maybePlace Nop pos], assigned)
modecheckStmt _ _ _ assigned _ final Fail pos = do
    logTyped "Mode checking Fail"
    return ([maybePlace Fail pos], forceFailure assigned)
modecheckStmt m name defPos assigned detism final
    stmt@(Cond tstStmt thnStmts elsStmts _ _ res) pos = do
    logTyped $ "Mode checking conditional " ++ show stmt
    (tstStmt', assigned1) <-
        placedApplyM
        (modecheckStmt m name defPos assigned SemiDet False)
        tstStmt
    logTyped $ "Assigned by test: " ++ show assigned1
    condBindings <- mapFromUnivSetM ultimateVarType Set.empty
                    $ bindingVars assigned1
    (thnStmts', assigned2) <-
        modecheckStmts m name defPos (forceDet assigned1) detism
                       final thnStmts
    logTyped $ "Assigned by then branch: " ++ show assigned2
    (elsStmts', assigned3) <-
        modecheckStmts m name defPos assigned detism final elsStmts
    logTyped $ "Assigned by else branch: " ++ show assigned3
    if mustSucceed assigned1 -- is condition guaranteed to succeed?
      then do
        logTyped $ "Assigned by succeeding conditional: " ++ show assigned2
        return (tstStmt'++thnStmts', assigned2)
      else if mustFail assigned1 -- is condition guaranteed to fail?
      then do
        logTyped $ "Assigned by failing conditional: " ++ show assigned3
        bindings <- mapFromUnivSetM ultimateVarType Set.empty
                    $ bindingVars assigned3
        impurity <- lift $ stmtsImpurity tstStmt'
        let stmts' = if impurity > Pure
                     -- if the test is non-pure, need to keep the test around
                     then Not (seqToStmt tstStmt') `maybePlace` pos:elsStmts'
                     -- otherwise, the cond must fail and wont bind anything
                     else elsStmts'
        return (stmts', assigned3)
      else do
        let finalAssigned = assigned2 `joinState` assigned3
        logTyped $ "Assigned by conditional: " ++ show finalAssigned
        bindings <- mapFromUnivSetM ultimateVarType Set.empty
                    $ bindingVars finalAssigned
        return
          ([maybePlace (Cond (seqToStmt tstStmt') thnStmts' elsStmts'
                        (Just condBindings) (Just bindings) res)
            pos], finalAssigned)
modecheckStmt m name defPos assigned detism final
    stmt@(TestBool exp) pos = do
    logTyped $ "Mode checking test " ++ show exp
    let exp' = [maybePlace (TestBool $ setExpTypeFlow (TypeFlow boolType ParamIn) exp) pos]
    case expIsConstant exp of
      Just (IntValue 0) -> return (exp', forceFailure assigned)
      Just (IntValue 1) -> return ([maybePlace Nop pos], assigned)
      _                 -> return (exp',
                                   bindingStateSeq SemiDet Pure Set.empty
                                   assigned)
modecheckStmt m name defPos assigned detism final
    stmt@(Loop stmts _ res) pos = do
    logTyped $ "Mode checking loop " ++ show stmt
    -- XXX `final` is wrong:  checking for a terminal loop is not this easy
    (stmts', assigned') <-
      modecheckStmts m name defPos (loopEntryBindingState assigned) detism
                     final stmts
    let startVars = toSet Set.empty $ bindingVars assigned
    logTyped $ "Assigned by loop: " ++ show assigned'
    vars <- mapFromUnivSetM ultimateVarType startVars
                    $ bindingBreakVars assigned'
    logTyped $ "Loop exit vars: " ++ show vars
    return ([maybePlace (Loop stmts' (Just vars) res) pos]
           ,postLoopBindingState assigned assigned')
modecheckStmt m name defPos assigned detism final
    stmt@(UseResources resources _ stmts) pos = do
    logTyped $ "Mode checking use ... in stmt " ++ show stmt
    canonRes <- lift (mapM (canonicaliseResourceSpec pos "use block") resources)
    let resources' = fst <$> canonRes
    let assigned' = assigned { bindingResources =
            List.foldr Set.insert (bindingResources assigned) resources' }
    (stmts', assigned'')
        <- modecheckStmts m name defPos assigned' detism final stmts
    let resVars = USet.fromList $ resourceName <$> resources'
    resfulBoundPre <- resfulBoundVars resVars assigned
    resfulBoundPost <- resfulBoundVars resVars assigned''
    let boundVars = bindingVars assigned''
    let vars = whenFinite (Set.\\ (Map.keysSet resfulBoundPost
                                    Set.\\ Map.keysSet resfulBoundPre)) boundVars
    return
        ([maybePlace (UseResources resources' (Just resfulBoundPre) stmts')
          pos]
        ,assigned'' { bindingResources = bindingResources assigned,
                      bindingVars = vars })
  where
    resfulBoundVars resVars bindings = do
        let boundVars = bindingVars bindings
        varTys <- mapFromUnivSetM ultimateVarType
                    (USet.toSet Set.empty boundVars) boundVars
        let filter nm ty = nm `USet.member` resVars
                        || isResourcefulHigherOrder ty
        return $ Map.filterWithKey filter varTys
-- XXX Need to implement these correctly:
modecheckStmt m name defPos assigned detism final
    stmt@(And stmts) pos = do
    logTyped $ "Mode checking conjunction " ++ show stmt
    (stmts', assigned')
        <- modecheckStmts m name defPos assigned detism final stmts
    if mustSucceed assigned'
        then return (stmts', assigned')
        else return ([maybePlace (And stmts') pos], assigned')
modecheckStmt m name defPos assigned detism final
    stmt@(Or disj _ res) pos = do
    logTyped $ "Mode checking disjunction " ++ show stmt
    (disj',assigned') <-
        modecheckDisj m name defPos assigned detism final
                      (failingBindingState assigned) disj
    varDict <- mapFromUnivSetM ultimateVarType Set.empty
                $ bindingVars assigned'
    return ([maybePlace (Or disj' (Just varDict) res) pos],assigned')
modecheckStmt m name defPos assigned detism final
    (Not stmt) pos = do
    logTyped $ "Mode checking negation " ++ show stmt
    (stmt', _) <-
        placedApplyM
        (modecheckStmt m name defPos assigned detism final)
        stmt
    return ([maybePlace (Not (seqToStmt stmt')) pos], assigned)
modecheckStmt _ _ _ _ _ final stmt@For{} pos =
    shouldnt $ "For statement left by unbranching: " ++ show stmt
modecheckStmt _ _ _ _ _ final stmt@Case{} pos =
    shouldnt $ "Case statement left by unbranching: " ++ show stmt
modecheckStmt m name defPos assigned detism final
    Break pos = do
    logTyped $ "Mode checking break with assigned=" ++ show assigned
    return ([maybePlace Break pos],bindingStateAfterBreak assigned)
modecheckStmt m name defPos assigned detism final
    Next pos = do
    logTyped $ "Mode checking continue with assigned=" ++ show assigned
    return ([maybePlace Next pos],bindingStateAfterNext assigned)


-- | Mode check a list of Placed Exps,
-- returning the mode checked Placed Exps and tmp counter
modeCheckExps :: ModSpec -> ProcName -> OptPos -> BindingState -> Determinism
             -> [Placed Exp] -> Typed [Placed Exp]
modeCheckExps _ _ _ _ _ [] = return []
modeCheckExps m name pos assigned detism (pexp:pexps) = do
    logTyped $ "Mode check exp " ++ show (content pexp)
    pexp' <- placedApply (modeCheckExp m name pos assigned detism) pexp
    logTyped $ "Mode check exp resulted in " ++ show (content pexp')
    pexps' <- modeCheckExps m name pos assigned detism pexps
    return (pexp':pexps')

-- | Mode check an Expression
-- This performs mode checking on the inner Stmts inside an AnonProc
modeCheckExp :: ModSpec -> ProcName -> OptPos -> BindingState -> Determinism
             -> Exp -> OptPos -> Typed (Placed Exp)
modeCheckExp m name defPos assigned _
        exp@(AnonProc mods@ProcModifiers{modifierDetism=detism} params ss _ res) pos = do
    logTyped $ "Mode checking AnonProc " ++ show exp
    let inArgs = List.foldl collectInParams Set.empty params
    (ss',_) <- modecheckStmts m name defPos (addBindings inArgs assigned)
                             detism True ss
    let paramVars = expVar . content . paramToVar <$> params
    let toClose = stmtsInputs ss' `Set.difference` Set.fromList paramVars
    varDict <- mapFromUnivSetM ultimateVarType Set.empty
                $ bindingVars assigned
    let closed = Map.filterWithKey (const . flip Set.member toClose) varDict
    params' <- (content <$>) <$> updateParamTypes (Unplaced <$> params)
    return (maybePlace (AnonProc mods params' ss' (Just closed) res) pos)
modeCheckExp m name defPos assigned detism
        (Typed exp ty cast) pos = do
    ty' <- ultimateType ty
    cast' <- forM cast ultimateType
    exp' <- modeCheckExp m name defPos assigned detism exp pos
    return (maybePlace (Typed (content exp') ty' cast') pos)
modeCheckExp m name defPos assigned detism exp pos =
    return (maybePlace exp pos)

-- | Check for flow errors in the given list of flows
checkFlowErrors :: Bool -> Bool -> String -> OptPos -> [(FlowDirection, Bool, Maybe VarName)]
                -> a -> Typed a -> Typed a
checkFlowErrors isForeign isHigherOrder name pos flows thn doEls = do
    let numbering = [if isHigherOrder then 0 else 1 ..]
    let flowErrs = [ReasonArgFlow name num pos
                   | ((mode,avail,_),num) <- zip flows numbering
                   , not avail && (if isForeign
                                   then mode == ParamIn
                                   else flowsIn mode)]
    if List.null flowErrs
    then doEls
    else do
        logTyped "mode error in foreign call"
        typeErrors flowErrs
        return thn


-- |Add in-flowing params to a set of varnames
collectInParams :: Set.Set VarName -> Param -> Set.Set VarName
collectInParams s (Param n _ flow _)
    | flowsIn flow = Set.insert n s
collectInParams s _ = s


modecheckDisj :: ModSpec -> ProcName -> OptPos -> BindingState -> Determinism
              -> Bool -> BindingState -> [Placed Stmt]
              -> Typed ([Placed Stmt],BindingState)
modecheckDisj m name defPos assigned detism final disjAssigned [] =
    return ([],disjAssigned)
modecheckDisj m name defPos assigned detism final disjAssigned (stmt:stmts) = do
    -- The last disjunct in a disjunction must have the same determinism
    -- required of the whole disjunction; others can be SemiDet.
    let detism1 = if List.null stmts then detism else SemiDet
    (disj1,assigned1) <-
        placedApply (modecheckStmt m name defPos assigned detism1 final) stmt
    let disjAssigned' = joinState disjAssigned assigned1
    (disjs,disjAssigned'') <-
        modecheckDisj m name defPos assigned detism final disjAssigned' stmts
    let disj1' = seqToStmt disj1
    return (disj1':disjs, disjAssigned'')



-- |Produce a typed statement sequence, the binding state, and final temp count
-- from a single proc call.
finaliseCall :: ModSpec -> ProcName -> OptPos -> BindingState -> Determinism -> Bool
             -> Bool -> OptPos -> [Placed Exp] -> CallInfo -> Stmt
             -> Typed ([Placed Stmt],BindingState)
finaliseCall m name defPos assigned detism resourceful final pos args
             match@FirstInfo{ fiProc=matchProc
                            , fiDetism=matchDetism
                            , fiImpurity=matchImpurity
                            , fiInRes=inResources
                            , fiOutRes=outResources
                            , fiNeedsResBang=needsResBang
                            , fiPartial=isPartial} stmt = do
    let matchName = procSpecName matchProc
    let allResources = inResources `Set.union` outResources
    let impurity = bindingImpurity assigned
    let isPartial = fiPartial match
    tys <- mapM (expType >=> ultimateType) args
    (args',stmts) <- matchArguments (zipWith TypeFlow tys (fiFlows match)) args
    let outOfScope = allResources `Set.difference`
                    (bindingResources assigned `Set.union` specialResourcesSet)
    let specials = Set.map resourceName
                   $ inResources `Set.intersection` specialResourcesSet
    let avail    = USet.toSet Set.empty $ bindingVars assigned
    typeErrors $
            detismPurityErrors pos "proc" (show matchProc)
                detism impurity resourceful
                matchDetism matchImpurity needsResBang
            ++ [ReasonResourceOutOfScope matchName res pos
                | res <- Set.toList outOfScope]
            ++ [ReasonResourceUnavail matchName res pos
                | res <- Set.toList
                    $ missingBindings
                      (Set.map resourceName
                       (inResources Set.\\ specialResourcesSet
                                    Set.\\ outOfScope))
                      assigned]
    let specials = Set.map resourceName
                 $ inResources `Set.intersection` specialResourcesSet
    if isPartial
    then do
        let result = last args'
        resultTy <- expType result
        let closed = init args'
        let partial = Closure matchProc closed `withType` resultTy
        logTyped $ "Finalising call as partial: " ++ show partial
        typeErrors
              [ReasonResourceUnavail ("partial application of " ++ name) res pos
              | res <- Set.toList specials]
        modecheckStmt m name defPos assigned detism final
            (ForeignCall "llvm" "move" [] [Unplaced partial, result]) pos
    else do
        let stmt' = ProcCall (First (procSpecMod matchProc) (procSpecName matchProc)
                                    (Just $ procSpecID matchProc))
                    matchDetism resourceful args'
        logTyped $ "Finalising call    :  " ++ show stmt'
        logTyped $ "Input resources    :  " ++ simpleShowSet inResources
        logTyped $ "Output resources   :  " ++ simpleShowSet outResources
        logTyped $ "Specials in call   :  " ++ simpleShowSet specials
        logTyped $ "Available vars     :  " ++ simpleShowSet avail
        logTyped $ "Available resources:  " ++ simpleShowSet (bindingResources assigned)
        let specialInstrs =
                [ move (s `withType` ty) (varSetTyped r ty)
                | resourceful -- no specials unless resourceful
                , r <- Set.elems $ specials Set.\\ avail
                , let (f,ty) = fromMaybe (const $ StringValue "Unknown" CString,
                                        cStringType)
                                $ Map.lookup r specialResources
                , let s = f $ maybePlace stmt pos]
        let assigned' =
                bindingStateSeq matchDetism matchImpurity
                (pexpListOutputs args')
                (assigned {bindingVars =
                    FiniteSet (Set.map resourceName outResources)
                            `USet.union` bindingVars assigned })
        logTyped $ "Generated special stmts = " ++ show specialInstrs
        logTyped $ "New instr = " ++ show stmt'
        logTyped $ "Generated extra stmts = " ++ show stmts
        (stmts',assigned'') <-
            modecheckStmts m name pos assigned' detism final stmts
        return (specialInstrs ++ maybePlace stmt' pos : stmts', assigned'')
finaliseCall m name defPos assigned detism resourceful final pos args
        (HigherInfo fn) _ =
    modecheckStmt m name defPos assigned detism final
        (ProcCall (Higher $ fn `maybePlace` pos) detism resourceful args) pos
finaliseCall m name defPos assigned detism resourceful final pos args
        (TestInfo exp) _ =
    modecheckStmt m name defPos assigned detism final (TestBool exp) pos


detismPurityErrors :: OptPos -> String -> String
                   -> Determinism -> Impurity -> Bool
                   -> Determinism -> Impurity -> Bool -> [TypeError]
detismPurityErrors pos prefix name contextDetism contextImpurity
    banged detism impurity usesResources =
    -- XXX Should postpone detism errors until we see if we
    -- can work out if the test is certain to succeed.
    -- Perhaps add mutual exclusion inference to the mode
    -- checker.
    [ReasonDeterminism prefixedName detism contextDetism pos
    | Det `determinismLEQ` contextDetism
        && not (detism `determinismLEQ` contextDetism)]
    ++ [ReasonPurity prefixedName impurity contextImpurity pos
        | impurity > contextImpurity]
    ++ [ReasonLooksPure prefixedName impurity pos
        | impurity > Pure && not banged]
    ++ [ReasonActuallyPure prefixedName impurity pos
        | impurity == Pure && banged && not usesResources]
  where prefixedName = prefix ++ " " ++ name


matchArguments :: [TypeFlow] -> [Placed Exp] -> Typed ([Placed Exp],[Placed Stmt])
matchArguments [] [] = return ([],[])
matchArguments [] _ = shouldnt "matchArguments arity mismatch"
matchArguments _ [] = shouldnt "matchArguments arity mismatch"
matchArguments (typeflow:typeflows) (arg:args) = do
    (arg', stmts1) <- matchArgument typeflow arg
    (args', stmts2) <- matchArguments typeflows args
    return (arg':args', stmts1++stmts2)


-- |Transform an argument as supplied to match the param it is passed to.  This
-- includes handling implied modes by generating a fresh variable to pass in the
-- call, and generating code to match it with the provided input.  Thus also
-- attaches the correct type to the argument.
matchArgument :: TypeFlow -> Placed Exp -> Typed (Placed Exp,[Placed Stmt])
matchArgument typeflow arg
    | ParamOut == typeFlowMode typeflow
      && ParamIn == flattenedExpFlow (content arg) = do
          tmpCount <- gets tyTmpCtr
          modify $ \s -> s{tyTmpCtr = tmpCount + 1}
          let var = mkTempName tmpCount
              inTypeFlow = typeflow {typeFlowMode = ParamIn}
              arg' = setPExpTypeFlow inTypeFlow arg
              setVar = Unplaced $ setExpTypeFlow typeflow (varSet var)
              getVar = Unplaced $ setExpTypeFlow inTypeFlow (varGet var)
              call = ProcCall (regularProc "=") SemiDet False [getVar, arg']
          return (setVar, [maybePlace call $ place arg])
    | otherwise = return (setPExpTypeFlow typeflow arg,[])


-- |Return a list of error messages for too weak a determinism at the end of a
-- statement sequence.
detismCheck :: ProcName -> OptPos -> Determinism -> Determinism -> [TypeError]
detismCheck name pos expectedDetism actualDetism
    -- XXX Report ReasonUndeclaredTerminal if appropriate, when terminalness is
    -- analysed correctly.
    | actualDetism `determinismLEQ` expectedDetism = []
    | Det `determinismLEQ` expectedDetism = []
    | otherwise = [ReasonWeakDetism name actualDetism expectedDetism pos]


----------------------------------------------------------------
--                    Check foreign calls
----------------------------------------------------------------

-- | Add the specified type error if the specified test fails
reportErrorUnless :: TypeError -> Bool -> Typed ()
reportErrorUnless err False = typeError err
reportErrorUnless err True = return ()


-- | Make sure a foreign call is valid; otherwise report an error
validateForeign :: Stmt -> OptPos -> Typed ()
validateForeign stmt@(ForeignCall lang name tags args) pos = do
    argTypes <- mapM (expType >=> ultimateType) args
    maybeReps <- lift $ mapM lookupTypeRepresentation argTypes
    let numberedMaybes = zip maybeReps [1..]
    let untyped = snd <$> List.filter (isNothing . fst) numberedMaybes
    if List.null untyped
      then do
        let argReps = List.filter (not . repIsPhantom)
                      $ trustFromJust "validateForeign" <$> maybeReps
        logTyped $ "Type checking foreign " ++ lang ++ " call "
                   ++ unwords (name:tags)
                   ++ "(" ++ intercalate ", " (show <$> argReps) ++ ")"
        validateForeignCall lang name tags argReps stmt pos
      else
        typeErrors (flip (ReasonForeignArgType name) pos <$> untyped)
validateForeign stmt _ =
    shouldnt $ "validateForeign of non-foreign stmt " ++ showStmt 4 stmt


-- | Make sure a foreign call is valid; otherwise report an error
-- XXX Check that the outputs of LLVM instructions are correct, after
--     considering casting.
validateForeignCall :: String -> ProcName -> [String] -> [TypeRepresentation]
                    -> Stmt -> OptPos -> Typed ()
-- just assume C calls are OK
validateForeignCall "c" _ _ _ _ _  = return ()
-- A move with no non-phantom arguments:  all OK
validateForeignCall "llvm" "move" _ [] stmt pos = return ()
validateForeignCall "llvm" "move" _ [inRep,outRep] stmt pos
  | compatibleReps inRep outRep = return ()
  | otherwise       = typeError (ReasonWrongOutput "move" outRep inRep pos)
validateForeignCall "llvm" "move" _ argReps stmt pos =
    typeError (ReasonForeignArity "move" (length argReps) 2 pos)
validateForeignCall "llvm" name flags argReps stmt pos = do
    let arity = length argReps
    case argReps of
        [inRep1,inRep2,outRep] ->
          case Map.lookup name llvmMapBinop of
             Just (_,fam,outTy) -> do
               reportErrorUnless (ReasonWrongFamily name 1 fam pos)
                                 (fam == typeFamily inRep1)
               reportErrorUnless (ReasonWrongFamily name 2 fam pos)
                                 (fam == typeFamily inRep2)
               reportErrorUnless (ReasonIncompatible name inRep1 inRep2 pos)
                                 (compatibleReps inRep1 inRep2)
             Nothing ->
               if isJust $ Map.lookup name llvmMapUnop
               then typeError (ReasonForeignArity name arity 2 pos)
               else typeError (ReasonBadForeign "llvm" name pos)
        [inRep,outRep] ->
          case Map.lookup name llvmMapUnop of
             Just (_,famIn,famOut) ->
               reportErrorUnless (ReasonWrongFamily name 1 famIn pos)
                                 (famIn == typeFamily inRep)
             Nothing ->
               if isJust $ Map.lookup name llvmMapBinop
               then typeError (ReasonForeignArity name arity 3 pos)
               else typeError (ReasonBadForeign "llvm" name pos)
        _ -> if isJust $ Map.lookup name llvmMapBinop
             then typeError (ReasonForeignArity name arity 3 pos)
             else if isJust $ Map.lookup name llvmMapUnop
                  then typeError (ReasonForeignArity name arity 2 pos)
                  else typeError (ReasonBadForeign "llvm" name pos)
validateForeignCall "lpvm" name flags argReps stmt pos =
    checkLPVMArgs name flags argReps stmt pos
validateForeignCall lang name flags argReps stmt pos =
    typeError (ReasonForeignLanguage lang name pos)


-- | Are two types compatible for use as inputs to a binary LLVM op?
--   Used for type checking LLVM instructions.
compatibleReps :: TypeRepresentation -> TypeRepresentation -> Bool
compatibleReps Address      Address      = True
compatibleReps Address      (Bits bs)    = bs == wordSize
compatibleReps Address      (Signed bs)  = bs == wordSize
compatibleReps Address      (Floating _) = False
compatibleReps Address      (Func _ _)   = True
compatibleReps (Bits bs)    Address      = bs == wordSize
compatibleReps (Bits m)     (Bits n)     = m == n
compatibleReps (Bits m)     (Signed n)   = m == n
compatibleReps (Bits _)     (Floating _) = False
compatibleReps (Bits bs)    (Func _ _)   = bs == wordSize
compatibleReps (Signed bs)  Address      = bs == wordSize
compatibleReps (Signed m)   (Bits n)     = m == n
compatibleReps (Signed m)   (Signed n)   = m == n
compatibleReps (Signed _)   (Floating _) = False
compatibleReps (Signed bs)  (Func _ _)   = bs == wordSize
compatibleReps (Floating _) Address      = False
compatibleReps (Floating _) (Bits _)     = False
compatibleReps (Floating _) (Signed _)   = False
compatibleReps (Floating m) (Floating n) = m == n
compatibleReps (Floating _) (Func _ _)   = False
compatibleReps (Func _ _)   Address      = True
compatibleReps (Func i1 o1) (Func i2 o2) = sameLength i1 i2 && sameLength o1 o2 &&
                                           and (zipWith compatibleReps i1 i2) &&
                                           and (zipWith compatibleReps o1 o2)
compatibleReps (Func _ _)   (Bits bs)    = bs == wordSize
compatibleReps (Func _ _)   (Signed bs)  = bs == wordSize
compatibleReps (Func _ _)   (Floating _) = False


-- | Check arg types of an LPVM instruction
checkLPVMArgs :: String -> [String] -> [TypeRepresentation] -> Stmt -> OptPos
              -> Typed ()
checkLPVMArgs "alloc" _ [sz,struct] stmt pos = do
    reportErrorUnless (ReasonForeignArgRep "alloc" 1 sz "integer" pos)
                      (integerTypeRep sz)
    reportErrorUnless (ReasonForeignArgRep "alloc" 2 struct "address" pos)
                      (struct == Address)
checkLPVMArgs "alloc" _ args stmt pos =
    typeError (ReasonForeignArity "alloc" (length args) 2 pos)
checkLPVMArgs "access" _ [struct,offset,size,startOffset,val] stmt pos = do
    reportErrorUnless (ReasonForeignArgRep "access" 1 struct "address" pos)
                      (struct == Address)
    reportErrorUnless (ReasonForeignArgRep "access" 2 offset "integer" pos)
                      (integerTypeRep offset)
    reportErrorUnless (ReasonForeignArgRep "access" 3 size "integer" pos)
                      (integerTypeRep size)
    reportErrorUnless (ReasonForeignArgRep "access" 4 startOffset "integer" pos)
                      (integerTypeRep startOffset)
checkLPVMArgs "access" _ args stmt pos =
    typeError (ReasonForeignArity "access" (length args) 5 pos)
checkLPVMArgs "mutate" _ [old,new,offset,destr,sz,start,val] stmt pos = do
    reportErrorUnless (ReasonForeignArgRep "mutate" 1 old "address" pos)
                      (old == Address)
    reportErrorUnless (ReasonForeignArgRep "mutate" 2 new "address" pos)
                      (new == Address)
    reportErrorUnless (ReasonForeignArgRep "mutate" 3 offset "integer" pos)
                      (integerTypeRep offset)
    reportErrorUnless (ReasonForeignArgRep "mutate" 4 destr "boolean" pos)
                      (integerTypeRep destr)
    reportErrorUnless (ReasonForeignArgRep "mutate" 5 sz "integer" pos)
                      (integerTypeRep sz)
    reportErrorUnless (ReasonForeignArgRep "mutate" 6 start "integer" pos)
                      (integerTypeRep start)
checkLPVMArgs "mutate" _ args stmt pos =
    typeError (ReasonForeignArity "mutate" (length args) 7 pos)
-- XXX do we still need a cast instruction?
checkLPVMArgs "cast" _ [old,new] stmt pos = return ()
checkLPVMArgs "cast" _ [] stmt pos = return ()
checkLPVMArgs "cast" _ args stmt pos =
    typeError (ReasonForeignArity "cast" (length args) 2 pos)
checkLPVMArgs name _ args stmt pos =
    typeError (ReasonBadForeign "lpvm" name pos)

----------------------------------------------------------------
--                    Check that everything is typed
----------------------------------------------------------------

-- |Make sure all args and params in the specified proc def are typed.
checkProcDefFullytyped :: ProcDef -> Compiler ()
checkProcDefFullytyped def = do
    let name = procName def
    let pos = procPos def
    zipWithM_ (placedApplyM . checkParamTyped name)
       [1..] (procProtoParams $ procProto def)
    mapM_ (placedApply (checkStmtTyped name pos)) $
          procDefSrc $ procImpln def


procDefSrc :: ProcImpln -> [Placed Stmt]
procDefSrc (ProcDefSrc def) = def
procDefSrc ProcDefPrim{} = shouldnt "procDefSrc applied to ProcDefPrim"


checkParamTyped :: ProcName -> Int -> Param -> OptPos -> Compiler ()
checkParamTyped name num Param{paramName=pName,paramType=ty,paramFlow=flow} pos = do
    when (AnyType == ty) $
        reportUntyped name pos (" parameter " ++ show num)


checkStmtTyped :: ProcName -> OptPos -> Stmt -> OptPos -> Compiler ()
checkStmtTyped name pos (ProcCall (First pmod pname pid) _ _ args) ppos = do
    when (isNothing pid || List.null pmod) $
         shouldnt $ "Call to " ++ pname ++ showOptPos ppos ++
                  " left unresolved"
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped name pos (ProcCall (Higher fn) _ _ args) ppos = do
    mapM_ (checkArgTyped name pos (show $ content fn) ppos) $
          zip [0..] $ List.map content $ fn:args
checkStmtTyped name pos (ForeignCall _ pname _ args) ppos =
    mapM_ (checkArgTyped name pos pname ppos) $
          zip [1..] $ List.map content args
checkStmtTyped _ _ (TestBool _) _ = return ()
checkStmtTyped name pos (And stmts) _ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos stmt@(Or stmts _ _) _ppos = do
    -- exit vars are Nothing when both disjuncts are infinite loops, so don't report this:
    -- when (isNothing exitVars) $
    --      shouldnt $ "exit vars of disjunction undetermined: " ++ showStmt 4 stmt
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (Not stmt) _ppos =
    placedApply (checkStmtTyped name pos) stmt
checkStmtTyped name pos
               stmt@(Cond tst thenstmts elsestmts _ _ _) _ppos = do
    -- exit vars are Nothing when both branches are infinite loops, so don't report this:
    -- when (isNothing exitVars) $
    --      shouldnt $ "exit vars of conditional undetermined: " ++ showStmt 4 stmt
    placedApply (checkStmtTyped name pos) tst
    mapM_ (placedApply (checkStmtTyped name pos)) thenstmts
    mapM_ (placedApply (checkStmtTyped name pos)) elsestmts
checkStmtTyped name pos stmt@(Loop stmts _ _) _ppos = do
    -- exit vars are Nothing for infinite loops, so don't report this:
    -- when (isNothing exitVars) $
    --      shouldnt $ "exit vars of loop undetermined: " ++ showStmt 4 stmt
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos (UseResources _ _ stmts) _ppos =
    mapM_ (placedApply (checkStmtTyped name pos)) stmts
checkStmtTyped name pos For{} ppos =
    shouldnt "For statement left by flattening"
checkStmtTyped name pos Case{} ppos =
    shouldnt "Case statement left by flattening"
checkStmtTyped _ _ Nop _ = return ()
checkStmtTyped _ _ Fail _ = return ()
checkStmtTyped _ _ Break _ = return ()
checkStmtTyped _ _ Next _ = return ()


checkArgTyped :: ProcName -> OptPos -> ProcName -> OptPos ->
                 (Int, Exp) -> Compiler ()
checkArgTyped callerName callerPos calleeName callPos (n,arg) =
    checkExpTyped callerName callerPos
                      ("in call to " ++ calleeName ++
                       showOptPos callPos ++
                       ", arg " ++ show n) arg


checkExpTyped :: ProcName -> OptPos -> String -> Exp ->
                 Compiler ()
checkExpTyped callerName callerPos msg (Typed expr ty _)
    | ty /= AnyType = return ()
checkExpTyped callerName callerPos msg _ =
    reportUntyped callerName callerPos msg


reportUntyped :: ProcName -> OptPos -> String -> Compiler ()
reportUntyped procname pos msg =
    liftIO $ putStrLn $ "Internal error: In " ++ procname ++
      showOptPos pos ++ ", " ++ msg ++ " left untyped"


--------------------------------------------------------------------------------
--                               Logging
--------------------------------------------------------------------------------

-- |Log a message, if we are logging type checker activity.
logTypes :: String -> Compiler ()
logTypes = logMsg Types

-- |Log a message, if we are logging type checker activity; used in Typed monad.
logTyped :: String -> Typed ()
logTyped = lift . logTypes


-- |Log a message including the current typing.
logTyping :: String -> Typed ()
logTyping prefix = do
    typing <- get
    logTyped $ prefix ++ show typing
