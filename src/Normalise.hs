--  File     : Normalise.hs
--  Author   : Peter Schachte
--  Purpose  : Convert parse tree into an AST
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

-- |Support for normalising wybe code as parsed to a simpler form
--  to make compiling easier.


module Normalise (normalise, normaliseItem, completeNormalisation) where

import AST
import Config (wordSize, wordSizeBytes, availableTagBits,
               tagMask, smallestAllocatedAddress, currentModuleAlias)
import Control.Monad
import Control.Monad.State (gets)
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.Extra (concatMapM)
import Data.List as List
import Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Data.Bits
import Data.Graph
import Data.Tuple.HT
import Data.Tuple.Select
import Flatten (flattenProcBody)
import Options (LogSelection(Normalise))
import Snippets
import Util
import Distribution.Parsec.FieldLineStream (fieldLineStreamEnd)
import UnivSet (UnivSet(FiniteSet, UniversalSet))
import Data.Function (on)
import Data.List.Extra (groupSort)

-- |Normalise a list of file items, storing the results in the current module.
normalise :: [Item] -> Compiler ()
normalise items = do
    mapM_ normaliseItem items
    -- import stdlib unless no_standard_library pragma is specified
    useStdLib <- getModuleImplementationField (Set.notMember NoStd . modPragmas)
    when useStdLib
      $ addImport ["wybe"] (ImportSpec (FiniteSet Set.empty) UniversalSet )


----------------------------------------------------------------
-- Normalising a module item
--
-- This only handles what can be handled without having loaded dependencies.
----------------------------------------------------------------

-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) mods
              (TypeRepresentation rep) items pos) = do
    let items' = RepresentationDecl params mods rep pos : items
    unless (List.null params)
      $ errmsg pos "types defined by representation cannot have type parameters"
    normaliseSubmodule name vis pos items'
normaliseItem (TypeDecl vis (TypeProto name params) mods
              (TypeCtors ctorVis ctors) items pos) = do
    let items' = ConstructorDecl ctorVis params mods ctors pos : items
    normaliseSubmodule name vis pos items'
normaliseItem (ModuleDecl vis name items pos) =
    normaliseSubmodule name vis pos items
normaliseItem (RepresentationDecl params mods rep pos) = do
    updateTypeModifiers mods
    addParameters (RealTypeVar <$> params) pos
    addTypeRep rep pos
normaliseItem (ConstructorDecl vis params mods ctors pos) = do
    updateTypeModifiers mods
    addParameters (RealTypeVar <$> params) pos
    case vis of
        Public -> mapM_ (addConstructor Public . snd) ctors
        Private -> mapM_ (uncurry addConstructor) ctors
normaliseItem (ImportMods vis modspecs pos) =
    mapM_ (\spec -> addImport spec (importSpec Nothing vis)) modspecs
normaliseItem (ImportItems vis modspec imports pos) =
    addImport modspec (importSpec (Just imports) vis)
normaliseItem (ImportForeign files _) =
    mapM_ addForeignImport files
normaliseItem (ImportForeignLib files _) =
    mapM_ addForeignLib files
normaliseItem (ResourceDecl vis name typ init pos) = do
  addSimpleResource name (SimpleResource typ init pos) vis
  case init of
    Nothing  -> return ()
    Just val -> normaliseItem (StmtDecl (ProcCall (regularProc "=") Det False
                                         [varSet name `maybePlace` pos, val]) pos)
normaliseItem (FuncDecl vis mods (ProcProto name params resources) resulttype
    (Placed (Where body (Placed (Var var ParamOut rflow) _)) _) pos) =
    -- Handle special reverse mode case of def foo(...) = var where ....
    normaliseItem
        (ProcDecl vis mods
            (ProcProto name (params ++ [Param var resulttype ParamIn rflow `maybePlace` pos])
                       resources)
             body
        pos)
normaliseItem (FuncDecl vis mods (ProcProto name params resources)
                        resulttype result pos) =
    normaliseItem
        (ProcDecl vis mods
            (ProcProto name (params ++ [Param outputVariableName resulttype
                                        ParamOut Ordinary `maybePlace` pos])
                       resources)
             [maybePlace (ForeignCall "llvm" "move" []
                 [result, varSet outputVariableName `maybePlace` pos])
              pos]
        pos)
normaliseItem item@ProcDecl{} = do
    logNormalise $ "Recording proc without flattening:" ++ show item
    addProc 0 item
normaliseItem (StmtDecl stmt pos) = do
    logNormalise $ "Normalising statement decl " ++ show stmt
    updateModule (\s -> s { stmtDecls = maybePlace stmt pos : stmtDecls s})
normaliseItem (PragmaDecl prag) =
    addPragma prag


-- |Normalise a nested submodule containing the specified items.
normaliseSubmodule :: Ident -> Visibility -> OptPos -> [Item] -> Compiler ()
normaliseSubmodule name vis pos items = do
    parentOrigin <- getOrigin
    parentModSpec <- getModuleSpec
    let subModSpec = parentModSpec ++ [name]
    logNormalise $ "Normalising submodule " ++ showModSpec subModSpec ++ " {"
    mapM_ (logNormalise . ("  "++) . show) items
    logNormalise "}"
    addImport subModSpec (importSpec Nothing vis)
    -- Add the submodule to the submodule list of the implementation
    updateImplementation $ updateModSubmods (Map.insert name subModSpec)
    alreadyExists <- isJust <$> getLoadingModule subModSpec
    if alreadyExists
      then reenterModule subModSpec
      else enterModule parentOrigin subModSpec (Just parentModSpec)
    -- submodule always imports parent module
    updateImplementation $ \i -> i { modNestedIn = Just parentModSpec }
    addImport parentModSpec (importSpec Nothing Private)
    normalise items
    if alreadyExists
    then reexitModule
    else exitModule
    logNormalise $ "Finished normalising submodule " ++ showModSpec subModSpec
    return ()



----------------------------------------------------------------
--                         Completing Normalisation
--
-- This only handles what cannot be handled until dependencies are loaded.
----------------------------------------------------------------

-- |Do whatever part of normalisation cannot be done until dependencies
--  have been loaded.  Currently that means laying out types, generating
--  constructors, deconstructors, accessors, mutators, and auxilliary
--  procs, and generation of main proc for
--  the module, which needs to know what resources are available.
--  Finally, we flatten the body of each proc in the module scc.

completeNormalisation :: [ModSpec] -> Compiler ()
completeNormalisation modSCC = do
    logNormalise $ "Completing normalisation of modules " ++ showModSpecs modSCC
    completeTypeNormalisation modSCC
    mapM_ (normaliseModMain `inModule`) modSCC
    mapM_ (transformModuleProcs flattenProcBody) modSCC


-- | Layout the types on the specified module list, which comprise a strongly
--   connected component in the *module* dependency graph.  Some of the
--   specified modules will not be types, and are ignored here.  Some that are
--   types will be specified by representation rather than by constructors; for
--   these, we just accept the specified representation, so there is nothing
--   more to do here.  The types specified as a list of constructors can only be
--   defined in terms of types in the specified module list or in modules that
--   have already been layed out.  Any mutually recursively defined types must
--   all be listed in the same module dependency SCC.  Also, all (mutually)
--   recursively defined types may be unbounded in size, and therefore must be
--   represented as pointers.
--
--   Thus we handle struct layout by first finding the SCCs in the *type*
--   dependency graph limited to the current *module* depenency SCC, and
--   handling the SCCs in topological order.  For recursive SCCs, we first
--   automatically assign a pointer representation for each type.  Then we lay
--   out each type in the type dependency SCC, and finally generate
--   constructors, deconstructors, accessors, mutators, and auxiliary
--   procedures.  This ensures we can do the layout in a single pass, and can
--   safely look up the representation of each type referred in each constructor
--   as we process it.
completeTypeNormalisation :: [ModSpec] -> Compiler ()
completeTypeNormalisation mods = do
    mods' <- filterM (getSpecModule "completeTypeNormalisation"
                      (modIsType &&& isNothing . modTypeRep)) mods
    typeSCCs <- modSCCTypeDeps mods'
    logNormalise $ "Ordered type dependency SCCs: " ++ show typeSCCs
    mapM_ completeTypeSCC typeSCCs


-- |An algebraic type definition, listing all the constructors.
data TypeDef = TypeDef {
    typeDefParams :: [TypeVarName],           -- the type parameters
    typeDefMembers :: [(Visibility, Placed ProcProto)]
                                              -- high level representation, 
                                              -- with visibilities
    } deriving (Eq, Show)


-- -- |How to show a type definition.
-- instance Show TypeDef where
--   show (TypeDef params members _ pos items) =
--     bracketList "(" "," ")" params
--     ++ " { "
--     ++ intercalate " | " (show <$> members)
--     ++ " "
--     ++ intercalate "\n  " (show <$> items)
--     ++ " } "
--     ++ showOptPos pos


-- | Return a topologically sorted list of type dependency SCCs in the
--   specified modules.
modSCCTypeDeps :: [ModSpec] -> Compiler [SCC (ModSpec,TypeDef)]
modSCCTypeDeps sccMods =
    let modSet = Set.fromList sccMods
    in stronglyConnComp <$> mapM (modTypeDeps modSet `inModule`) sccMods


-- | Return a list of type dependencies on types defined in the specified
-- modules that are defined in the current module
modTypeDeps :: Set ModSpec -> Compiler ((ModSpec,TypeDef), ModSpec, [ModSpec])
modTypeDeps modSet = do
    tyMod <- getModule modSpec
    tyParams <- getModule modParams
    ctorsVis <- reverse . trustFromJust "modTypeDeps"
               <$> getModuleImplementationField modConstructors
    ctors <- mapM (placedApply resolveCtorTypes . snd) ctorsVis
    let deps = List.filter (`Set.member` modSet)
               $ concatMap
                 (catMaybes . (typeModule . paramType . content <$>)
                  . procProtoParams . content)
                 ctors
    return ((tyMod, TypeDef tyParams ctorsVis), tyMod, deps)


-- | Resolve constructor argument types.
resolveCtorTypes :: ProcProto -> OptPos -> Compiler (Placed ProcProto)
resolveCtorTypes proto pos = do
    params <- mapM (placedApplyM resolveParamType) $ procProtoParams proto
    return $ maybePlace (proto { procProtoParams = params }) pos


-- | Resolve the type of a parameter
resolveParamType :: Param -> OptPos -> Compiler (Placed Param)
resolveParamType param@Param{paramType=ty} pos = do
    ty' <- lookupType "constructor parameter" pos ty
    return $ param { paramType = ty' } `maybePlace` pos



-- | Layout the types defined in the specified type dependency SCC, and then
--   generate constructors, deconstructors, accessors, mutators, and
--   auxiliary procedures.
completeTypeSCC :: SCC (ModSpec,TypeDef) -> Compiler ()
completeTypeSCC (AcyclicSCC (mod,typedef)) = do
    logNormalise $ "Completing non-recursive type "
                   ++ showModSpec mod ++ " = " ++ show typedef
    completeType mod typedef
completeTypeSCC (CyclicSCC modTypeDefs) = do
    logNormalise $ "Completing recursive type(s):" ++ show modTypeDefs
    mapM_ (\(mod,typedef) ->
             logNormalise $ "   " ++ showModSpec mod ++ " = " ++ show typedef)
          modTypeDefs
    -- First set representations to addresses, then layout types
    mapM_ ((setTypeRep Address `inModule`) . fst) modTypeDefs
    mapM_ (uncurry completeType) modTypeDefs


-- | Information about a non-constant constructor
data CtorInfo = CtorInfo {
           ctorInfoName   :: ProcName,        -- ^ this constructor's name
           ctorInfoParams :: [CtorParamInfo], -- ^ params of this ctor
           ctorInfoVis    :: Visibility,      -- ^ Vsibility of ctor
           ctorInfoPos    :: OptPos,          -- ^ file position of ctor
           ctorInfoTag    :: Int,             -- ^ this constructor's tag
           ctorInfoBits   :: Int              -- ^ min number of bits needed
     } deriving (Show)


data CtorParamInfo = CtorParamInfo {
    paramInfoParam :: Placed Param,
    paramInfoAnon :: Bool,
    paramInfoTypeRep :: TypeRepresentation,
    paramInfoBitSize :: Int
} deriving (Show)


-- | Layout the specified type, and then generate constructors,
--   deconstructors, accessors, mutators, and auxiliary procedures.
--   When called, all referred types have established representations.
--
--   Our type layout strategy:
--     * Let numConsts = the number of constant constructors
--     * Let numNonConsts = the number of non-constant constructors
--     * Let tagLimit = wordSizeBytes - 1
--     * Let tagBits = log 2 numNonConsts
--     * If numNonConsts > wordSizeBytes:
--           decrement tagLimit
--           tagBits = log 2 wordSizeBytes
--     * For each non-constant constructor:
--         * let ctorSize = total of sizes in bits of the members
--         * If the ctor number > tagLimit: add log 2 numNonConsts
--     * If numNonConsts == 0 && numConsts == 0: error!
--     * elif numNonConsts > 0 && numConsts > smallestAllocatedAddress:  nyi!
--     * elif numNonConsts == 0: rep = integer with ceil(log 2 numConsts) bits
--     * elif numConsts == 0 && max ctorSize <= wordSizeBytes:
--          rep = integer with max ctorSize bits
--     * else: rep = integer with wordSizeBytes bits
completeType :: ModSpec -> TypeDef -> Compiler ()
completeType modspec (TypeDef params []) =
    shouldnt $ "completeType with no constructors: " ++ show modspec
completeType modspec (TypeDef params ctors) = do
    logNormalise $ "Completing type " ++ showModSpec modspec
    reenterModule modspec

    let (constCtors,nonConstCtors) =
            List.partition (List.null . procProtoParams . content . snd) ctors
    let numConsts = length constCtors
    let numNonConsts = length nonConstCtors
    let (tagBits,tagLimit)
         | numNonConsts > wordSizeBytes
         = -- must set aside one tag to indicate secondary tag
           (availableTagBits, wordSizeBytes - 2)
         | numNonConsts == 0
         = (0, 0)
         | otherwise
         = (ceiling $ logBase 2 (fromIntegral numNonConsts), wordSizeBytes - 1)
    logNormalise $ "Complete " ++ showModSpec modspec
                   ++ " with " ++ show tagBits ++ " tag bits and "
                   ++ show tagLimit ++ " tag limit"

    -- XXX if numNonConsts == 0, then we could handle more consts.
    when (numConsts >= fromIntegral smallestAllocatedAddress)
      $ nyi $ "Type '" ++ show modspec ++ "' has too many constant constructors"

    let typespec = TypeSpec [] currentModuleAlias $ List.map TypeVariable params

    let constItems = concatMap (constCtorItems typespec) $ zip constCtors [0..]

    (nonConstCtors',infos) <- unzip <$> zipWithM nonConstCtorInfo nonConstCtors [0..]
    isUnique <- tmUniqueness . typeModifiers <$> getModuleInterface
    (reps,nonconstItemsList,gettersSetters) <-
         unzip3 <$> mapM
         (nonConstCtorItems isUnique typespec numConsts numNonConsts
          tagBits tagLimit)
         infos

    let rep = typeRepresentation reps numConsts
    setTypeRep rep
    logNormalise $ "Representation of type " ++ showModSpec modspec
                   ++ " is " ++ show rep

    getSetItems <- concat <$>
        mapM (uncurry $ getterSetterItems numConsts numNonConsts typespec)
            (groupSort (concat gettersSetters))

    extraItems <-
        if isUnique
            then return [] -- No implicit procs for unique types
            else implicitItems Nothing typespec constCtors nonConstCtors' rep

    normalise $ constItems ++ concat nonconstItemsList ++ extraItems ++ getSetItems

    reexitModule


-- | Analyse the representation of a single constructor, determining the
--   representation of its members, its total size in bits (assuming it is
--   *not* boxed, so each member takes the minimum number of bits), and its
--   total size in bytes (assuming it is boxed, so each member takes an
--   integral number of bytes).

nonConstCtorInfo :: (Visibility, Placed ProcProto) -> Int -> Compiler (Placed ProcProto, CtorInfo)
nonConstCtorInfo (vis, placedProto) tag = do
    logNormalise $ "Analysing non-constant ctor "
                   ++ show tag ++ ": " ++ show placedProto
    let (proto,pos) = unPlace placedProto
    unless (Set.null $ procProtoResources proto)
      $ shouldnt $ "Constructor with resources: " ++ show placedProto
    let name   = procProtoName proto
    let params = procProtoParams proto
    let anonParams = zipWith (placedApply . fixAnonFieldName name) [1..] params
    let (params', anons) = unzip anonParams
    logNormalise $ "With types resolved: " ++ show placedProto

    reps <- mapM (placedApply resolveParamType >=> lookupTypeRepresentation . paramType . content) params'
    let reps' = catMaybes reps
    logNormalise $ "Member representations: " ++ intercalate ", " (show <$> reps')

    let bitSizes = typeRepSize <$> reps'
    let bitSize  = sum bitSizes
    let paramInfos = zipWith4 CtorParamInfo params' anons reps' bitSizes
    return (maybePlace proto{procProtoParams=params'} pos,
            CtorInfo name paramInfos vis pos tag bitSize)


-- | Replace a field's name with an appropriate replacement if it is anonymous
-- (empty string). Bool indicates if the name was replaced
fixAnonFieldName :: ProcName -> Int -> Param -> OptPos -> (Placed Param, Bool)
fixAnonFieldName name i param@Param{paramName=""} pos
  = (param{paramName = specialName2 name $ show i} `maybePlace` pos, True)
fixAnonFieldName _ _ param pos = (param `maybePlace` pos, False)


-- | Determine the appropriate representation for a type based on a list of
-- the representations of all the non-constant constructors and the number
-- of constant constructors.
typeRepresentation :: [TypeRepresentation] -> Int -> TypeRepresentation
typeRepresentation [] numConsts =
    Bits $ ceiling $ logBase 2 $ fromIntegral numConsts
typeRepresentation [rep] 0      = rep
typeRepresentation _ _          = Address


----------------------------------------------------------------
-- Generating top-level code for the current module

normaliseModMain :: Compiler ()
normaliseModMain = do
    stmts <- getModule stmtDecls
    modSpec <- getModuleSpec
    logNormalise $ "Completing main normalisation of module "
                   ++ showModSpec modSpec
    resources <- initResources
    let initBody = List.reverse stmts
    logNormalise $ "Top-level statements = " ++ show initBody
    unless (List.null stmts)
      $ normaliseItem $ ProcDecl Public (setImpurity Semipure defaultProcModifiers)
                        (ProcProto "" [] resources) initBody Nothing


-- |The resources available at the top level of this module, plus the
-- initialisations to be performed before executing any code that uses this
-- module.
initResources :: Compiler (Set ResourceFlowSpec)
initResources = do
    thisMod <- getModule modSpec
    mods <- getModuleImplementationField (Map.keys . modImports)
    mods' <- (mods ++) . concat <$> mapM descendentModules mods
    logNormalise $ "in initResources, mods = " ++ showModSpecs mods'
    importedMods <- catMaybes <$> mapM getLoadingModule mods'
    let importImplns = catMaybes (modImplementation <$> importedMods)
    initialisedImports <- Set.toList . Set.unions . (Map.keysSet <$>)
                          <$> mapM (initialisedResources `inModule`) mods'
    initialisedLocal <- Set.toList . Map.keysSet <$> initialisedResources
    -- Direct tie-in to command_line library module:  for the command_line
    -- module, or any module that imports it, we add argc and argv as resources.
    -- This is necessary because argc and argv are effectively initialised by
    -- the fact that they're automatically generated as arguments to the
    -- top-level main, but we can't declare them with resource initialisations,
    -- because that would overwrite them.
    let cmdlineResources =
            if cmdLineModSpec == thisMod
            then let cmdline = ResourceSpec cmdLineModSpec 
                 in [ResourceFlowSpec (cmdline "argc") ParamInOut
                    ,ResourceFlowSpec (cmdline "argv") ParamInOut]
            else []
    let resources = cmdlineResources
                    ++ ((`ResourceFlowSpec` ParamInOut) <$> initialisedImports)
                    ++ ((`ResourceFlowSpec` ParamOut) <$> initialisedLocal)
    -- let inits = [ForeignCall "llvm" "move" []
    --                 [maybePlace ((content initExp) `withType` resType)
    --                     (place initExp)
    --                 , varSet (resourceName resSpec) `maybePlace` pos] 
    --                  `maybePlace` pos
    --             | (resSpec, resImpln) <- initialisedLocal
    --             , let initExp = trustFromJust "initResources"
    --                             $ resourceInit resImpln
    --             , let resType = resourceType resImpln]
    logNormalise $ "In initResources, resources = " ++ show resources
    -- logNormalise $ "In initResources, initialisations =" ++ showBody 4 inits
    return (Set.fromList resources)



----------------------------------------------------------------
--                Generating code for type declarations
----------------------------------------------------------------

-- Data used to create a getter and setter for a field
data GetterSetterInfo = GetterSetterInfo {
    gsPos :: OptPos,
    gsVisibility :: Visibility,
    gsTypeSpec :: TypeSpec,
    gsTagCheck :: Placed Stmt,
    gsGetter :: [Placed Stmt],
    gsSetter :: [Placed Stmt]
} deriving (Show, Eq, Ord)


-- Data about a boxed field
data FieldInfo = FieldInfo {
    fldName     :: VarName,
    fldPos      :: OptPos,
    fldAnon     :: Bool,
    fldTypeSpec :: TypeSpec,
    fldRep      :: TypeRepresentation,
    fldOffset   :: Int,
    fldSize     :: Int
} deriving (Show)




-- |All items needed to implement a const contructor for the specified type.
constCtorItems :: TypeSpec -> ((Visibility, Placed ProcProto),Integer) -> [Item]
constCtorItems typeSpec ((vis, placedProto), num) =
    let (proto,pos) = unPlace placedProto
        constName = procProtoName proto
    in [ProcDecl vis (inlineModifiers (ConstructorProc constName) Det)
        (ProcProto constName
            [Param outputVariableName typeSpec ParamOut Ordinary `maybePlace` pos] Set.empty)
        [lpvmCastToVar (castTo (iVal num) typeSpec) outputVariableName] pos
       ]


-- |All items needed to implement a non-const contructor for the specified type.
nonConstCtorItems :: Bool -> TypeSpec -> Int -> Int -> Int -> Int
                  -> CtorInfo
                  -> Compiler (TypeRepresentation, [Item], [(VarName, GetterSetterInfo)])
nonConstCtorItems uniq typeSpec numConsts numNonConsts tagBits tagLimit
                  info@(CtorInfo ctorName paramInfos vis pos tag bits) = do
    -- If we're unboxed and there are const ctors, then we need an extra
    -- bit to make sure the unboxed value is > than any const value
    let nonConstsize = bits + tagBits
    let (size,nonConstBit)
          = if numConsts == 0
            then (nonConstsize,Nothing)
            else let constSize = ceiling $ logBase 2 $ fromIntegral numConsts
                     size' = 1 + max nonConstsize constSize
                 in (size', Just $ size' - 1)
    logNormalise $ "Making constructor items for type " ++ show typeSpec
                   ++ ": " ++ show info
    logNormalise $ show bits ++ " data bit(s)"
    logNormalise $ show tagBits ++ " tag bit(s)"
    logNormalise $ "nonConst bit = " ++ show nonConstBit

    if size <= wordSize && tag <= tagLimit
      then do -- unboxed representation
        let fields =
                fst
                $ List.foldr
                (\(CtorParamInfo param anon rep sz) (flds, shift) ->
                    let (param', pPos) = unPlace param
                        Param pName pType _ _ = param'
                    in (FieldInfo pName pPos anon pType rep shift sz : flds,
                        shift + sz))
                ([],tagBits)
                paramInfos
        return (Bits size,
                unboxedConstructorItems vis ctorName typeSpec tag nonConstBit
                fields pos
                ++ unboxedDeconstructorItems vis uniq ctorName typeSpec
                    numConsts numNonConsts tag tagBits pos fields,
                concatMap
                    (unboxedGetterSetterStmts vis typeSpec numConsts numNonConsts
                        tag tagBits)
                    fields
                )
      else do -- boxed representation
        let (fields,size) = layoutRecord paramInfos tag tagLimit
        logNormalise $ "Laid out structure size " ++ show size
            ++ ": " ++ show fields
        let ptrCount = length $ List.filter ((==Address) . paramInfoTypeRep) paramInfos
        logNormalise $ "Structure contains " ++ show ptrCount ++ " pointers, "
                        ++ show numConsts ++ " const constructors, "
                        ++ show numNonConsts ++ " non-const constructors"
        let params = paramInfoParam <$> paramInfos
        return (Address,
                constructorItems vis ctorName typeSpec params fields
                    size tag tagLimit pos
                ++ deconstructorItems uniq vis ctorName typeSpec params numConsts
                        numNonConsts tag tagBits tagLimit pos fields size,
                concatMap
                    (boxedGetterSetterStmts vis typeSpec numConsts numNonConsts
                    ptrCount size tag tagBits tagLimit)
                    fields
                )



----------------------------------------------------------------
--                Generating code for boxed types (records)
----------------------------------------------------------------

-- | Lay out a record in memory, returning the size of the record and a
-- list of the fields and offsets of the structure.  This ensures that
-- values are aligned properly for their size (eg, word sized values are
-- aligned on word boundaries).
layoutRecord :: [CtorParamInfo] -> Int -> Int -> ([FieldInfo], Int)
layoutRecord paramInfos tag tagLimit =
    let sizes = (2^) <$> [0..floor $ logBase 2 $ fromIntegral wordSizeBytes]
        fields = List.map
                (\(CtorParamInfo param anon rep sz) ->
                    let byteSize = (sz + 7) `div` 8
                        wordSize = (byteSize + wordSizeBytes - 1)
                                    `div` wordSizeBytes * wordSizeBytes
                        alignment =
                            fromMaybe wordSizeBytes $ find (>=byteSize) sizes
                        (p, pos) = unPlace param
                    in ((paramName p, pos, anon,paramType p,rep,byteSize),
                        alignment))
                paramInfos
        -- put fields in order of increasing alignment
        ordFields = sortOn snd fields
        -- add secondary tag if necessary
        initOffset = if tag > tagLimit then wordSizeBytes else 0
        offsets = List.foldl align ([],initOffset) ordFields
    in mapFst reverse offsets
    where align (aligned,offset) ((name,pos,anon,ty,rep,sz),alignment) =
            let alignedOffset = offset + (-offset) `mod` alignment
            in (FieldInfo name pos anon ty rep alignedOffset sz:aligned,
                alignedOffset + sz)



-- |Generate constructor code for a non-const constructor
constructorItems :: Visibility -> ProcName -> TypeSpec -> [Placed Param]
                 -> [FieldInfo]
                 -> Int -> Int -> Int -> OptPos -> [Item]
constructorItems vis ctorName typeSpec params fields size tag tagLimit pos =
    [ProcDecl vis (inlineModifiers (ConstructorProc ctorName) Det)
        (ProcProto ctorName
            ((placedApply (\p -> maybePlace p {paramFlow=ParamIn, paramFlowType=Ordinary}) <$> params)
             ++ [Param outputVariableName typeSpec ParamOut Ordinary `maybePlace` pos])
            Set.empty)
        -- Code to allocate memory for the value
        ([maybePlace (ForeignCall "lpvm" "alloc" []
          [Unplaced $ iVal size,
           varSetTyped recName typeSpec `maybePlace` pos]) pos]
         ++
         -- fill in the secondary tag, if necessary
         ([maybePlace (ForeignCall "lpvm" "mutate" []
            [varGetTyped recName typeSpec `maybePlace` pos,
              varSetTyped recName typeSpec `maybePlace` pos,
              Unplaced $ iVal 0,
              Unplaced $ iVal 1,
              Unplaced $ iVal size,
              Unplaced $ iVal 0,
              Unplaced $ iVal tag]) pos
          | tag > tagLimit])
         ++
         -- Code to fill all the fields
         List.map
          (\(FieldInfo var pPos _ ty _ offset _) ->
               maybePlace (ForeignCall "lpvm" "mutate" []
                [varGetTyped recName typeSpec `maybePlace` pos,
                  varSetTyped recName typeSpec `maybePlace` pos,
                  Unplaced $ iVal offset,
                  Unplaced $ iVal 1,
                  Unplaced $ iVal size,
                  Unplaced $ iVal 0,
                  varGetTyped var ty `maybePlace` pPos]) pos)
          fields
         ++
         -- Finally, code to tag the reference
         [maybePlace (ForeignCall "llvm" "or" []
           [varGetTyped recName typeSpec `maybePlace` pos,
            Unplaced $ iVal (if tag > tagLimit then tagLimit+1 else tag),
            varSetTyped outputVariableName typeSpec `maybePlace` pos]) pos])
        pos]


-- |Generate deconstructor code for a non-const constructor
deconstructorItems :: Bool -> Visibility -> Ident -> TypeSpec -> [Placed Param]
                   -> Int -> Int -> Int -> Int -> Int -> OptPos
                   -> [FieldInfo] -> Int -> [Item]
deconstructorItems uniq vis ctorName typeSpec params numConsts numNonConsts tag
                   tagBits tagLimit pos fields size =
    let startOffset = (if tag > tagLimit then tagLimit+1 else tag)
        detism = deconstructorDetism numConsts numNonConsts
    in [ProcDecl vis (inlineModifiers (DeconstructorProc ctorName) detism)
        (ProcProto ctorName
         ((contentApply (\p -> p {paramFlow=ParamOut, paramFlowType=Ordinary}) <$> params)
          ++ [Param outputVariableName typeSpec ParamIn Ordinary `maybePlace` pos])
         Set.empty)
        -- Code to check we have the right constructor
        (tagCheck pos numConsts numNonConsts tag tagBits tagLimit
            (Just size) outputVariableName
         -- Code to fetch all the fields
         : List.map (\(FieldInfo var pPos _ ty _ aligned _) ->
                        maybePlace (ForeignCall "lpvm" "access"
                            ["unique" | uniq]
                              [varGetTyped outputVariableName typeSpec `maybePlace` pos,
                               Unplaced $ iVal (aligned - startOffset),
                               Unplaced $ iVal size,
                               Unplaced $ iVal startOffset,
                               varSetTyped var ty `maybePlace` pPos])
                            pos)
            fields)
        pos]


-- |Generate the needed Test statements to check that the tag of the value
--  of the specified variable matches the specified tag.  If not checking
--  is necessary, just generate a Nop, rather than a true test.
tagCheck :: OptPos -> Int -> Int -> Int -> Int -> Int -> Maybe Int -> Ident -> Placed Stmt
tagCheck pos numConsts numNonConsts tag tagBits tagLimit size varName =
    let startOffset = (if tag > tagLimit then tagLimit+1 else tag) in
    -- If there are any constant constructors, be sure it's not one of them
    let tests =
          (case numConsts of
               0 -> []
               _ -> [comparison "icmp_uge"
                     (intCast $ varGet varName)
                     (intCast $ iVal numConsts)]
           ++
           -- If there is more than one non-const constructors, check that
           -- it's the right one
           (case numNonConsts of
               1 -> []  -- Nothing to do if it's the only non-const constructor
               _ -> [comparison "icmp_eq"
                     (intCast $ ForeignFn "llvm" "and" [] [Unplaced $ intCast $ varGet varName,
                         Unplaced $ iVal (2^tagBits-1) `withType` intType])
                     (intCast $ iVal (if tag > tagLimit
                                      then wordSizeBytes-1
                                      else tag))])
           ++
           -- If there's a secondary tag, check that, too.
           if tag > tagLimit
           then [maybePlace (ForeignCall "lpvm" "access" [] [varGet varName `maybePlace` pos,
                    Unplaced $ iVal (negate startOffset),
                    Unplaced $ iVal $ trustFromJust
                               "unboxed type shouldn't have a secondary tag" size,
                    Unplaced $ iVal startOffset,
                    Unplaced $ tagCast (varSet tagName)]) pos,
                 comparison "icmp_eq" (varGetTyped tagName tagType)
                                      (iVal tag `withType` tagType)]
           else [])

    in if List.null tests
       then Unplaced Nop
       else seqToStmt tests


-- | Produce a getter and a setter for one field of the specified type.
boxedGetterSetterStmts :: Visibility -> TypeSpec
                       -> Int -> Int -> Int -> Int -> Int -> Int -> Int
                       -> FieldInfo
                       -> [(VarName, GetterSetterInfo)]
boxedGetterSetterStmts _ _ _ _ _ _ _ _ _ FieldInfo{fldAnon=True} = []
boxedGetterSetterStmts vis rectype numConsts numNonConsts ptrCount size
        tag tagBits tagLimit (FieldInfo field pos _ fieldtype rep offset _) =
    let startOffset = if tag > tagLimit then tagLimit+1 else tag
        detism = deconstructorDetism numConsts numNonConsts
        -- Set the "noalias" flag when all other fields (exclude the one
        -- that is being changed) in this struct aren't [Address].
        -- This flag is used in [AliasAnalysis.hs]
        otherPtrCount = if rep == Address then ptrCount-1 else ptrCount
        flags = ["noalias" | otherPtrCount == 0]
    in [( field
        , GetterSetterInfo pos vis fieldtype
           (tagCheck pos numConsts numNonConsts tag tagBits tagLimit (Just size) recName)
           [maybePlace (ForeignCall "lpvm" "access" []
                [ varGetTyped recName rectype `maybePlace` pos
                , Unplaced $ iVal (offset - startOffset)
                , Unplaced $ iVal size
                , Unplaced $ iVal startOffset
                , varSetTyped outputVariableName fieldtype `maybePlace` pos]) pos]
           [maybePlace (ForeignCall "lpvm" "mutate" flags
                [ varGetTyped recName rectype `maybePlace` pos
                , varSetTyped recName rectype `maybePlace` pos
                , Unplaced $ iVal (offset - startOffset)
                , Unplaced $ iVal 0    -- May be changed to 1 by CTGC transform
                , Unplaced $ iVal size
                , Unplaced $ iVal startOffset
                , Unplaced $ varGet fieldName]) pos]
          )]


----------------------------------------------------------------
--                Generating code for unboxed types
----------------------------------------------------------------

-- |Generate constructor code for a non-const constructor
unboxedConstructorItems :: Visibility -> ProcName -> TypeSpec -> Int
                        -> Maybe Int -> [FieldInfo]
                        -> OptPos -> [Item]
unboxedConstructorItems vis ctorName typeSpec tag nonConstBit fields pos =
    let proto = ProcProto ctorName
                ([Param name paramType ParamIn Ordinary `maybePlace` pPos
                 | FieldInfo name pPos _ paramType _ _ _ <- fields]
                  ++ [Param outputVariableName typeSpec ParamOut Ordinary `maybePlace` pos])
                Set.empty
    in [ProcDecl vis (inlineModifiers (ConstructorProc ctorName) Det) proto
         -- Initialise result to 0
        ([ForeignCall "llvm" "move" []
          [castFromTo intType typeSpec (iVal 0) `maybePlace` pos,
           varSetTyped outputVariableName typeSpec `maybePlace` pos]
           `maybePlace` pos]
         ++
         -- Shift each field into place and or with the result
         List.concatMap
          (\(FieldInfo var pPos _ ty _ shift sz) ->
               [maybePlace (ForeignCall "llvm" "shl" []
                 [castFromTo ty typeSpec (varGet var) `maybePlace` pPos,
                  iVal shift `castTo` typeSpec `maybePlace` pos,
                  varSetTyped tmpName1 typeSpec `maybePlace` pos]) pos,
                maybePlace (ForeignCall "llvm" "or" []
                 [varGetTyped tmpName1 typeSpec `maybePlace` pos,
                  varGetTyped outputVariableName typeSpec `maybePlace` pos,
                  varSetTyped outputVariableName typeSpec `maybePlace` pos])
                pos])
          fields
         ++
         -- Or in the bit to ensure the value is greater than the greatest
         -- possible const value, if necessary
         (case nonConstBit of
            Nothing -> []
            Just shift ->
              [maybePlace (ForeignCall "llvm" "or" []
               [varGetTyped outputVariableName typeSpec `maybePlace` pos,
                Unplaced $ Typed (iVal (bit shift::Int)) typeSpec Nothing,
                varSetTyped outputVariableName typeSpec `maybePlace` pos])
               pos])
         -- Or in the tag value
          ++ [maybePlace (ForeignCall "llvm" "or" []
               [varGetTyped outputVariableName typeSpec `maybePlace` pos,
                Unplaced $ Typed (iVal tag) typeSpec Nothing,
                varSetTyped outputVariableName typeSpec `maybePlace` pos])
              pos]
        ) pos]


-- |Generate deconstructor code for a unboxed non-const constructor
unboxedDeconstructorItems :: Visibility -> Bool -> ProcName -> TypeSpec -> Int
                          -> Int -> Int -> Int -> OptPos
                          -> [FieldInfo] -> [Item]
unboxedDeconstructorItems vis uniq ctorName recType numConsts numNonConsts tag
                          tagBits pos fields =
    let detism = deconstructorDetism numConsts numNonConsts
    in [ProcDecl vis (inlineModifiers (DeconstructorProc ctorName) detism)
        (ProcProto ctorName
         (List.map (\(FieldInfo n pPos _ fieldType _ _ _) -> Param n fieldType ParamOut Ordinary `maybePlace` pPos)
          fields
          ++ [Param outputVariableName recType ParamIn Ordinary `maybePlace` pos])
         Set.empty)
         -- Code to check we have the right constructor
        (tagCheck pos numConsts numNonConsts tag tagBits (wordSizeBytes-1) Nothing
          outputVariableName
         -- Code to fetch all the fields
         : List.concatMap
            (\(FieldInfo n pPos _ fieldType _ shift sz) ->
               -- Code to access the selected field
               [maybePlace (ForeignCall "llvm" "lshr" ["unique" | uniq]
                 [varGetTyped outputVariableName recType `maybePlace` pos,
                  Typed (iVal shift) recType Nothing `maybePlace` pos,
                  varSetTyped tmpName1 recType `maybePlace` pos]) pPos,
                maybePlace (ForeignCall "llvm" "and" []
                 [varGetTyped tmpName1 recType `maybePlace` pos,
                  Typed (iVal $ (bit sz::Int) - 1) recType Nothing `maybePlace` pos,
                  varSetTyped tmpName2 recType `maybePlace` pos]) pos,
                maybePlace (ForeignCall "lpvm" "cast" []
                 [varGetTyped tmpName2 recType `maybePlace` pos,
                  varSetTyped n fieldType `maybePlace` pPos]) pPos
               ])
            fields)
        pos]


-- -- | Produce a getter and a setter for one field of the specified type.
unboxedGetterSetterStmts :: Visibility -> TypeSpec -> Int -> Int -> Int -> Int
                         -> FieldInfo
                         -> [(VarName, GetterSetterInfo)]
unboxedGetterSetterStmts _ _ _ _ _ _ FieldInfo{fldAnon=True} = []
unboxedGetterSetterStmts vis recType numConsts numNonConsts tag tagBits
                         (FieldInfo field pos _ fieldType _ shift sz) =
    let detism = deconstructorDetism numConsts numNonConsts
        fieldMask = (bit sz::Int) - 1
        shiftedHoleMask = complement $ fieldMask `shiftL` shift
    in [ ( field
         , GetterSetterInfo pos vis fieldType
           (tagCheck pos numConsts numNonConsts tag tagBits (wordSizeBytes-1) Nothing recName)
           [maybePlace (ForeignCall "llvm" "lshr" [] -- The getter:
                [varGetTyped recName recType `maybePlace` pos,
                    iVal shift `withType` recType `maybePlace` pos,
                    varSetTyped recName recType `maybePlace` pos]) pos,
                -- XXX Don't need to do this for the most significant field:
                maybePlace (ForeignCall "llvm" "and" []
                [varGetTyped recName recType `maybePlace` pos,
                    iVal fieldMask `withType` recType `maybePlace` pos,
                    varSetTyped fieldName recType `maybePlace` pos]) pos,
                maybePlace (ForeignCall "lpvm" "cast" []
                [varGetTyped fieldName recType `maybePlace` pos,
                    varSetTyped outputVariableName fieldType `maybePlace` pos]) pos
                ]
            [maybePlace (ForeignCall "llvm" "and" []
                [varGetTyped recName recType `maybePlace` pos,
                    iVal shiftedHoleMask `withType` recType `maybePlace` pos,
                    varSetTyped recName recType `maybePlace` pos]) pos,
                maybePlace (ForeignCall "llvm" "shl" []
                [castFromTo fieldType recType (varGet fieldName) `maybePlace` pos,
                    iVal shift `castTo` recType `maybePlace` pos,
                    varSetTyped tmpName1 recType `maybePlace` pos]) pos,
                maybePlace (ForeignCall "llvm" "or" []
                [varGetTyped tmpName1 recType `maybePlace` pos,
                    varGetTyped recName recType `maybePlace` pos,
                    varSetTyped recName recType `maybePlace` pos]) pos
                ]
            )]


deconstructorDetism :: Int -> Int -> Determinism
deconstructorDetism numConsts numNonConsts
    | numConsts + numNonConsts > 1 = SemiDet
    | otherwise                    = Det


-- | Construct Getter and Setter items for a given field over a series of constructors
getterSetterItems :: Int -> Int -> TypeSpec -> VarName -> [GetterSetterInfo]
                  -> Compiler [Item]
getterSetterItems _ _ _ _ [] = shouldnt "empty getterSetterItems"
getterSetterItems numConsts numNonConsts recType field infos = do
    let nCtors = length infos
        GetterSetterInfo _ fieldVis fieldType lastCheck lastGet lastSet = last infos
        pos = gsPos $ head infos
        detism = if nCtors == numNonConsts && numConsts == 0 then Det else SemiDet
        inline = if nCtors == 1 then Inline else MayInline
        body0 = if nCtors == numNonConsts && numConsts == 0
                then (lastGet, lastSet)
                else (lastCheck:lastGet, lastCheck:lastSet)
        ((getBody, setBody), visCheck, tyCheck) = List.foldr (
            \(GetterSetterInfo pos vis ty check get set) ((getBody, setBody), visCheck, tyCheck) ->
                ( ( [Cond check get getBody Nothing Nothing Nothing `maybePlace` pos]
                    , [Cond check set setBody Nothing Nothing Nothing `maybePlace` pos])
                , vis == fieldVis && visCheck
                , ty == fieldType && tyCheck)
         ) (body0, True, True) $ init infos
    unless visCheck $
        errmsg pos $
            "field '" ++ field ++ "' declared with multiple visibilities"
    unless tyCheck $
        errmsg pos $
            "field '" ++ field ++ "' declared with multiple types"
    return
        [-- The getter:
        ProcDecl fieldVis (setInline inline $ inlineModifiers (GetterProc field fieldType) detism)
        (ProcProto field [Param recName recType ParamIn Ordinary `maybePlace` pos,
                          Param outputVariableName fieldType ParamOut Ordinary `maybePlace` pos] Set.empty)
        getBody
        pos,
        -- The setter:
        ProcDecl fieldVis (setInline inline $ inlineModifiers (SetterProc field fieldType) detism)
        (ProcProto field [Param recName recType ParamInOut Ordinary `maybePlace` pos,
                          Param fieldName fieldType ParamIn Ordinary `maybePlace` pos] Set.empty)
        setBody
        pos]

----------------------------------------------------------------
--                     Generating implicit procs
--
-- Wybe automatically generates equality test procs if you don't write
-- your own definitions.  It should generate default implementations of
-- many more such procs.
--
----------------------------------------------------------------

implicitItems :: OptPos -> TypeSpec
              -> [(Visibility, Placed ProcProto)] -> [Placed ProcProto]
              -> TypeRepresentation -> Compiler [Item]
implicitItems pos typespec consts nonconsts rep
 | genericType typespec
   || any (higherOrderType . paramType . content)
          (concatMap (procProtoParams . content) nonconsts) = return []
 | otherwise = do
    eq <- implicitEquality pos typespec (snd <$> consts) nonconsts rep
    dis <- implicitDisequality pos typespec (snd <$> consts) nonconsts rep
    return $ eq ++ dis
    -- XXX add comparison, print, display, maybe prettyprint, and lots more


implicitEquality :: OptPos -> TypeSpec -> [Placed ProcProto] -> [Placed ProcProto]
                 -> TypeRepresentation -> Compiler [Item]
implicitEquality pos typespec consts nonconsts rep = do
    defs <- lookupProc "="
    -- XXX verify that it's an arity 2 test with two inputs of the right type
    if isJust defs
    then return [] -- don't generate if user-defined
    else do
      let eqProto = ProcProto "=" [Param leftName typespec ParamIn Ordinary `maybePlace` pos,
                                   Param rightName typespec ParamIn Ordinary `maybePlace` pos]
                    Set.empty
      let (body,inline) = equalityBody pos consts nonconsts rep
      return [ProcDecl Public (setInline inline
                               $ setDetism SemiDet defaultProcModifiers)
                   eqProto body Nothing]


implicitDisequality :: OptPos -> TypeSpec -> [Placed ProcProto] -> [Placed ProcProto]
                    -> TypeRepresentation -> Compiler [Item]
implicitDisequality pos typespec consts nonconsts _ = do
    defs <- lookupProc "~="
    if isJust defs
    then return [] -- don't generate if user-defined
    else do
      let neProto = ProcProto "~=" [Param leftName typespec ParamIn Ordinary `maybePlace` pos,
                                     Param rightName typespec ParamIn Ordinary `maybePlace` pos]
                    Set.empty
      let neBody = [maybePlace (Not $
                        ProcCall (First [] "=" Nothing) SemiDet False
                            [varGetTyped leftName typespec `maybePlace` pos,
                             varGetTyped rightName typespec `maybePlace` pos]
                            `maybePlace` pos) pos]
      return [ProcDecl Public inlineSemiDetModifiers neProto neBody Nothing]


-- |Does the item declare a test or Boolean function with the specified
-- name and arity?
isTestProc :: ProcName -> Int -> Item -> Bool
isTestProc name arity (ProcDecl _ mods (ProcProto n params _) _ _) =
    n == name && modifierDetism mods == SemiDet && length params == arity
isTestProc name arity (FuncDecl _ mods (ProcProto n params _) ty _ _) =
    n == name && modifierDetism mods == Det
    && length params == arity && ty == boolType
isTestProc _ _ _ = False


-- | Generate the body of an equality test proc given the const and
--   non-const constructors.
--   Our strategy is:
--       if there are no non-consts, just compare the values; otherwise
--       if there are any consts, generate code to check if the value
--       of the first is less than the number of consts, and if so, return
--       whether or not the two values are equal.  If there are no consts,
--       or if the value is not less than the number, then generate one
--       test per non-const constructor.  Each test checks if the tag of
--       the first argument is the tag for that constructor (unless there
--       is exactly one non-const constructor, in which case skip the test),
--       and then test each field for equality by calling the = test.
--
--   Also return whether the test should be inlined.  We inline when there
--   there is no more than one non-const constructor and either it has no more
--   than two arguments or there are no const constructors.
--
equalityBody :: OptPos -> [Placed ProcProto] -> [Placed ProcProto]
             -> TypeRepresentation -> ([Placed Stmt],Inlining)
-- Special case for phantom (void) types
equalityBody _ _ _ (Bits 0) = ([succeedTest], Inline)
equalityBody _ [] [] _ = shouldnt "trying to generate = test with no constructors"
equalityBody pos _ _ (Bits _) = ([simpleEqualityTest pos],Inline)
equalityBody pos consts [] _ = ([equalityConsts pos consts],Inline)
equalityBody pos consts nonconsts _ =
    -- decide whether $left is const or non const, and handle accordingly
    ([Cond (comparison "icmp_uge"
            (castTo (varGet leftName) intType)
            (iVal $ length consts))
        [equalityNonconsts pos (content <$> nonconsts) (List.null consts)]
        [equalityConsts pos consts]
        Nothing Nothing Nothing `maybePlace` pos],
     -- Decide to inline if only 1 non-const constructor, no non-const
     -- constructors (so not recursive), and at most 4 fields
     case List.map content nonconsts of
         [ProcProto _ params _ ] | length params <= 4 && List.null consts ->
              Inline
         _ -> MayInline
        )


-- |Return code to check if two const values values are equal, given that we
--  know that the $left value is a const.
equalityConsts :: OptPos -> [Placed ProcProto] -> Placed Stmt
equalityConsts pos [] = rePlace pos failTest
equalityConsts pos _  = simpleEqualityTest pos


-- |An equality test that just compares $left and $right for identity
simpleEqualityTest :: OptPos -> Placed Stmt
simpleEqualityTest pos =
    rePlace pos $ comparison "icmp_eq" (varGet leftName) (varGet rightName)


-- |Return code to check that two values are equal when the first is known
--  not to be a const constructor.  The first argument is the list of
--  nonconsts, second is the list of consts.
equalityNonconsts :: OptPos -> [ProcProto] -> Bool -> Placed Stmt
equalityNonconsts _ [] _ =
    shouldnt "type with no non-const constructors should have been handled"
equalityNonconsts pos [ProcProto name params _] noConsts =
    -- single non-const and no const constructors:  just compare fields
    let detism = if noConsts then Det else SemiDet
    in  And ([deconstructCall name leftName params detism,
            deconstructCall name rightName params detism]
            ++ concatMap equalityField params) `maybePlace` pos
equalityNonconsts pos ctrs _ =
    equalityMultiNonconsts pos ctrs


-- |Return code to check that two values are equal when the first is known
--  not to be a const constructor specifically for a type with multiple
--  nonconst constructors.  This generates nested conditions testing
--  $left against each possible constructor; if it matches, it tests
--  that $right is also that constructor and all the fields match; if
--  it doesn't match, it tests the next possible constructor, etc.
equalityMultiNonconsts :: OptPos -> [ProcProto] -> Placed Stmt
equalityMultiNonconsts pos [] = rePlace pos failTest
equalityMultiNonconsts pos (ProcProto name params _:ctrs) =
    Cond (deconstructCall name leftName params SemiDet)
        [And (deconstructCall name rightName params SemiDet : concatMap equalityField params) `maybePlace` pos]
        [equalityMultiNonconsts pos ctrs] Nothing Nothing Nothing `maybePlace` pos

-- |Return code to deconstruct
deconstructCall :: Ident -> Ident -> [Placed Param] -> Determinism -> Placed Stmt
deconstructCall ctor arg params detism =
    Unplaced $ ProcCall (regularProc ctor) detism False
     $ List.map (Unplaced . varSet . specialName2 arg . paramName . content) params
        ++ [Unplaced $ varGet arg]


-- |Return code to check that one field of two data are equal, when
--  they are known to have the same constructor.
equalityField :: Placed Param -> [Placed Stmt]
equalityField param =
    let field = paramName $ content param
        leftField = specialName2 leftName field
        rightField = specialName2 rightName field
    in  [Unplaced $ ProcCall (regularProc "=") SemiDet False
            [Unplaced $ varGet leftField,
             Unplaced $ varGet rightField]]


inlineModifiers :: ProcVariant -> Determinism -> ProcModifiers
inlineModifiers variant detism
    = setInline Inline
    $ setVariant variant
    $ setDetism detism defaultProcModifiers



inlineSemiDetModifiers :: ProcModifiers
inlineSemiDetModifiers = inlineModifiers RegularProc SemiDet


-- |The name of the variable holding a record
recName :: Ident
recName = specialName "rec"


-- |The name of the variable holding the current record field
fieldName :: Ident
fieldName = specialName "field"


-- |The name of the variable holding the current record tag
tagName :: Ident
tagName = specialName "tag"


-- |The name of the first temp variable
tmpName1 :: Ident
tmpName1 = specialName "temp"


-- |The name of the second temp variable
tmpName2 :: Ident
tmpName2 = specialName "temp2"


-- |The name of the left argument to =
leftName :: Ident
leftName = specialName "left"


-- |The name of the right argument to =
rightName :: Ident
rightName = specialName "right"


-- |Log a message about normalised input items.
logNormalise :: String -> Compiler ()
logNormalise = logMsg Normalise
