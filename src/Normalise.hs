--  File     : Normalise.hs
--  Author   : Peter Schachte
--  Purpose  : Convert parse tree into an AST
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
--  BEGIN MAJOR DOC
--  This code normalises wybe code as parsed, converting it to a simpler form
--  to make compiling easier.  This is complicated by the need to handle
--  module dependencies, in particular for handling type declarations.  For this
--  reason, normalisation is divided into the part that can per completed
--  without considering dependencies and the part that can only be performed
--  when all dependencies are available and normalised.
--
--  Dependency-independent normalisation includes:
--
--      * recording dependencies (imports, including foreign dependencies)
--
--      * converting function definitions into procedure definitions
--
--      * flattening and recording procedure definitions
--
--      * recording type declarations for later handling, as well as determining
--        type representation and type signatures of generated procedures
--
--      * flattening and recording top-level statements
--
--      * recording resource declarations
--
--      * recording pragmas
--
--  These are all handled by the `normalise` function.
--
--  Currently, only the normalisation delayed until dependencies are determined
--  and loaded is the laying out of user-defined types and the generation of
--  constructor, deconstructor, accessor, mutator, and auxiliary procedures.
--  This is implemented by the `completeNormalisation` function, which takes a
--  list of modules forming a SCC in the module dependency hierarchy, and which
--  is not called until all the dependencies other than mutual dependencies have
--  been loaded.  Because any recursive (or mutually-recursive) type is
--  represented as a word pointer, this doesn't create a conflict.
--  END MAJOR DOC


module Normalise (normalise, completeNormalisation) where

import AST
import Config (wordSize, wordSizeBytes, availableTagBits,
               tagMask, smallestAllocatedAddress)
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
-- import Data.Tuple.Extra
import Flatten
import Options (LogSelection(Normalise))
import Snippets
import Util

-- |Normalise a list of file items, storing the results in the current module.
normalise :: [Item] -> Compiler ()
normalise items = do
    mapM_ normaliseItem items
    -- import stdlib unless no_standard_library pragma is specified
    useStdLib <- getModuleImplementationField (Set.notMember NoStd . modPragmas)
    when useStdLib $ addImport (ImportSpec ["wybe"] (Just Set.empty) Nothing)
    return ()


----------------------------------------------------------------
-- Normalising a module item
--
-- This only handles what can be handled without having loaded dependencies.
----------------------------------------------------------------

-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) typeImpln items pos)
  = do
    let items' = normaliseTypeImpln typeImpln params pos items
    normaliseSubmodule name vis pos items'
    return ()
normaliseItem (ModuleParamsDecl params pos) =
    addParameters params pos
normaliseItem (RepresentationDecl rep pos) =
    addTypeRep rep pos
normaliseItem (ConstructorDecl vis ctors) =
    mapM_ (addConstructor vis) ctors
normaliseItem (ModuleDecl vis name items pos) =
    normaliseSubmodule name vis pos items
normaliseItem (ImportMods vis modspecs pos) =
    mapM_ (\mspec -> addImport (importSpec mspec Nothing vis)) modspecs
normaliseItem (ImportItems vis modspec imports pos) =
    addImport (importSpec modspec (Just imports) vis)
normaliseItem (ImportForeign files _) =
    mapM_ addForeignImport files
normaliseItem (ImportForeignLib files _) =
    mapM_ addForeignLib files
normaliseItem (ResourceDecl vis name typ init pos) = do
  addSimpleResource name (SimpleResource typ init pos) vis
  case init of
    Nothing  -> return ()
    Just val -> normaliseItem (StmtDecl (ProcCall [] "=" Nothing Det False
                                         [Unplaced $ varSet name, val]) pos)
normaliseItem (FuncDecl vis detism inline
                           (ProcProto name params resources)
                           resulttype result pos) =
  let flowType = Implicit pos
  in  normaliseItem
   (ProcDecl
    vis detism inline
    (ProcProto name (params ++ [Param "$" resulttype ParamOut flowType])
     resources)
    [maybePlace (ForeignCall "llvm" "move" []
                 [maybePlace (Typed (content result) resulttype False)
                  $ place result,
                  Unplaced
                  $ Typed (Var "$" ParamOut flowType) resulttype False])
     pos]
    pos)
normaliseItem item@(ProcDecl _ _ _ _ _ _) = do
    (item',tmpCtr) <- flattenProcDecl item
    logNormalise $ "Normalised proc:" ++ show item'
    addProc tmpCtr item'
normaliseItem (StmtDecl stmt pos) = do
    logNormalise $ "Normalising statement decl " ++ show stmt
    updateModule (\s -> s { stmtDecls = maybePlace stmt pos : stmtDecls s})
normaliseItem (PragmaDecl prag) =
    addPragma prag



normaliseSubmodule :: Ident -> Visibility -> OptPos -> [Item] -> Compiler ()
normaliseSubmodule name vis pos items = do
    dir <- getDirectory
    parentModSpec <- getModuleSpec
    let subModSpec = parentModSpec ++ [name]
    pragmas <- getModuleImplementationField modPragmas
    logNormalise $ "Normalising submodule " ++ showModSpec subModSpec ++ " {"
    mapM_ (logNormalise . ("  "++) . show) items
    logNormalise "}"
    addImport (importSpec subModSpec Nothing vis)
    when (vis == Public) $ addPubSubmod subModSpec pos
    -- Add the submodule to the submodule list of the implementation
    updateImplementation $ updateModSubmods (Map.insert name subModSpec)
    logNormalise $ "Submodule " ++ showModSpec subModSpec
                   ++ " is new:  entering"
    enterModule dir subModSpec (Just parentModSpec)
    -- submodule always imports parent module
    addImport (importSpec parentModSpec Nothing Private)
    -- Pragmas of the father are visited upon the sons
    updateImplementation (\imp -> imp { modPragmas = pragmas})
    -- when (isJust typeParams)
    --   $ do
    --     logNormalise $ "Adding known type " ++ name
    --                    ++ " to module " ++ intercalate "." subModSpec
    --     updateImplementation
    --       (\imp ->
    --          let set = Set.singleton $ TypeSpec parentModSpec name []
    --          in imp { modKnownTypes = Map.insert name set $ modKnownTypes imp })
    --     mapM_
    --       (\param -> do
    --           logNormalise $ "Adding type parameter " ++ param
    --                          ++ " to module " ++ intercalate "." subModSpec
    --           updateImplementation
    --            (\imp ->
    --               let set = Set.singleton $ TypeParam param
    --               in imp { modKnownTypes = Map.insert param set
    --                        $ modKnownTypes imp }))
    --       (fromJust typeParams)
    normalise items
    modSpecs <- exitModule
    unless (List.null modSpecs)
          $ shouldnt $ "finish normalising submodule left modules to compile: "
                       ++ showModSpecs modSpecs
    -- logNormalise $ "Deferring compilation of submodules "
    --                ++ showModSpecs modSpecs
    -- mods <- List.map (trustFromJust "lookup submodule after normalising")
    --         <$> mapM getLoadingModule modSpecs
    -- deferModules mods
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

completeNormalisation :: [ModSpec] -> Compiler ()
completeNormalisation mods = do
    completeTypeNormalisation mods
    mapM_ (normaliseModMain `inModule`) mods


-- | Layout the types defined on the specified module list, which comprise
--   a strongly connected component in the module dependency graph. Because
--   SCCs are handled in topologically sorted order (bottom-up), this means
--   all types defined in the specified modules have already been laid out
--   and can be looked up. However, to layout a type, we need to have first
--   laid out the types it depends on. In the case of (mutually) recursive
--   types, we represent all of them as pointers. Thus we first find the
--   SCCs in the type dependency graph restricted to the specified modules,
--   and lay out those types bottom-up. Once a type is laid out, we also
--   generate constructors, deconstructors, accessors, mutators, and
--   auxiliary procedures.
completeTypeNormalisation :: [ModSpec] -> Compiler ()
completeTypeNormalisation mods = do
    logNormalise $ "Completing normalisation of modules " ++ showModSpecs mods
    types <- modSCCTypeDeps mods
    logNormalise $ "Ordered type dependency SCCs: " ++ show types
    -- Some of these may ultimately not be reference types, but for now what
    -- matters is that they have representations, so we can tell they're types.
    mapM_ recordRefType $ concat [ typeDefMod <$> sccElts scc | scc <- types]
    -- Now all types used by any types in this module SCC have representations
    mapM_ recordTypeImports mods
    mapM_ completeTypeSCC types


data TypeDef = TypeDef {
               typeDefMod   :: ModSpec,
               typeDefCtors :: [(Visibility,Placed ProcProto)]
  } deriving Show


-- | Return a topologically sorted list of type dependency SCCs in the
--   specified modules.  Any types depended on by these types that are not on
--   the sccMods list will already have been processed.  Types defined by
--   representation are included first in the list as acyclic SCCs, followed
--   by SCCs of algebraic types by type dependencies, limited to modules (types)
--   defined in this module dependency SCC.
modSCCTypeDeps :: [ModSpec] -> Compiler [SCC TypeDef]
modSCCTypeDeps sccMods = do
    -- Collect the Modules in the module dependency SCC
    sccModules <- catMaybes <$> mapM getLoadedModule sccMods
    -- Report primitive types in the module dependency SCC.  These already have
    -- their representations defined, so there's nothing more to do for them.
    let repTypes = [modSpec modl
                   | modl <- sccModules
                   , isJust $ modTypeRep modl]
    logNormalise $ "Primitive Types in module SCC:  "
                   ++ showModSpecs repTypes
    -- Collect algebraic types in this SCC and their constructors
    let defs = [TypeDef modspec ctrs
               | modl <- sccModules
               , let modspec = modSpec modl
               , ctrs <- maybeToList $
                         reverse <$>
                         (modImplementation modl >>= modConstructors)]
    graph <- mapM (\def@(TypeDef spec ctrs) -> do
                      reenterModule spec
                      used <- concatMapM (usedTypes sccMods . snd) ctrs
                      _ <- reexitModule
                      return (def, spec, used))
             defs
    let typeSccs = stronglyConnComp graph
    logNormalise $ "Algebraic Types in module SCC:  "
                   ++ intercalate ", " (show <$> typeSccs)
    return typeSccs


-- | Return a list of the algebraic types, limited to the specified list of
-- modules, that are referred to by members of the specified constructor.
-- This is executed in the module of the type being defined.
usedTypes :: [ModSpec] -> Placed ProcProto -> Compiler [ModSpec]
usedTypes mods pproto = do
    let pos = place pproto
    let types = paramType <$> procProtoParams (content pproto)
    tspecs <- catMaybes <$> mapM (flip lookupType pos) types
    let modDeps = Set.fromList $ catMaybes $ typeSpecModule <$> tspecs
    let candidates = Set.fromList mods
    return $ Set.toList $ Set.intersection modDeps candidates


-- | Update the specified module to indicate that it's a type represented as a
-- reference type.
recordRefType :: ModSpec -> Compiler ()
recordRefType = updateLoadedModule (\m -> m { modTypeRep = Just Address })


-- Every type the specified module imports has a representation defined (which
-- may be changed later). Now record all the types visible to this module, which
-- is the set of modules it imports that have type representations.
recordTypeImports :: ModSpec -> Compiler ()
recordTypeImports modspec = do
    reenterModule modspec
    imports <- (importedMod <$>) . concat . Map.elems
               <$> getModuleImplementationField modImports
    logNormalise $ "Module " ++ showModSpec modspec ++ " imports: "
                   ++ showModSpecs imports
    knownTypes <- filterM moduleIsType imports
    logNormalise $ "  Adding known types from: " ++ showModSpecs imports
    mapM_ (\m -> addKnownType (last m) m) knownTypes
    _ <- reexitModule
    return ()



-- modTypeDeps :: [ModSpec] -> Compiler [((TypeKey,TypeDef), TypeKey, [TypeKey])]
-- modTypeDeps sccMods = do
--     modspec <- getModuleSpec
--     pairs <- Map.toList <$> getModuleImplementationField modTypes
--     mapM (typeDeps sccMods) [((name,modspec),def) | (name,def) <- pairs]


-- | Produce the input needed to construct a list of SCCs.
-- typeDeps :: [ModSpec] -> (TypeKey,TypeDef)
--          -> Compiler ((TypeKey,TypeDef), TypeKey, [TypeKey])
-- typeDeps sccMods (key,def) = do
--     let deps = typeDefMembers def
--     depKeys <- (Set.toList . Set.fromList . concat)
--                <$> mapM (placedApplyM $ protoKeys sccMods) deps
--     return ((key,def), key, depKeys)

-- | Return a list of all the types defined in any of the sccMods that are
--   used as parameter types of any of the parameters of the provided ProcProto
-- protoKeys :: [ModSpec] -> ProcProto -> OptPos -> Compiler [TypeKey]
-- protoKeys sccMods proto pos = do
--     let types = paramType <$> procProtoParams proto
--     -- XXX to handle parametric types, we need to include the type parameters
--     types' <- catMaybes <$> mapM (`lookupType` pos) types
--     return [(name,mod) | (TypeSpec mod name _) <- types', mod `elem` sccMods]


-- | Layout the types defined in the specified type dependency SCC, and then
--   generate constructors, deconstructors, accessors, mutators, and
--   auxiliary procedures.
completeTypeSCC :: SCC TypeDef -> Compiler ()
completeTypeSCC (AcyclicSCC tdef@(TypeDef modspec members)) = do
    logNormalise $ "Completing non-recursive type "
                   ++ showModSpec modspec ++ " = " ++ show members
    completeType tdef
completeTypeSCC (CyclicSCC typedefs) = do
    logNormalise $ "Completing recursive type(s):" ++ show typedefs
    mapM_ (\(TypeDef modspec members) ->
             logNormalise $ "   " ++ showModSpec modspec ++ " = "
               ++ show members)
      typedefs
    mapM_ completeType typedefs


-- | Information about a non-constant constructor
data CtorInfo = CtorInfo {
           ctorInfoVis   :: Visibility, -- ^ visibility of this constructor
           ctorInfoName  :: ProcName,   -- ^ this constructor's name
           ctorInfoParams:: [(Param,TypeRepresentation,Int)],
                                        -- ^ params of this ctor, with their
                                        -- representation and bit size
           ctorInfoPos   :: OptPos,     -- ^ file position of ctor
           ctorInfoTag   :: Int,        -- ^ this constructor's tag
           ctorInfoBits  :: Int         -- ^ min number of bits needed
     } deriving (Show)


-- | Layout the specified type, and then generate constructors,
--   deconstructors, accessors, mutators, and auxiliary procedures.
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
completeType :: TypeDef -> Compiler ()
completeType (TypeDef modspec ctors) = do
    logNormalise $ "Completing type " ++ showModSpec modspec
    reenterModule modspec
    let (constCtors,nonConstCtors) =
          List.partition (List.null . procProtoParams . content . snd) ctors
    let numConsts = length constCtors
    let numNonConsts = length nonConstCtors
    let (tagBits,tagLimit) =
          if numNonConsts > wordSizeBytes
          then -- must set aside one tag to indicate secondary tag
            (availableTagBits, wordSizeBytes - 2)
          else if numNonConsts == 0
          then (0, 0)
          else (ceiling $ logBase 2 (fromIntegral numNonConsts),
                 wordSizeBytes - 1)
    logNormalise $ "Complete " ++ showModSpec modspec
                   ++ " with " ++ show tagBits ++ " tag bits and "
                   ++ show tagLimit ++ " tag limit"
    when (numConsts >= fromIntegral smallestAllocatedAddress)
      $ nyi $ "Type '" ++ showModSpec modspec
              ++ "' has too many constant constructors"
    let typespec = TypeSpec (init modspec) (last modspec) []
                   -- XXX need the right type parameters
                   -- $ List.map TypeParam params
    let constItems = concatMap (constCtorItems typespec) $ zip constCtors [0..]
    infos <- zipWithM nonConstCtorInfo nonConstCtors [0..]
    (reps,nonconstItemsList) <-
      unzip <$> mapM
      (nonConstCtorItems typespec numConsts numNonConsts
        tagBits tagLimit)
      infos
    let rep = typeRepresentation reps numConsts
    setTypeRep rep
    extraItems <- implicitItems typespec (snd <$> constCtors)
                  (snd <$> nonConstCtors) rep
    logNormalise $ "Representation of type "
                   ++ showModSpec modspec
                   ++ " is " ++ show rep
    normalise $ constItems ++ concat nonconstItemsList ++ extraItems
    reexitModule
    return ()


-- | Analyse the representation of a single constructor, determining the
--   representation of its members, its total size in bits (assuming it is
--   *not* boxed, so each member takes the minimum number of bits), and its
--   total size in bytes (assuming it is boxed, so each member takes an
--   integral number of bytes).
nonConstCtorInfo :: (Visibility,Placed ProcProto) -> Int -> Compiler CtorInfo
nonConstCtorInfo (vis,placedProto) tag = do
    logNormalise $ "Analysing non-constant ctor "
                   ++ show tag ++ ": " ++ show placedProto
    let (proto,pos) = unPlace placedProto
    unless (Set.null $ procProtoResources proto)
      $ shouldnt $ "Constructor with resources: " ++ show placedProto
    let name   = procProtoName proto
    let params = procProtoParams proto
    params' <- mapM (fixParamType pos) params
    logNormalise $ "With types resolved: " ++ show placedProto
    reps <- mapM ( lookupTypeRepresentation . paramType ) params'
    let reps' = catMaybes reps
    logNormalise $ "Member representations: "
                   ++ intercalate ", " (show <$> reps')
    let bitSizes = typeRepSize <$> reps'
    let bitSize  = sum bitSizes
    let typeReps = zip3 params' reps' bitSizes
    return $ CtorInfo vis name typeReps pos tag bitSize



fixParamType :: OptPos -> Param -> Compiler Param
fixParamType pos param = do
    let ty = paramType param
    ty' <- lookupType ty pos
    when (isNothing ty') $ errmsg pos $ "Unknown parameter type " ++ show ty
    let ty'' = fromMaybe InvalidType ty'
    return $ param { paramType = ty'' }


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
    logNormalise $ "Top-level statements = " ++ show stmts
    unless (List.null stmts) $ do
      resources <- initResources
      normaliseItem (ProcDecl Public Det False (ProcProto "" [] resources)
                      (List.reverse stmts) Nothing)

-- |The resources available at the top level of this module
initResources :: Compiler (Set ResourceFlowSpec)
initResources = do
    mods <- getModuleImplementationField
            ((importedMod <$>) . concat . Map.elems . modImports)
    mods' <- ((mods ++) . concat) <$> mapM descendentModules mods
    logNormalise $ "in initResources, mods = " ++ showModSpecs mods'
    importedMods <- catMaybes <$> mapM getLoadingModule mods'
    let importImplns = catMaybes (modImplementation <$> importedMods)
    let importResources = (Map.assocs . content . snd) <$>
                     (concat $ (Map.assocs . modResources) <$> importImplns)
    let initialisedImports = List.filter (isJust . snd) $ concat importResources
    impln <- getModuleImplementationField id
    let localResources = (Map.assocs . content . snd) <$>
                         (Map.assocs $ modResources impln)
    let initialisedLocal = List.filter (isJust . snd) $ concat localResources
    let resources = ((\spec -> ResourceFlowSpec (fst spec) ParamInOut)
                     <$> initialisedImports)
                    ++ ((\spec -> ResourceFlowSpec (fst spec) ParamOut)
                        <$> initialisedLocal)
    logNormalise $ "In initResources, resources = " ++ show resources
    return $ Set.fromList resources



----------------------------------------------------------------
--                Generating code for type declarations
----------------------------------------------------------------


-- |Given a type declaration, turn it into separate Items for parameters,
-- representation, and constructors that implement the type.
normaliseTypeImpln :: TypeImpln -> [Ident] -> OptPos -> [Item] -> [Item]
normaliseTypeImpln (TypeRepresentation rep) params pos items =
    paramsItem params pos ++ RepresentationDecl rep pos : items
normaliseTypeImpln (TypeCtors vis ctors) params pos items =
    paramsItem params pos ++ ConstructorDecl vis ctors : items

-- Add an Item for type parameters, if needed.
paramsItem :: [Ident] -> OptPos -> [Item]
paramsItem [] _       = []
paramsItem params pos = [ModuleParamsDecl params pos]

-- |All items needed to implement a const contructor for the specified type.
constCtorItems :: TypeSpec -> ((Visibility,Placed ProcProto),Integer) -> [Item]
constCtorItems typeSpec ((vis,placedProto),num) =
    let (proto,pos) = unPlace placedProto
        constName = procProtoName proto
    in [ProcDecl vis Det True
        (ProcProto constName [Param "$" typeSpec ParamOut Ordinary] Set.empty)
        [lpvmCastToVar (castTo (iVal num) typeSpec) "$"] pos
       ]


-- |All items needed to implement a non-const contructor for the specified type.
nonConstCtorItems :: TypeSpec -> Int -> Int -> Int -> Int -> CtorInfo
                  -> Compiler (TypeRepresentation,[Item])
nonConstCtorItems typeSpec numConsts numNonConsts tagBits tagLimit
                  info@(CtorInfo vis ctorName paramsReps pos tag bits) = do
    -- If we're unboxed and there are const ctors, then we need an extra
    -- bit to make sure the unboxed value is > than any const value
    let nonConstsize = bits + tagBits
    let (size,nonConstBit)
          = if numConsts == 0
            then (nonConstsize,Nothing)
            else let constSize = ceiling $ logBase 2 $ fromIntegral numConsts
                     size' = 1 + max nonConstsize constSize
                 in (size', Just $ size' - 1)
    logNormalise $ "Making constructor items for " ++ show info
    logNormalise $ show bits ++ " data bit(s)"
    logNormalise $ show tagBits ++ " tag bit(s)"
    logNormalise $ "nonConst bit = " ++ show nonConstBit
    if size <= wordSize && tag <= tagLimit
      then do -- unboxed representation
      let fields =
            reverse
            $ snd
            $ List.foldr
              (\(param,_,sz) (shift,flds) ->
                  (shift+sz,(paramName param,paramType param,shift,sz):flds))
              (tagBits,[])
              paramsReps
      return (Bits size,
              unboxedConstructorItems vis ctorName typeSpec tag nonConstBit
               fields pos
               ++ unboxedDeconstructorItems vis ctorName typeSpec
                  numConsts numNonConsts tag pos fields
               ++ concatMap (unboxedGetterSetterItems vis typeSpec
                             numConsts numNonConsts tag pos) fields
             )
      else do -- boxed representation
      let (fields,size) = layoutRecord paramsReps tag tagLimit
      logNormalise $ "Laid out structure size " ++ show size
          ++ ": " ++ show fields
      let ptrCount = length $ List.filter ((==Address) . snd3) paramsReps
      logNormalise $ "Structure contains " ++ show ptrCount ++ " pointers, "
                     ++ show numConsts ++ " const constructors, "
                     ++ show numNonConsts ++ " non-const constructors"
      return (Address,
              constructorItems ctorName typeSpec fields size tag tagLimit pos
              ++ deconstructorItems ctorName typeSpec numConsts numNonConsts
                 tag tagLimit pos fields
              ++ concatMap
                 (getterSetterItems vis typeSpec pos numConsts numNonConsts
                  ptrCount size tag tagLimit)
                 fields
             )

-- |The number of bytes occupied by a value of the specified type.  If the
--  type is boxed, this is the word size.
fieldSize :: TypeSpec -> Compiler Int
-- XXX Generalise to allow non-word size fields
fieldSize _ = return wordSizeBytes


----------------------------------------------------------------
--                Generating code for boxed types
----------------------------------------------------------------

-- | Lay out a record in memory, returning the size of the record and a
-- list of the fields and offsets of the structure.  This ensures that
-- values are aligned properly for their size (eg, word sized values are
-- aligned on word boundaries).
layoutRecord :: [(Param,TypeRepresentation,Int)] -> Int -> Int
             -> ([(VarName,TypeSpec,TypeRepresentation,Int)], Int)
layoutRecord paramsReps tag tagLimit =
      let sizes = (2^) <$> [0..floor $ logBase 2 $ fromIntegral wordSizeBytes]
          fields = List.map
                   (\(var,rep,sz) ->
                       let byteSize = (sz + 7) `div` 8
                           wordSize = ((byteSize + wordSizeBytes - 1)
                                        `div` wordSizeBytes) * wordSizeBytes
                           alignment =
                             fromMaybe wordSizeBytes $ find (>=byteSize) sizes
                       in ((paramName var,paramType var,rep,byteSize),
                           alignment))
                   paramsReps
          -- put fields in order of increasing alignment
          ordFields = sortOn snd fields
          -- add secondary tag if necessary
          initOffset = if tag > tagLimit then wordSizeBytes else 0
          offsets = List.foldl align ([],initOffset) ordFields
      in mapFst reverse offsets


-- | Actually layout the fields.
align :: ([(VarName,TypeSpec,TypeRepresentation,Int)], Int)
      -> ((VarName,TypeSpec,TypeRepresentation,Int),Int)
      -> ([(VarName,TypeSpec,TypeRepresentation,Int)], Int)
align (aligned,offset) ((name,ty,rep,sz),alignment) =
    ((name,ty,rep,alignedOffset):aligned, alignedOffset+sz)
  where alignedOffset = alignOffset offset alignment


-- |Given the smallest offset into a structure that a value can be stored at
-- and the required alignment for that value, return the aligned offset.
alignOffset :: Int -> Int -> Int
alignOffset offset alignment =
    offset + (-offset) `mod` alignment


-- |Generate constructor code for a non-const constructor
--  XXX generalise to generate unboxed constructors
constructorItems :: ProcName -> TypeSpec
                 -> [(VarName,TypeSpec,TypeRepresentation,Int)]
                 -> Int -> Int -> Int -> OptPos -> [Item]
constructorItems ctorName typeSpec fields size tag tagLimit pos =
    let flowType = Implicit pos
        params = sel1 <$> fields
        proto = (ProcProto ctorName
                 ([Param name paramType ParamIn Ordinary
                  | (name,paramType,_,_) <- fields]
                   ++[Param "$" typeSpec ParamOut Ordinary])
                 Set.empty)
    in [ProcDecl Public Det True proto
        -- Code to allocate memory for the value
        ([Unplaced $ ForeignCall "lpvm" "alloc" []
          [Unplaced $ iVal size,
           Unplaced $ Typed (varSet "$rec") typeSpec True]]
         ++
         -- fill in the secondary tag, if necessary
         (if tag > tagLimit
          then [Unplaced $ ForeignCall "lpvm" "mutate" []
                 [Unplaced $ Typed (varGetSet "$rec" flowType) typeSpec False,
                  Unplaced $ iVal 0,
                  Unplaced $ iVal 1,
                  Unplaced $ iVal size,
                  Unplaced $ iVal 0,
                  Unplaced $ iVal tag]]
          else [])
         ++
         -- Code to fill all the fields
         (List.map
          (\(var,ty,_,offset) ->
               (Unplaced $ ForeignCall "lpvm" "mutate" []
                 [Unplaced $ Typed (varGetSet "$rec" flowType) typeSpec False,
                  Unplaced $ iVal offset,
                  Unplaced $ iVal 1,
                  Unplaced $ iVal size,
                  Unplaced $ iVal 0,
                  Unplaced $ Typed (Var var ParamIn flowType) ty False]))
          fields)
         ++
         -- Finally, code to tag the reference
         [Unplaced $ ForeignCall "llvm" "or" []
          [Unplaced $ varGet "$rec",
           Unplaced $ iVal (if tag > tagLimit then tagLimit+1 else tag),
           Unplaced $ varSet "$"]])
        pos]


-- |Generate deconstructor code for a non-const constructor
deconstructorItems :: Ident -> TypeSpec -> Int -> Int -> Int -> Int -> OptPos
                   -> [(Ident,TypeSpec,TypeRepresentation,Int)] -> [Item]
deconstructorItems ctorName typeSpec numConsts numNonConsts tag tagLimit
                   pos fields =
    let flowType = Implicit pos
        detism = if numConsts + numNonConsts > 1 then SemiDet else Det
    in [ProcDecl Public detism True
        (ProcProto ctorName
         (List.map (\(n,t,_,_) -> (Param n t ParamOut Ordinary)) fields
          ++ [Param "$" typeSpec ParamIn Ordinary])
         Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag tagLimit "$"]
         -- Code to fetch all the fields
         ++ List.map (\(var,_,_,aligned) ->
                              (Unplaced $ ForeignCall "lpvm" "access" []
                               [Unplaced $ Var "$" ParamIn flowType,
                                Unplaced $ iVal (aligned - tag),
                                Unplaced $ Var var ParamOut flowType]))
            fields)
        pos]


-- |Generate the needed Test statements to check that the tag of the value
--  of the specified variable matches the specified tag.  If not checking
--  is necessary, just generate a Nop, rather than a true test.
tagCheck :: Int -> Int -> Int -> Int -> Ident -> Placed Stmt
tagCheck numConsts numNonConsts tag tagLimit varName =
    -- If there are any constant constructors, be sure it's not one of them
    let tests =
          (case numConsts of
               0 -> []
               _ -> [comparison "uge"
                     (varGet varName)
                     (intCast $ iVal numConsts)]
           ++
           -- If there is more than one non-const constructors, check that
           -- it's the right one
           (case numNonConsts of
               1 -> []  -- Nothing to do if it's the only non-const constructor
               _ -> [comparison "eq"
                     (intCast $ ForeignFn "llvm" "and" []
                      [Unplaced $ varGet varName,
                       Unplaced $ iVal tagMask])
                     (intCast $ iVal (if tag > tagLimit
                                      then wordSizeBytes-1
                                      else tag))])
           ++
           -- If there's a secondary tag, check that, too.
           if tag > tagLimit
           then [Unplaced $ ForeignCall "lpvm" "access" []
                 [Unplaced $ varGet varName,
                  Unplaced $ iVal 0,
                  Unplaced $ varSet "$tag"],
                 comparison "eq" (varGet "$tag") (iVal tag)]
           else [])

    in if List.null tests
       then Unplaced Nop
       else seqToStmt tests


-- |Generate the needed statements to strip the specified tag off of the value
--  of the specified variable, placing the result in the second variable.
--  We use the stripped name with "$asInt" appended as a temp var name.
-- | Produce a getter and a setter for one field of the specified type.
getterSetterItems :: Visibility -> TypeSpec -> OptPos
                    -> Int -> Int -> Int -> Int -> Int -> Int
                    -> (VarName,TypeSpec,TypeRepresentation,Int) -> [Item]
getterSetterItems vis rectype pos numConsts numNonConsts ptrCount size
                  tag tagLimit (field,fieldtype,rep,offset) =
    -- XXX generate cleverer code if multiple constructors have some of
    --     the same field names
    let detism = if numConsts + numNonConsts == 1 then Det else SemiDet
        otherPtrCount = if rep == Address then ptrCount-1 else ptrCount
        flags = if otherPtrCount == 0 then ["noalias"] else []
    in [-- The getter:
        ProcDecl vis detism True
        (ProcProto field [Param "$rec" rectype ParamIn Ordinary,
                          Param "$" fieldtype ParamOut Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag tagLimit "$rec"]
         ++
        -- Code to access the selected field
         [Unplaced $ ForeignCall "lpvm" "access" []
          [Unplaced $ varGet "$rec",
           Unplaced $ iVal (offset - tag),
           Unplaced $ varSet "$"]])
        pos,
        -- The setter:
        ProcDecl vis detism True
        (ProcProto field [Param "$rec" rectype ParamInOut Ordinary,
                          Param "$field" fieldtype ParamIn Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag tagLimit "$rec"]
         ++
        -- Code to mutate the selected field
         [Unplaced $ ForeignCall "lpvm" "mutate" flags
          [Unplaced $ Typed (Var "$rec" ParamInOut $ Implicit pos)
                      rectype False,
           Unplaced $ iVal (offset - tag),
           Unplaced $ iVal 0,    -- May be changed to 1 by CTGC transform
           Unplaced $ iVal size,
           Unplaced $ iVal tag,
           Unplaced $ varGet "$field"]])
        pos]


----------------------------------------------------------------
--                Generating code for unboxed types
----------------------------------------------------------------

-- |Generate constructor code for a non-const constructor
-- unboxedConstructorItems
unboxedConstructorItems :: Visibility -> ProcName -> TypeSpec -> Int
                        -> Maybe Int -> [(VarName,TypeSpec,Int,Int)]
                        -> OptPos -> [Item]
unboxedConstructorItems vis ctorName typeSpec tag nonConstBit fields pos =
    let flowType = Implicit pos
        params = sel1 <$> fields
        proto = (ProcProto ctorName
                 ([Param name paramType ParamIn Ordinary
                  | (name,paramType,_,_) <- fields]
                   ++[Param "$" typeSpec ParamOut Ordinary])
                 Set.empty)
    in [ProcDecl vis Det True proto
         -- Initialise result to 0
        ([Unplaced $ ForeignCall "llvm" "move" []
          [Unplaced $ Typed (iVal 0) typeSpec False,
           Unplaced $ Typed (varSet "$") typeSpec False]]
         ++
         -- Shift each field into place and or with the result
         (List.concatMap
          (\(var,ty,shift,sz) ->
               [Unplaced $ ForeignCall "llvm" "shl" []
                 [Unplaced $ Typed (varGet var) typeSpec True,
                  Unplaced $ Typed (iVal shift) typeSpec False,
                  Unplaced $ Typed (varSet "$temp") typeSpec False],
                Unplaced $ ForeignCall "llvm" "or" []
                 [Unplaced $ Typed (varGet "$") typeSpec False,
                  Unplaced $ Typed (varGet "$temp") typeSpec False,
                  Unplaced $ Typed (varSet "$") typeSpec False]])
          fields)
         ++
         -- Or in the bit to ensure the value is greater than the greatest
         -- possible const value, if necessary
         (case nonConstBit of
            Nothing -> []
            Just shift ->
              [Unplaced $ ForeignCall "llvm" "or" []
               [Unplaced $ Typed (varGet "$") typeSpec False,
                Unplaced $ Typed (iVal (bit shift::Int)) typeSpec False,
                Unplaced $ Typed (varSet "$") typeSpec False]])
         -- Or in the tag value
          ++ [Unplaced $ ForeignCall "llvm" "or" []
               [Unplaced $ Typed (varGet "$") typeSpec False,
                Unplaced $ Typed (iVal tag) typeSpec False,
                Unplaced $ Typed (varSet "$") typeSpec False]]
        ) pos]


-- |Generate deconstructor code for a unboxed non-const constructor
unboxedDeconstructorItems :: Visibility -> ProcName -> TypeSpec -> Int -> Int
                          -> Int -> OptPos -> [(VarName,TypeSpec,Int,Int)]
                          -> [Item]
unboxedDeconstructorItems vis ctorName recType numConsts numNonConsts tag
                          pos fields =
    let flowType = Implicit pos
        detism = if numConsts + numNonConsts > 1 then SemiDet else Det
    in [ProcDecl vis detism True
        (ProcProto ctorName
         (List.map (\(n,fieldType,_,_) -> (Param n fieldType ParamOut Ordinary))
          fields
          ++ [Param "$" recType ParamIn Ordinary])
         Set.empty)
         -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag (wordSizeBytes-1) "$"]
         -- Code to fetch all the fields
         ++ List.concatMap
            (\(var,fieldType,shift,sz) ->
               -- Code to access the selected field
               [Unplaced $ ForeignCall "llvm" "lshr" []
                 [Unplaced $ Typed (varGet "$") recType False,
                  Unplaced $ Typed (iVal shift) recType False,
                  Unplaced $ Typed (varSet "$temp") recType False],
                Unplaced $ ForeignCall "llvm" "and" []
                 [Unplaced $ Typed (varGet "$temp") recType False,
                  Unplaced $ Typed (iVal $ (bit sz::Int) - 1) recType False,
                  Unplaced $ Typed (varSet "$temp2") recType False],
                Unplaced $ ForeignCall "lpvm" "cast" []
                 [Unplaced $ Typed (varGet "$temp2") recType False,
                  Unplaced $ Typed (varSet var) fieldType False]
               ])
            fields)
        pos]


-- -- | Produce a getter and a setter for one field of the specified type.
unboxedGetterSetterItems :: Visibility -> TypeSpec -> Int -> Int -> Int
                         -> OptPos -> (VarName,TypeSpec,Int,Int) -> [Item]
unboxedGetterSetterItems vis recType numConsts numNonConsts tag pos
                         (field,fieldType,shift,sz) =
    -- XXX generate cleverer code if multiple constructors have some of
    --     the same field names
    let detism = if numConsts + numNonConsts == 1 then Det else SemiDet
        fieldMask = (bit sz::Int) - 1
        shiftedHoleMask = complement $ fieldMask `shiftL` shift
    in [-- The getter:
        ProcDecl vis detism True
        (ProcProto field [Param "$rec" recType ParamIn Ordinary,
                          Param "$" fieldType ParamOut Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag (wordSizeBytes-1) "$rec"]
         ++
        -- Code to access the selected field
         [Unplaced $ ForeignCall "llvm" "lshr" []
           [Unplaced $ Typed (varGet "$rec") recType False,
            Unplaced $ Typed (iVal shift) recType False,
            Unplaced $ Typed (varSet "$rec") recType False],
          -- XXX Don't need to do this for the most significant field:
          Unplaced $ ForeignCall "llvm" "and" []
           [Unplaced $ Typed (varGet "$rec") recType False,
            Unplaced $ Typed (iVal fieldMask) recType False,
            Unplaced $ Typed (varSet "$field") recType False],
          Unplaced $ ForeignCall "lpvm" "cast" []
           [Unplaced $ Typed (varGet "$field") recType False,
            Unplaced $ Typed (varSet "$") fieldType False]
         ])
        pos,
        -- The setter:
        ProcDecl vis detism True
        (ProcProto field [Param "$rec" recType ParamInOut Ordinary,
                          Param "$field" fieldType ParamIn Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag (wordSizeBytes-1) "$rec"]
         ++
        -- Code to mutate the selected field by masking out the current
        -- value, shifting the new value into place and bitwise or-ing it
         [Unplaced $ ForeignCall "llvm" "and" []
           [Unplaced $ Typed (varGet "$rec") recType False,
            Unplaced $ Typed (iVal shiftedHoleMask) recType False,
            Unplaced $ Typed (varSet "$rec") recType False],
          Unplaced $ ForeignCall "llvm" "shl" []
           [Unplaced $ Typed (varGet "$field") recType True,
            Unplaced $ Typed (iVal shift) recType False,
            Unplaced $ Typed (varSet "$field") recType False],
          Unplaced $ ForeignCall "llvm" "or" []
           [Unplaced $ Typed (varGet "$rec") recType False,
            Unplaced $ Typed (varGet "$field") recType False,
            Unplaced $ Typed (varSet "$rec") recType False]
         ])
        pos]


----------------------------------------------------------------
--                     Generating implicit procs
--
-- Wybe automatically generates equality test procs if you don't write
-- your own definitions.  It should generate default implementations of
-- many more such procs.
--
----------------------------------------------------------------

implicitItems :: TypeSpec -> [Placed ProcProto] -> [Placed ProcProto]
              -> TypeRepresentation -> Compiler [Item]
implicitItems typespec consts nonconsts rep =
    if consts==[] && nonconsts==[]
    then return [] -- Can't generate implicit items for non-algebraic types
    else do
      eq <-  implicitEquality typespec consts nonconsts rep
      neq <- implicitDisequality typespec consts nonconsts rep
      -- XXX add comparison, print, display, maybe prettyprint, and lots more
      return $ eq ++ neq


implicitEquality :: TypeSpec -> [Placed ProcProto] -> [Placed ProcProto]
                 -> TypeRepresentation -> Compiler [Item]
implicitEquality typespec consts nonconsts rep = do
    eqProcs <- lookupProc "="
    if any ((==2) . length . procProtoParams . procProto) eqProcs
    then return [] -- don't generate proc if already user-defined
    else
      let eqProto = ProcProto "=" [Param "$left" typespec ParamIn Ordinary,
                                   Param "$right" typespec ParamIn Ordinary]
                    Set.empty
          (body,inline) = equalityBody consts nonconsts rep
      in return [ProcDecl Public SemiDet inline eqProto body Nothing]


implicitDisequality :: TypeSpec -> [Placed ProcProto] -> [Placed ProcProto]
                    -> TypeRepresentation -> Compiler [Item]
implicitDisequality typespec consts nonconsts _ = do
    neqProcs <- lookupProc "/="
    if any ((==2) . length . procProtoParams . procProto) neqProcs
    then return [] -- don't generate proc if already user-defined
    else
      let neProto = ProcProto "/=" [Param "$left" typespec ParamIn Ordinary,
                                     Param "$right" typespec ParamIn Ordinary]
                    Set.empty
          neBody = [Unplaced $ Not $ Unplaced $
                    ProcCall [] "=" Nothing SemiDet False
                    [Unplaced $ varGet "$left", Unplaced $ varGet "$right"]]
      in return [ProcDecl Public SemiDet True neProto neBody Nothing]


-- |Does the item declare a test or Boolean function with the specified
-- name and arity?
isTestProc :: ProcName -> Int -> Item -> Bool
isTestProc name arity (ProcDecl _ SemiDet _ (ProcProto n params _) _ _) =
    n == name && length params == arity
isTestProc name arity (FuncDecl _ Det _ (ProcProto n params _) ty _ _) =
    n == name && length params == arity && ty == boolType
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
equalityBody :: [Placed ProcProto] -> [Placed ProcProto] -> TypeRepresentation
             -> ([Placed Stmt],Bool)
-- Special case for phantom (void) types
equalityBody _ _ (Bits 0) = ([succeedTest], True)
equalityBody [] [] _ = shouldnt "trying to generate = test with no constructors"
equalityBody _ _ (Bits _) = ([simpleEqualityTest],True)
equalityBody consts [] _ = ([equalityConsts consts],True)
equalityBody consts nonconsts _ =
    -- decide whether $left is const or non const, and handle accordingly
    ([Unplaced $ Cond (comparison "ult"
                         (lpvmCastExp (varGet "$left") intType)
                         (iVal $ length consts))
                [equalityConsts consts]
                [equalityNonconsts (content <$> nonconsts) (List.null consts)]],
     -- Decide to inline if only 1 non-const constructor, no non-const
     -- constructors (so not recursive), and at most 4 fields
     case List.map content nonconsts of
         [ProcProto _ params _ ] -> length params <= 4 && List.null consts
         _ -> False
        )


-- |Return code to check if two const values values are equal, given that we
--  know that the $left value is a const.
equalityConsts :: [Placed ProcProto] -> Placed Stmt
equalityConsts [] = failTest
equalityConsts _  = simpleEqualityTest


-- |An equality test that just compares $left and $right for identity
simpleEqualityTest :: Placed Stmt
simpleEqualityTest = comparison "eq" (varGet "$left") (varGet "$right")


-- |Return code to check that two values are equal when the first is known
--  not to be a const constructor.  The first argument is the list of
--  nonconsts, second is the list of consts.
equalityNonconsts :: [ProcProto] -> Bool -> Placed Stmt
equalityNonconsts [] _ =
    shouldnt "type with no non-const constructors should have been handled"
equalityNonconsts [ProcProto name params _] noConsts =
    -- single non-const and no const constructors:  just compare fields
    let detism = if noConsts then Det else SemiDet
    in  Unplaced $ And ([deconstructCall name "$left" params detism,
                        deconstructCall name "$right" params detism]
                        ++ concatMap equalityField params)
equalityNonconsts ctrs _ =
    equalityMultiNonconsts ctrs


-- |Return code to check that two values are equal when the first is known
--  not to be a const constructor specifically for a type with multiple
--  nonconst constructors.  This generates nested conditions testing
--  $left against each possible constructor; if it matches, it tests
--  that $right is also that constructor and all the fields match; if
--  it doesn't match, it tests the next possible constructor, etc.
equalityMultiNonconsts :: [ProcProto] -> Placed Stmt
equalityMultiNonconsts [] = failTest
equalityMultiNonconsts (ProcProto name params _:ctrs) =
    Unplaced
     $ Cond (deconstructCall name "$left" params SemiDet)
        [Unplaced $ And ([deconstructCall name "$right" params SemiDet]
                         ++ concatMap equalityField params)]
        [equalityMultiNonconsts ctrs]

-- |Return code to deconstruct
deconstructCall :: Ident -> Ident -> [Param] -> Determinism -> Placed Stmt
deconstructCall ctor arg params detism =
    Unplaced $ ProcCall [] ctor Nothing detism False
     $ List.map (\p -> Unplaced $ varSet $ arg++"$"++paramName p) params
        ++ [Unplaced $ varGet arg]


-- |Return code to check that one field of two data are equal, when
--  they are known to have the same constructor.
equalityField :: Param -> [Placed Stmt]
equalityField param =
    let field = paramName param
        leftField = "$left$"++field
        rightField = "$right$"++field
    in  [Unplaced $ ProcCall [] "=" Nothing SemiDet False
            [Unplaced $ varGet leftField,
             Unplaced $ varGet rightField]]

-- |Log a message about normalised input items.
logNormalise :: String -> Compiler ()
logNormalise = logMsg Normalise
