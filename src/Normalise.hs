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
    when useStdLib $ addImport ["wybe"] (ImportSpec (Just Set.empty) Nothing)
    return ()


----------------------------------------------------------------
-- Normalising a module item
--
-- This only handles what can be handled without having loaded dependencies.
----------------------------------------------------------------

-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) (TypeRepresentation rep)
              items pos) = do
    let items' =
            [ModuleParamsDecl params pos | not $ List.null params]
            ++ [RepresentationDecl rep pos] ++ items
    normaliseSubmodule name vis pos items'
normaliseItem (TypeDecl vis (TypeProto name params) (TypeCtors ctorVis ctors)
              items pos) = do
    let items' =
            [ModuleParamsDecl params pos | not $ List.null params]
            ++ [ConstructorDecl ctorVis ctors] ++ items
    normaliseSubmodule name vis pos items'
normaliseItem (ModuleDecl vis name items pos) =
    normaliseSubmodule name vis pos items
normaliseItem (ModuleParamsDecl params pos) =
    addParameters params pos
normaliseItem (RepresentationDecl rep pos) =
    addTypeRep rep pos
normaliseItem (ConstructorDecl ctorVis ctors) =
    mapM_ (addConstructor ctorVis) ctors
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
    Just val -> normaliseItem (StmtDecl (ProcCall [] "=" Nothing Det False
                                         [Unplaced $ varSet name, val]) pos)
normaliseItem (FuncDecl vis mods (ProcProto name params resources)
                        resulttype result pos) =
  let flowType = Implicit pos
  in  normaliseItem
        (ProcDecl vis mods
            (ProcProto name (params ++ [Param "$" resulttype ParamOut flowType])
                       resources)
             [maybePlace (ForeignCall "llvm" "move" []
                 [maybePlace (Typed (content result) resulttype False)
                  $ place result,
                  Unplaced
                  $ Typed (Var "$" ParamOut flowType) resulttype False])
              pos]
        pos)
normaliseItem item@(ProcDecl _ _ _ _ _) = do
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

completeNormalisation :: [ModSpec] -> Compiler ()
completeNormalisation mods = do
    logNormalise $ "Completing normalisation of modules " ++ showModSpecs mods
    completeTypeNormalisation mods
    mapM_ (normaliseModMain `inModule`) mods


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
    typeDefMembers :: [Placed ProcProto],     -- high level representation
    typeDefMemberVis :: Visibility            -- are members public?
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
--     ++ showMaybeSourcePos pos


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
    ctorsVis <- (reverse . trustFromJust "modTypeDeps")
               <$> getModuleImplementationField modConstructors
    -- XXX should pull visibility out of list
    let vis = fst $ head ctorsVis
    ctors <- mapM (placedApply resolveCtorTypes . snd) ctorsVis
    let deps = List.filter (`Set.member` modSet)
               $ concatMap 
                 (((typeModule . paramType) <$>) . procProtoParams . content)
                 ctors
    return ((tyMod, TypeDef tyParams ctors vis), tyMod, deps)


-- | Resolve constructor argument types.
resolveCtorTypes :: ProcProto -> OptPos -> Compiler (Placed ProcProto)
resolveCtorTypes proto pos = do
    params <- mapM (resolveParamType pos) $ procProtoParams proto
    return $ maybePlace (proto { procProtoParams = params }) pos


-- | Resolve the type of a parameter
resolveParamType :: OptPos -> Param -> Compiler Param
resolveParamType pos param@Param{paramType=ty} = do
    maybeTy <- lookupType ty pos
    case maybeTy of
        Nothing -> do errmsg pos $ "Unknown type " ++ show ty
                      return param
        Just ty' -> return $ param {paramType=ty'}


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
           ctorInfoName  :: ProcName,  -- ^ this constructor's name
           ctorInfoParams:: [(Param,TypeRepresentation,Int)],
                                       -- ^ params of this ctor, with their
                                       -- representation and bit size
           ctorInfoPos   :: OptPos,    -- ^ file position of ctor
           ctorInfoTag   :: Int,       -- ^ this constructor's tag
           ctorInfoBits  :: Int        -- ^ min number of bits needed
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
completeType modspec (TypeDef params ctors ctorVis) = do
    logNormalise $ "Completing type " ++ showModSpec modspec
    when (List.null ctors)
      $ shouldnt $ "completeType with no constructors: " ++ show modspec
    reenterModule modspec
    let (constCtors,nonConstCtors) =
            List.partition (List.null . procProtoParams . content) $ ctors
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
    -- XXX if numNonConsts == 0, then we could handle more consts.
    when (numConsts >= fromIntegral smallestAllocatedAddress)
      $ nyi $ "Type '" ++ show modspec ++ "' has too many constant constructors"
    -- XXX remove name from TypeSpec, and add type variable as an alternative ctor
    let typespec = TypeSpec (init modspec) (last modspec)
                   $ List.map (\n->TypeSpec [] n []) params
    let constItems =
          concatMap (constCtorItems ctorVis typespec) $ zip constCtors [0..]
    infos <- zipWithM nonConstCtorInfo nonConstCtors [0..]
    (reps,nonconstItemsList) <-
         unzip <$> mapM
         (nonConstCtorItems ctorVis typespec numConsts numNonConsts
          tagBits tagLimit)
         infos
    let rep = typeRepresentation reps numConsts
    extraItems <- implicitItems typespec constCtors nonConstCtors rep
    logNormalise $ "Representation of type " ++ showModSpec modspec
                   ++ " is " ++ show rep
    setTypeRep rep
    normalise $ constItems ++ concat nonconstItemsList ++ extraItems
    reexitModule
    return ()


-- | Analyse the representation of a single constructor, determining the
--   representation of its members, its total size in bits (assuming it is
--   *not* boxed, so each member takes the minimum number of bits), and its
--   total size in bytes (assuming it is boxed, so each member takes an
--   integral number of bytes).
nonConstCtorInfo :: Placed ProcProto -> Int -> Compiler CtorInfo
nonConstCtorInfo placedProto tag = do
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
    return $ CtorInfo name typeReps pos tag bitSize



fixParamType :: OptPos -> Param -> Compiler Param
fixParamType pos param = do
    let ty = paramType param
    ty' <- lookupType ty pos
    when (isNothing ty') (message Error ("Unknown type " ++ show ty) pos)
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
      normaliseItem (ProcDecl Public detModifiers (ProcProto "" [] resources)
                      (List.reverse stmts) Nothing)

-- |The resources available at the top level of this module
initResources :: Compiler (Set ResourceFlowSpec)
initResources = do
    mods <- getModuleImplementationField (Map.keys . modImports)
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


-- |Given a type implementation, return the low-level type, the visibility
--  of its constructors, and the constructors divided into constant (arity 0)
--  and non-constant ones.
normaliseTypeImpln :: TypeImpln
                   -> (Maybe TypeRepresentation,Visibility,[Placed ProcProto])
normaliseTypeImpln (TypeRepresentation rep) =
    (Just rep, Private, [])
normaliseTypeImpln (TypeCtors vis ctors) =
    (Nothing, vis, ctors)


-- |All items needed to implement a const contructor for the specified type.
constCtorItems :: Visibility -> TypeSpec -> (Placed ProcProto,Integer) -> [Item]
constCtorItems  vis typeSpec (placedProto,num) =
    let (proto,pos) = unPlace placedProto
        constName = procProtoName proto
    in [ProcDecl vis inlineDetModifiers
        (ProcProto constName [Param "$" typeSpec ParamOut Ordinary] Set.empty)
        [lpvmCastToVar (castTo (iVal num) typeSpec) "$"] pos
       ]


-- |All items needed to implement a non-const contructor for the specified type.
nonConstCtorItems :: Visibility -> TypeSpec -> Int -> Int -> Int -> Int
                  -> CtorInfo -> Compiler (TypeRepresentation,[Item])
nonConstCtorItems vis typeSpec numConsts numNonConsts tagBits tagLimit
                  info@(CtorInfo ctorName paramsReps pos tag bits) = do
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
                 tag tagLimit pos fields size
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
    in [ProcDecl Public inlineDetModifiers proto
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
                   -> [(Ident,TypeSpec,TypeRepresentation,Int)] -> Int -> [Item]
deconstructorItems ctorName typeSpec numConsts numNonConsts tag tagLimit
                   pos fields size =
    let startOffset = (if tag > tagLimit then tagLimit+1 else tag) in
    let flowType = Implicit pos
        detism = deconstructorDetism numConsts numNonConsts
    in [ProcDecl Public (inlineModifier detism)
        (ProcProto ctorName
         (List.map (\(n,t,_,_) -> (Param n t ParamOut Ordinary)) fields
          ++ [Param "$" typeSpec ParamIn Ordinary])
         Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag tagLimit (Just size) "$"]
         -- Code to fetch all the fields
         ++ List.map (\(var,_,_,aligned) ->
                              (Unplaced $ ForeignCall "lpvm" "access" []
                               [Unplaced $ Var "$" ParamIn flowType,
                                Unplaced $ iVal (aligned - startOffset),
                                Unplaced $ iVal size,
                                Unplaced $ iVal startOffset,
                                Unplaced $ Var var ParamOut flowType]))
            fields)
        pos]


-- |Generate the needed Test statements to check that the tag of the value
--  of the specified variable matches the specified tag.  If not checking
--  is necessary, just generate a Nop, rather than a true test.
tagCheck :: Int -> Int -> Int -> Int -> Maybe Int -> Ident -> Placed Stmt
tagCheck numConsts numNonConsts tag tagLimit size varName =
    let startOffset = (if tag > tagLimit then tagLimit+1 else tag) in
    -- If there are any constant constructors, be sure it's not one of them
    let tests =
          (case numConsts of
               0 -> []
               _ -> [comparison "icmp_uge"
                     (varGet varName)
                     (intCast $ iVal numConsts)]
           ++
           -- If there is more than one non-const constructors, check that
           -- it's the right one
           (case numNonConsts of
               1 -> []  -- Nothing to do if it's the only non-const constructor
               _ -> [comparison "icmp_eq"
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
                  Unplaced $ iVal (0 - startOffset),
                  Unplaced $ iVal $ trustFromJust
                             "unboxed type shouldn't have a secondary tag" size,
                  Unplaced $ iVal startOffset,
                  Unplaced $ varSet "$tag"],
                 comparison "icmp_eq" (varGet "$tag") (iVal tag)]
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
    let startOffset = (if tag > tagLimit then tagLimit+1 else tag) in
    let detism = deconstructorDetism numConsts numNonConsts
        -- Set the "noalias" flag when all other fields (exclude the one
        -- that is being changed) in this struct aren't [Address].
        -- This flag is used in [AliasAnalysis.hs]
        otherPtrCount = if rep == Address then ptrCount-1 else ptrCount
        flags = if otherPtrCount == 0 then ["noalias"] else []
    in [-- The getter:
        ProcDecl vis (inlineModifier detism)
        (ProcProto field [Param "$rec" rectype ParamIn Ordinary,
                          Param "$" fieldtype ParamOut Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag tagLimit (Just size) "$rec"]
         ++
        -- Code to access the selected field
         [Unplaced $ ForeignCall "lpvm" "access" []
          [Unplaced $ varGet "$rec",
           Unplaced $ iVal (offset - startOffset),
           Unplaced $ iVal size,
           Unplaced $ iVal startOffset,
           Unplaced $ varSet "$"]])
        pos,
        -- The setter:
        ProcDecl vis (inlineModifier detism)
        (ProcProto field [Param "$rec" rectype ParamInOut Ordinary,
                          Param "$field" fieldtype ParamIn Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag tagLimit (Just size) "$rec"]
         ++
        -- Code to mutate the selected field
         [Unplaced $ ForeignCall "lpvm" "mutate" flags
          [Unplaced $ Typed (Var "$rec" ParamInOut $ Implicit pos)
                      rectype False,
           Unplaced $ iVal (offset - startOffset),
           Unplaced $ iVal 0,    -- May be changed to 1 by CTGC transform
           Unplaced $ iVal size,
           Unplaced $ iVal startOffset,
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
    in [ProcDecl vis inlineDetModifiers proto
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
        detism = deconstructorDetism numConsts numNonConsts
    in [ProcDecl vis (inlineModifier detism)
        (ProcProto ctorName
         (List.map (\(n,fieldType,_,_) -> (Param n fieldType ParamOut Ordinary))
          fields
          ++ [Param "$" recType ParamIn Ordinary])
         Set.empty)
         -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag (wordSizeBytes-1) Nothing "$"]
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
    let detism = deconstructorDetism numConsts numNonConsts
        fieldMask = (bit sz::Int) - 1
        shiftedHoleMask = complement $ fieldMask `shiftL` shift
    in [-- The getter:
        ProcDecl vis (inlineModifier detism)
        (ProcProto field [Param "$rec" recType ParamIn Ordinary,
                          Param "$" fieldType ParamOut Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag (wordSizeBytes-1) Nothing "$rec"]
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
        ProcDecl vis (inlineModifier detism)
        (ProcProto field [Param "$rec" recType ParamInOut Ordinary,
                          Param "$field" fieldType ParamIn Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck numConsts numNonConsts tag (wordSizeBytes-1) Nothing "$rec"]
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


deconstructorDetism :: Int -> Int -> Determinism
deconstructorDetism numConsts numNonConsts
    | numConsts + numNonConsts > 1 = SemiDet
    | otherwise                    = Det

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
implicitItems typespec consts nonconsts rep = do
    eq <- implicitEquality typespec consts nonconsts rep
    dis <- implicitDisequality typespec consts nonconsts rep
    return $ eq ++ dis
    -- XXX add comparison, print, display, maybe prettyprint, and lots more


implicitEquality :: TypeSpec -> [Placed ProcProto] -> [Placed ProcProto]
                 -> TypeRepresentation -> Compiler [Item]
implicitEquality typespec consts nonconsts rep = do
    defs <- lookupProc "="
    -- XXX should verify that it's an arity 2 test with two inputs of the right type
    if isJust defs
    then return [] -- don't generate if user-defined
    else do
      let eqProto = ProcProto "=" [Param "$left" typespec ParamIn Ordinary,
                                   Param "$right" typespec ParamIn Ordinary]
                    Set.empty
      let (body,inline) = equalityBody consts nonconsts rep
      return [ProcDecl Public (setInline inline $ setDetism SemiDet detModifiers)
                   eqProto body Nothing]



implicitDisequality :: TypeSpec -> [Placed ProcProto] -> [Placed ProcProto]
                    -> TypeRepresentation -> Compiler [Item]
implicitDisequality typespec consts nonconsts _ = do
    defs <- lookupProc "/="
    if isJust defs
    then return [] -- don't generate if user-defined
    else do
      let neProto = ProcProto "/=" [Param "$left" typespec ParamIn Ordinary,
                                     Param "$right" typespec ParamIn Ordinary]
                    Set.empty
      let neBody = [Unplaced $ Not $ Unplaced $
                    ProcCall [] "=" Nothing SemiDet False
                    [Unplaced $ varGet "$left", Unplaced $ varGet "$right"]]
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
equalityBody :: [Placed ProcProto] -> [Placed ProcProto] -> TypeRepresentation
             -> ([Placed Stmt],Inlining)
-- Special case for phantom (void) types
equalityBody _ _ (Bits 0) = ([succeedTest], Inline)
equalityBody [] [] _ = shouldnt "trying to generate = test with no constructors"
equalityBody _ _ (Bits _) = ([simpleEqualityTest],Inline)
equalityBody consts [] _ = ([equalityConsts consts],Inline)
equalityBody consts nonconsts _ =
    -- decide whether $left is const or non const, and handle accordingly
    ([Unplaced $ Cond (comparison "icmp_uge"
                         (castTo (varGet "$left") intType)
                         (iVal $ length consts))
                [equalityNonconsts (content <$> nonconsts) (List.null consts)]
                [equalityConsts consts]
                Nothing],
     -- Decide to inline if only 1 non-const constructor, no non-const
     -- constructors (so not recursive), and at most 4 fields
     case List.map content nonconsts of
         [ProcProto _ params _ ] | length params <= 4 && List.null consts ->
              Inline
         _ -> MayInline
        )


-- |Return code to check if two const values values are equal, given that we
--  know that the $left value is a const.
equalityConsts :: [Placed ProcProto] -> Placed Stmt
equalityConsts [] = failTest
equalityConsts _  = simpleEqualityTest


-- |An equality test that just compares $left and $right for identity
simpleEqualityTest :: Placed Stmt
simpleEqualityTest = comparison "icmp_eq" (varGet "$left") (varGet "$right")


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
        [equalityMultiNonconsts ctrs] Nothing

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


inlineModifier :: Determinism -> ProcModifiers
inlineModifier detism = setInline Inline $ setDetism detism detModifiers


inlineDetModifiers :: ProcModifiers
inlineDetModifiers = setInline Inline detModifiers


inlineSemiDetModifiers :: ProcModifiers
inlineSemiDetModifiers = inlineModifier SemiDet


-- |Log a message about normalised input items.
logNormalise :: String -> Compiler ()
logNormalise = logMsg Normalise
