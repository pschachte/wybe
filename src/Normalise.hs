{-# OPTIONS -XTupleSections #-}
--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri Jan  6 11:28:23 2012
--  Purpose  : Convert parse tree into AST
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

-- |Support for normalising wybe code as parsed to a simpler form
--  to make compiling easier.
module Normalise (normalise, normaliseItem, completeNormalisation) where

import AST
import Config (wordSize, wordSizeBytes, tagMask, smallestAllocatedAddress)
import Control.Monad
import Control.Monad.State (gets)
import Control.Monad.Trans (lift,liftIO)
import Data.List as List
import Data.Map as Map
import Data.Maybe
import Data.Set as Set
import Flatten
import Options (LogSelection(Normalise))
import Snippets

-- |Normalise a list of file items, storing the results in the current module.
normalise :: [Item] -> Compiler ()
normalise items = do
    mapM_ normaliseItem items
    -- import stdlib unless no_standard_library pragma is specified
    useStdLib <- getModuleImplementationField (Set.notMember NoStd . modPragmas)
    when useStdLib $ addImport ["wybe"] (ImportSpec (Just Set.empty) Nothing)
    return ()


-- |Do whatever part of normalisation cannot be done until dependencies
--  have been loaded.  Currently that means generation of main proc for
--  the module, which needs to know what resources are available.
completeNormalisation :: Compiler ()
completeNormalisation = do
    normaliseModMain


----------------------------------------------------------------
-- Generating top-level code for a module

normaliseModMain :: Compiler ()
normaliseModMain = do
    stmts <- getModule stmtDecls
    logNormalise $ "Completing normalisation with top-level statements "
                   ++ show stmts
    unless (List.null stmts) $ do
      resources <- initResources
      normaliseItem (ProcDecl Public Det False (ProcProto "" [] resources)
                      (List.reverse stmts) Nothing)

-- |The resources available at the top level of this module
initResources :: Compiler (Set ResourceFlowSpec)
initResources = do
    mods <- getModuleImplementationField (Map.keys . modImports)
    mods' <- ((mods ++) . concat) <$> mapM descendentModules mods
    logNormalise $ "in initResources, mods = " ++ show mods'
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
-- Normalising a module item
--
-- This only handles what can be handled without having loaded dependencies.
----------------------------------------------------------------

-- |Normalise a single file item, storing the result in the current module.
normaliseItem :: Item -> Compiler ()
normaliseItem (TypeDecl vis (TypeProto name params) rep items pos)
  = do
    let (rep', ctorVis, consts, nonconsts) = normaliseTypeImpln rep
    ty <- addType name
          (TypeDef (length params) rep' (consts++nonconsts) ctorVis pos) vis
    modspec <- getModuleSpec
    let typespec = TypeSpec modspec name
                   $ List.map (\n->TypeSpec [] n []) params
    let constCount = length consts
    let nonConstCount = length nonconsts
    -- XXX Handle these cases by boxing the const constructors and by
    --     boxing the extra non-const constructors
    when (constCount >= fromIntegral smallestAllocatedAddress)
        $ nyi $ "Type '" ++ name ++ "' has too many constant constructors"
    when (nonConstCount > tagMask)
        $ nyi $ "Type '" ++ name ++ "' has too many non-constant constructors"
    updateImplementation (\imp -> imp { modConstCtorCount = constCount,
                                        modNonConstCtorCount = nonConstCount })
    let constItems =
          concatMap (constCtorItems ctorVis typespec) $ zip consts [0..]
    nonconstItems <- fmap concat $
           mapM (nonConstCtorItems ctorVis typespec constCount nonConstCount)
           $ zip nonconsts [0..]
    let extraItems = implicitItems typespec consts nonconsts items
    normaliseSubmodule name (Just params) vis pos
      $ constItems ++ nonconstItems ++ items ++ extraItems
normaliseItem (ModuleDecl vis name items pos) = do
    normaliseSubmodule name Nothing vis pos items
normaliseItem (ImportMods vis modspecs pos) = do
    mapM_ (\spec -> addImport spec (importSpec Nothing vis)) modspecs
normaliseItem (ImportItems vis modspec imports pos) = do
    addImport modspec (importSpec (Just imports) vis)
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



normaliseSubmodule :: Ident -> Maybe [Ident] -> Visibility -> OptPos ->
                      [Item] -> Compiler ()
normaliseSubmodule name typeParams vis pos items = do
    dir <- getDirectory
    parentModSpec <- getModuleSpec
    let subModSpec = parentModSpec ++ [name]
    logNormalise $ "Normalising submodule " ++ showModSpec subModSpec
    addImport subModSpec (importSpec Nothing vis)
    -- Add the submodule to the submodule list of the implementation
    updateImplementation $
        updateModSubmods (\sm-> Map.insert name subModSpec sm)
    enterModule dir subModSpec (Just parentModSpec) typeParams
    -- submodule always imports parent module
    addImport parentModSpec (importSpec Nothing Private)
    case typeParams of
      Nothing -> return ()
      Just _ ->
        updateImplementation
        (\imp ->
          let set = Set.singleton $ TypeSpec parentModSpec name []
          in imp { modKnownTypes = Map.insert name set $ modKnownTypes imp })
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
    return ()



----------------------------------------------------------------
--                Generating code for type declarations
----------------------------------------------------------------


-- |Given a type implementation, return the low-level type, the visibility
--  of its constructors, and the constructors divided into constant (arity 0)
--  and non-constant ones.
normaliseTypeImpln :: TypeImpln ->
                      (Maybe TypeRepresentation,Visibility,
                       [Placed ProcProto],[Placed ProcProto])
normaliseTypeImpln (TypeRepresentation repName) =
    (Just $ normaliseTypeRepresntation repName, Private, [], [])
normaliseTypeImpln (TypeCtors vis ctors) =
    let (constCtrs,nonConstCtrs) =
            List.partition (List.null . procProtoParams . content) ctors
    in (Just (if List.null nonConstCtrs
              then "i" ++
               (show $ ceiling $ logBase 2 $ fromIntegral $ length constCtrs)
              else "pointer"),
        vis,constCtrs,nonConstCtrs)


normaliseTypeRepresntation :: String -> String
normaliseTypeRepresntation "int" = "i" ++ show wordSize
normaliseTypeRepresntation "float" = "f" ++ show wordSize
normaliseTypeRepresntation "double" = "f64"
normaliseTypeRepresntation other = other


-- |Generate an assignment proc (a definition of '=')
assignmentProc :: TypeSpec -> Bool -> Item
assignmentProc ty leftToRight =
    let (lname,lflow,rname,rflow)
            = if leftToRight
              then ("in", ParamIn,"out", ParamOut)
              else ("out", ParamOut,"in", ParamIn)
    in ProcDecl Public Det True
       (ProcProto "=" [Param lname ty lflow Ordinary,
                       Param rname ty rflow Ordinary] Set.empty)
       [move (varGet "in") (varSet "out")]
       Nothing


-- |All items needed to implement a const contructor for the specified type.
constCtorItems :: Visibility -> TypeSpec -> (Placed ProcProto,Integer) -> [Item]
constCtorItems  vis typeSpec (placedProto,num) =
    let pos = place placedProto
        constName = procProtoName $ content placedProto
    in [ProcDecl vis Det True
        (ProcProto constName [Param "$" typeSpec ParamOut Ordinary] Set.empty)
        [lpvmCastToVar (castTo (IntValue num) typeSpec) "$"] pos
       ]


-- |All items needed to implement a non-const contructor for the specified type.
-- XXX need to handle the case of too many constructors for the number of tag
-- bits available
nonConstCtorItems :: Visibility -> TypeSpec -> Int -> Int
                  -> (Placed ProcProto,Integer) -> Compiler [Item]
nonConstCtorItems vis typeSpec constCount nonConstCount (placedProto,tag) = do
    let pos = place placedProto
    let ctorName = procProtoName $ content placedProto
    let params = procProtoParams $ content placedProto
    -- fields <- mapM (\(Param var typ _ _) -> fmap (var,typ,) $ fieldSize typ)
    fields <- mapM (\(Param var typ _ _) -> do
                       maybeSpec <- lookupType typ pos
                       maybeRep <- if isJust maybeSpec
                         then lookupTypeRepresentation $ fromJust maybeSpec
                         else return Nothing
                       let rep = fromMaybe "pointer" maybeRep
                       sz  <- fieldSize typ
                       return (var,typ,rep,sz))
              params
    let ptrCount = length
                   $ List.filter (\(_,_,rep,_) -> rep == "pointer") fields
    let (fields',size) =
          List.foldl (\(lst,offset) (var,typ,rep,sz) ->
                       let aligned = alignOffset offset sz
                       in (((var,typ,rep,aligned):lst),aligned + sz))
          ([],0) fields
    return
      $ constructorItems ctorName params typeSpec size fields' tag pos
      ++ deconstructorItems ctorName params typeSpec constCount nonConstCount
         fields' tag pos
      ++ concatMap (getterSetterItems vis typeSpec ctorName pos
                    constCount nonConstCount ptrCount size tag) fields'


-- |The number of bytes occupied by a value of the specified type.  If the
--  type is boxed, this is the word size.
fieldSize :: TypeSpec -> Compiler Int
-- XXX Generalise to allow non-word size fields
fieldSize _ = return wordSizeBytes

-- |The number of bytes occupied by a value of the specified type.  This is
--  the actual size of a value of the type, regardless of boxing.
-- typeSize :: TypeSpec -> Compiler Int


-- |Given a tentative offset into a structure and the size of the thing at
--  that offset, return the appropriate actual offset based on the size.
--  Our approach is never to align anything on more than a word size
--  boundary, anything bigger than that is aligned to the word size.
--  For smaller things
alignOffset :: Int -> Int -> Int
alignOffset offset size =
    let alignment = if size > wordSizeBytes
                    then wordSizeBytes
                    else fromJust $ find ((0==) . (size`mod`)) $
                         reverse $ List.map (2^)
                         [0..floor $ logBase 2 $ fromIntegral wordSizeBytes]
    in ((offset + alignment - 1) `div` alignment) * alignment


-- |Generate constructor code for a non-const constructor
constructorItems :: Ident -> [Param] -> TypeSpec -> Int
                 -> [(Ident,TypeSpec,TypeRepresentation,Int)] -> Integer
                 -> OptPos -> [Item]
constructorItems ctorName params typeSpec size fields tag pos =
    let flowType = Implicit pos
    in [ProcDecl Public Det True
        (ProcProto ctorName (params++[Param "$" typeSpec ParamOut Ordinary])
         Set.empty)
       -- Code to allocate memory for the value
        ([Unplaced $ ForeignCall "lpvm" "alloc" []
          [Unplaced $ IntValue $ fromIntegral size,
           Unplaced $ Typed (varSet "$rec") typeSpec True]]
         ++
       -- Code to fill all the fields
         (reverse $ List.map (\(var,_,_,aligned) ->
                               (Unplaced $ ForeignCall "lpvm" "mutate" []
                                [Unplaced $ Typed
                                   (Var "$rec" ParamInOut flowType)
                                   typeSpec True,
                                 Unplaced $ IntValue $ fromIntegral aligned,
                                 Unplaced $ IntValue $ 1,
                                 Unplaced $ IntValue $ fromIntegral size,
                                 Unplaced $ IntValue $ 0,
                                 Unplaced $ Var var ParamIn flowType]))
          fields)
         ++
       -- Finally, code to tag the reference and cast to the right type
         [Unplaced $ ForeignCall "llvm" "or" []
          [Unplaced $ varGet "$rec",
           Unplaced $ IntValue $ fromIntegral tag,
           Unplaced $ intCast (varSet "$")]])
        pos]


-- |Generate deconstructor code for a non-const constructor
deconstructorItems :: Ident -> [Param] -> TypeSpec -> Int -> Int
                   -> [(Ident,TypeSpec,TypeRepresentation,Int)] -> Integer
                   -> OptPos -> [Item]
deconstructorItems ctorName params typeSpec constCount nonConstCount
    fields tag pos =
    -- XXX this needs to take the tag into account
    -- XXX this needs to be able to fail if the constructor doesn't match
    let flowType = Implicit pos
        detism = if constCount + nonConstCount > 1 then SemiDet else Det
    in [ProcDecl Public detism True
        (ProcProto ctorName
         (List.map (\(Param n t _ ft) -> (Param n t ParamOut ft)) params
          ++ [Param "$" typeSpec ParamIn Ordinary])
         Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck constCount nonConstCount tag "$"]
         ++
        -- Code to fetch all the fields
        reverse (List.map (\(var,_,_,aligned) ->
                              (Unplaced $ ForeignCall "lpvm" "access" []
                               [Unplaced $ Var "$" ParamIn flowType,
                                Unplaced $ IntValue
                                  $ fromIntegral aligned - tag,
                                Unplaced $ Var var ParamOut flowType]))
                 fields))
        pos]


-- |Generate the needed Test statements to check that the tag of the value
--  of the specified variable matches the specified tag.  If not checking
--  is necessary, just generate a Nop, rather than a true test.
tagCheck :: Int -> Int -> Integer -> Ident -> Placed Stmt
tagCheck constCount nonConstCount tag varName =
    -- If there are any constant constructors, be sure it's not one of them
    let tests =
          (case constCount of
               0 -> []
               _ -> [comparison "uge"
                     (varGet varName)
                     (intCast $ iVal constCount)]
           ++
           -- If there is more than one non-const constructors, check that
           -- it's the right one
           case nonConstCount of
               1 -> []  -- Nothing to do if it's the only non-const constructor
               _ -> [comparison "eq"
                     (intCast $ ForeignFn "llvm" "and" []
                      [Unplaced $ varGet varName,
                       Unplaced $ iVal tagMask])
                     (intCast $ iVal tag)])
    in if List.null tests
       then Unplaced Nop
       else seqToStmt tests


-- |Generate the needed statements to strip the specified tag off of the value
--  of the specified variable, placing the result in the second variable.
--  We use the stripped name with "$asInt" appended as a temp var name.
-- | Produce a getter and a setter for one field of the specified type.
getterSetterItems :: Visibility -> TypeSpec -> Ident -> OptPos
                    -> Int -> Int -> Int -> Int -> Integer
                    -> (VarName,TypeSpec,TypeRepresentation,Int) -> [Item]
getterSetterItems vis rectype ctorName pos constCount nonConstCount
    ptrCount size tag (field,fieldtype,rep,offset) =
    -- XXX generate cleverer code if multiple constructors have some of
    --     the same field names
    let detism = if constCount + nonConstCount == 1 then Det else SemiDet
        otherPtrCount = if rep == "pointer" then ptrCount-1 else ptrCount
        flags = if otherPtrCount == 0 then ["noalias"] else []
    in [ProcDecl vis detism True
        (ProcProto field [Param "$rec" rectype ParamIn Ordinary,
                          Param "$" fieldtype ParamOut Ordinary]
         Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck constCount nonConstCount tag "$rec"]
         ++
        -- Code to access the selected field
         [Unplaced $ ForeignCall "lpvm" "access" []
          [Unplaced $ varGet "$rec",
           Unplaced $ IntValue $ fromIntegral offset - tag,
           Unplaced $ varSet "$"]])
        pos,
        ProcDecl vis detism True
        (ProcProto field
         [Param "$rec" rectype ParamInOut Ordinary,
          Param "$field" fieldtype ParamIn Ordinary] Set.empty)
        -- Code to check we have the right constructor
        ([tagCheck constCount nonConstCount tag "$rec"]
         ++
        -- Code to mutate the selected field
         [Unplaced $ ForeignCall "lpvm" "mutate" flags
          [Unplaced $ Typed (Var "$rec" ParamInOut $ Implicit pos)
                      rectype False,
           Unplaced $ IntValue $ fromIntegral offset - tag,
           Unplaced $ IntValue 0,    -- May be changed to 1 by CTGC transform
           Unplaced $ IntValue $ fromIntegral size,
           Unplaced $ IntValue tag,
           Unplaced $ varGet "$field"]])
        pos]


----------------------------------------------------------------
--                     Generating implicit procs
--
-- Wybe automatically generates equality test procs if you don't write
-- your own definitions.  It should generate default implementations of
-- many more such procs.
--
----------------------------------------------------------------

implicitItems :: TypeSpec -> [Placed ProcProto] -> [Placed ProcProto] -> [Item]
                 -> [Item]
implicitItems typespec consts nonconsts items =
    implicitEquality typespec consts nonconsts items
    -- XXX add comparison, print, display, maybe prettyprint, and lots more


implicitEquality :: TypeSpec -> [Placed ProcProto] -> [Placed ProcProto] -> [Item]
                 -> [Item]
implicitEquality typespec consts nonconsts items =
    if List.any equalityTest items || consts==[] && nonconsts==[]
    then [] -- don't generate if user-defined or if no constructors at all
    else
      let proto = ProcProto "=" [Param "$left" typespec ParamIn Ordinary,
                                 Param "$right" typespec ParamIn Ordinary]
                  Set.empty
          (body,inline) = equalityBody consts nonconsts
      in [ProcDecl Public SemiDet inline proto body Nothing]

-- |Does the item declare an = test or function?
equalityTest :: Item -> Bool
equalityTest (ProcDecl _ SemiDet _ (ProcProto "=" [_,_] _) _ _) = True
equalityTest (FuncDecl _ Det _ (ProcProto "=" [_,_] _) ty _ _) =
    ty == boolType
equalityTest _ = False


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
equalityBody :: [Placed ProcProto] -> [Placed ProcProto] -> ([Placed Stmt],Bool)
equalityBody [] [] = shouldnt "trying to generate = test with no constructors"
equalityBody consts [] = ([equalityConsts consts],True)
equalityBody consts nonconsts =
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


-- |Return code to check of two const values values are equal, given that we
--  know that the $left value is a const.
equalityConsts :: [Placed ProcProto] -> Placed Stmt
equalityConsts [] = failTest
equalityConsts _ =
    comparison "eq" (intCast $ varGet "$left") (intCast $ varGet "$right")


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
