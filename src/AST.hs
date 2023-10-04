--  File     : AST.hs
--  Author   : Peter Schachte
--  Purpose  : Wybe Abstract Syntax Tree and LPVM representation
--  Copyright: (c) 2010-2019 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- |The abstract syntax tree, and supporting types and functions.
--  This includes the parse tree, as well as the AST types, which
--  are normalised versions of the parse tree types.
--
--  This also includes the Compiler monad and the Module types.
module AST (
  -- *Types just for parsing
  Item(..), Visibility(..), isPublic,
  Determinism(..), determinismLEQ, determinismJoin, determinismMeet,
  determinismFail, determinismSucceed,
  determinismSeq, determinismProceding, determinismName, determinismCanFail,
  impurityName, impuritySeq, expectedImpurity,
  inliningName,
  TypeProto(..), TypeModifiers(..), TypeSpec(..), typeVarSet, TypeVarName(..),
  genericType, higherOrderType, isHigherOrder,
  isResourcefulHigherOrder, typeModule,
  VarDict, TypeImpln(..),
  ProcProto(..), Param(..), TypeFlow(..),
  paramTypeFlow, primParamTypeFlow, setParamArgFlowType,
  paramToVar, primParamToArg, unzipTypeFlow, unzipTypeFlows,
  PrimProto(..), PrimParam(..), ParamInfo(..),
  Exp(..), StringVariant(..), GlobalInfo(..), Generator(..), Stmt(..), ProcFunctor(..),
  regularProc, regularModProc,
  flattenedExpFlow, expIsVar, expIsConstant, expVar, expVar', maybeExpType, innerExp,
  setExpFlowType,
  TypeRepresentation(..), TypeFamily(..), typeFamily,
  defaultTypeRepresentation, typeRepSize, integerTypeRep,
  defaultTypeModifiers,
  lookupTypeRepresentation, lookupModuleRepresentation,
  paramIsPhantom, argIsPhantom, typeIsPhantom, repIsPhantom,
  primProtoParamNames,
  protoRealParams, realParams, paramIsReal, paramIsNeeded,
  protoInputParamNames, protoRealParamsWhere, isProcProtoArg,
  -- *Source Position Types
  OptPos, Placed(..), place, betterPlace, content, maybePlace, rePlace, unPlace,
  placedApply, defaultPlacedApply, placedApplyM, contentApply, updatePlacedM,
  -- *AST types
  Module(..), isRootModule, ModuleInterface(..), ModuleImplementation(..), InterfaceHash, PubProcInfo(..),
  ImportSpec(..), importSpec, Pragma(..), addPragma,
  descendentModules, sameOriginModules,
  refersTo,
  enterModule, reenterModule, exitModule, reexitModule, inModule,
  emptyInterface, emptyImplementation,
  getParams, getPrimParams, getDetism, getProcDef, getProcPrimProto,
  mkTempName, updateProcDef, updateProcDefM,
  ModSpec, maybeModPrefix, ProcImpln(..), ProcDef(..), procInline, procCallCount,
  transformModuleProcs,
  getProcGlobalFlows,
  primImpurity, flagsImpurity, flagsDetism,
  AliasMap, aliasMapToAliasPairs, ParameterID, parameterIDToVarName,
  parameterVarNameToID, SpeczVersion, CallProperty(..), generalVersion,
  speczVersionToId, SpeczProcBodies,
  MultiSpeczDepInfo, CallSiteProperty(..), InterestingCallProperty(..),
  ProcAnalysis(..), emptyProcAnalysis,
  ProcBody(..), PrimFork(..), Ident, VarName,
  ProcName, ResourceDef(..), FlowDirection(..), showFlowName,
  argFlowDirection, argType, setArgType, setArgFlow, setArgFlowType, maybeArgFlowType,
  argDescription, argIntVal, trustArgInt, setParamType, paramIsResourceful,
  setPrimParamType, setTypeFlowType,
  flowsIn, flowsOut, primFlowToFlowDir, isInputFlow, isOutputFlow,
  foldStmts, foldExps, foldBodyPrims, foldBodyDistrib,
  expToStmt, seqToStmt, stmtsImpurity, stmtImpurity, procCallToExp,
  stmtsInputs, expOutputs, pexpListOutputs, expInputs, pexpListInputs,
  setExpTypeFlow, setPExpTypeFlow,
  Prim(..), primArgs, replacePrimArgs, 
  primGlobalFlows, argGlobalFlow, argsGlobalFlows, effectiveGlobalFlows, 
  argIsVar, argIsConst, argIntegerValue,
  varsInPrims, varsInPrim, varsInPrimArgs, varsInPrimArg,
  ProcSpec(..), PrimVarName(..), PrimArg(..), PrimFlow(..), ArgFlowType(..),
  CallSiteID, SuperprocSpec(..), initSuperprocSpec, -- addSuperprocSpec,
  maybeGetClosureOf, isClosureProc, isClosureVariant, isConstructorVariant,
  GlobalFlows(..), emptyGlobalFlows, univGlobalFlows, makeGlobalFlows,
  addGlobalFlow, hasGlobalFlow, globalFlowsUnion, globalFlowsUnions, globalFlowsIntersection,
  -- *Stateful monad for the compilation process
  MessageLevel(..), updateCompiler,
  CompilerState(..), Compiler, runCompiler,
  updateModules, updateImplementations, updateImplementation,
  updateTypeModifiers,
  addParameters, addTypeRep, setTypeRep, addConstructor,
  getModuleImplementationField, getModuleImplementation,
  getLoadedModule, getLoadingModule, updateLoadedModule, updateLoadedModuleM,
  getLoadedModuleImpln, updateLoadedModuleImpln, updateLoadedModuleImplnM,
  getModule, getModuleInterface, updateModule, getSpecModule,
  updateModImplementation, updateModImplementationM,
  addForeignImport, addForeignLib,
  updateModInterface, updateAllProcs, updateModSubmods, updateModProcs,
  getModuleSpec, moduleIsType, option,
  getOrigin, getSource, getDirectory,
  optionallyPutStr, message, errmsg, (<!>), prettyPos, Message(..), queueMessage,
  genProcName, addImport, doImport, importFromSupermodule, lookupType, lookupType',
  typeIsUnique,
  ResourceName, ResourceSpec(..), ResourceFlowSpec(..), ResourceImpln(..),
  initialisedResources,
  addSimpleResource, lookupResource,
  specialResources, specialResourcesSet, isSpecialResource,
  publicResource, resourcefulName,
  ProcModifiers(..), defaultProcModifiers,
  setDetism, setInline, setImpurity, setVariant,
  ProcVariant(..), Inlining(..), Impurity(..),
  addProc, addProcDef, lookupProc, publicProc, callTargets,
  specialChar, specialName, specialName2,
  outputVariableName, outputStatusName,
  envParamName, envPrimParam, makeGlobalResourceName,
  showBody, showPlacedPrims, showStmt, showBlock, showProcDef,
  showProcIdentifier, showProcName,
  showModSpec, showModSpecs, showResources, showOptPos, showProcDefs, showUse,
  shouldnt, nyi, checkError, checkValue, trustFromJust, trustFromJustM,
  flowPrefix, showProcModifiers, showProcModifiers', showFlags, showFlags',
  showMap, showVarMap, simpleShowMap, simpleShowSet, bracketList,
  maybeShow, showMessages, stopOnError,
  logMsg, whenLogging2, whenLogging,
  -- *Helper functions
  defaultBlock, moduleIsPackage,
  -- *LPVM Encoding types
  EncodedLPVM(..), makeEncodedLPVM
  ) where

import           Config (magicVersion, wordSize, objectExtension,
                         sourceExtension, currentModuleAlias)
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans (lift,liftIO)
import           Control.Monad.Trans.State
import           Crypto.Hash
import qualified Data.Binary
import qualified Data.ByteString.Lazy as BL
import           Data.List as List
import           Data.List.Extra (nubOrd,splitOn)
import           Data.Map as Map
import           Data.Maybe
import           Data.Set as Set
import           UnivSet as USet
import           Data.Tuple.HT ( mapSnd, mapFst )
import           Data.Word (Word8)
import           Text.Read (readMaybe)
import           Flow             ((|>))
import           Numeric          (showHex)
import           Options
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Directory (makeAbsolute, makeRelativeToCurrentDirectory)
-- import           Text.ParserCombinators.Parsec.Pos
import           Text.Parsec.Pos
                 ( SourcePos, sourceName, sourceColumn, sourceLine )
import           Util
import           System.Console.ANSI

import           GHC.Generics (Generic)

import qualified LLVM.AST as LLVMAST
import Data.Binary (Binary)

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

-- |An item appearing at the top level of a source file.
data Item
     = TypeDecl Visibility TypeProto TypeModifiers TypeImpln [Item] OptPos
     | ModuleDecl Visibility Ident [Item] OptPos
     | RepresentationDecl [Ident] TypeModifiers TypeRepresentation OptPos
     | ConstructorDecl Visibility [Ident] TypeModifiers [(Visibility, Placed ProcProto)]
                       OptPos
     | ImportMods Visibility [ModSpec] OptPos
     | ImportItems Visibility ModSpec [Ident] OptPos
     | ImportForeign [FilePath] OptPos
     | ImportForeignLib [Ident] OptPos
     | ResourceDecl Visibility ResourceName TypeSpec (Maybe (Placed Exp)) OptPos
       -- The Bool in the next two indicates whether inlining is forced
     | FuncDecl Visibility ProcModifiers ProcProto TypeSpec (Placed Exp) OptPos
     | ProcDecl Visibility ProcModifiers ProcProto [Placed Stmt] OptPos
     | StmtDecl Stmt OptPos
     | PragmaDecl Pragma
     deriving (Generic, Eq)

-- |The visibility of a file item.  We only support public and private.
data Visibility = Private | Public
                  deriving (Eq, Ord, Show, Generic)


-- |Determinism describes whether a statement can succeed or fail if execution
-- reaches a given program point.  Det means it will definitely succeed, Failure
-- means it will definitely fail, SemiDet means it could either succeed or fail,
-- and Terminal means it won't do either (so execution will not reach that
-- point).  This values form a lattice, with Terminal at the bottom, SemiDet at
-- the top, and Failure and Det incomparable values between them.
data Determinism = Terminal | Failure | Det | SemiDet
                  deriving (Eq, Ord, Show, Generic)


-- |Partial order less or equal for Determinism.
determinismLEQ :: Determinism -> Determinism -> Bool
determinismLEQ Failure Det = False
determinismLEQ det1 det2 = det1 <= det2


-- |Lattice meet for Determinism.  Probably not needed
determinismMeet :: Determinism -> Determinism -> Determinism
determinismMeet Failure Det = Terminal
determinismMeet Det Failure = Terminal
determinismMeet det1 det2 = min det1 det2


-- |Force the specified determinism to succeed, if it is reachable.
determinismSucceed :: Determinism -> Determinism
determinismSucceed Terminal = Terminal
determinismSucceed Failure  = Det
determinismSucceed Det      = Det
determinismSucceed SemiDet  = Det


-- |Force the specified determinism to fail, if it is reachable.
determinismFail  :: Determinism -> Determinism
determinismFail  Terminal = Terminal
determinismFail  Failure  = Failure
determinismFail  Det      = Failure
determinismFail  SemiDet  = Failure


-- |Lattice join for Determinism.
determinismJoin :: Determinism -> Determinism -> Determinism
determinismJoin Failure Det = SemiDet
determinismJoin Det Failure = SemiDet
determinismJoin det1 det2 = max det1 det2


-- |Determinism for ordered sequence of steps.  This is not the same as meet or
-- join, because nothing will be executed after a Failure, even a Terminal.
-- This operation is associative.
determinismSeq :: Determinism -> Determinism -> Determinism
determinismSeq Terminal _        = Terminal
determinismSeq Failure  _        = Failure
-- NonDet Failure = Failure
-- NonDet Terminal = Failure
determinismSeq _        Terminal = Terminal
determinismSeq _        Failure  = Failure
determinismSeq det1     det2     = max det1 det2


-- |Does this determinism reflect a state that could continue to the next
-- statement?
determinismProceding :: Determinism -> Bool
determinismProceding Terminal = False
determinismProceding Failure  = False
determinismProceding Det      = True
determinismProceding SemiDet  = True
-- NonDet = True


-- |A suitable printable name for each determinism.
determinismName :: Determinism -> String
determinismName Terminal = "terminal"
determinismName Failure  = "failing"
determinismName Det      = ""
determinismName SemiDet  = "test"
-- NonDet = "generator"

-- | Can the determinism fail?
determinismCanFail :: Determinism -> Bool
determinismCanFail Terminal = False
determinismCanFail Failure  = True
determinismCanFail Det      = False
determinismCanFail SemiDet  = True


-- | Internal representation of data
data TypeRepresentation
    = Address           -- ^ A pointer; occupies wordSize bits
    | Bits Int          -- ^ An unsigned integer representation
    | Signed Int        -- ^ A signed integer representation
    | Floating Int      -- ^ A floating point representation
    | Func [TypeRepresentation] [TypeRepresentation]
                        -- ^ A function pointer with inputs and outputs
    deriving (Eq, Ord, Generic)


-- | Type representation for opaque things
defaultTypeRepresentation :: TypeRepresentation
defaultTypeRepresentation = Bits wordSize


-- | How many bits a type representation occupies
typeRepSize :: TypeRepresentation -> Int
typeRepSize (Bits bits)     = bits
typeRepSize (Signed bits)   = bits
typeRepSize (Floating bits) = bits
typeRepSize (Func _ _)      = wordSize
typeRepSize Address         = wordSize


-- | The type representation is for a (signed or unsigned) integer type
integerTypeRep :: TypeRepresentation -> Bool
integerTypeRep (Bits bits)     = True
integerTypeRep (Signed bits)   = True
integerTypeRep _               = False


-- | Crude division of types useful for categorising primitive operations
data TypeFamily = IntFamily | FloatFamily
  deriving (Eq, Ord)


-- | Categorise a type representation as either int or float
typeFamily :: TypeRepresentation -> TypeFamily
typeFamily (Floating _) = FloatFamily
typeFamily _            = IntFamily


-- | Declared implementation of a type, either in terms of representation or by
--   listing constructors and having the compiler determine the representation.
data TypeImpln = TypeRepresentation TypeRepresentation
               | TypeCtors Visibility [(Visibility, Placed ProcProto)]
               deriving (Generic, Eq)


-- |Does the specified visibility make the item public?
isPublic :: Visibility -> Bool
isPublic = (==Public)


-- |A type prototype consists of a type name and zero or more type parameters.
data TypeProto = TypeProto Ident [Ident]
                 deriving (Generic, Eq)


-- | A type modifier consists of a boolean indicating its uniqueness.
data TypeModifiers = TypeModifiers {
    tmUniqueness :: Bool,     -- ^ Is the type required to be unique?
    tmUnknown :: [String]     -- ^ Unknown type modifiers specified
} deriving (Generic, Eq)


-- | A default boolean value for Uniqueness (false)
defaultTypeModifiers :: TypeModifiers
defaultTypeModifiers = TypeModifiers False []

----------------------------------------------------------------
--                    Handling Source Positions
----------------------------------------------------------------

-- |Optional source position.
type OptPos = Maybe SourcePos

-- |Some kind of value, with a source position optionally attached.
data Placed t
    = Placed t SourcePos
    | Unplaced t
    deriving (Eq, Ord, Generic)


-- |Return the optional position attached to a Placed value.
place :: Placed t -> OptPos
place (Placed _ pos) = Just pos
place (Unplaced _) = Nothing

-- |Return the optional position attached to a Placed value, if
-- present, or the provided optional pos otherwise.
betterPlace :: OptPos -> Placed t -> OptPos
betterPlace _ (Placed _ pos) = Just pos
betterPlace pos (Unplaced _) = pos

-- |Return the content of a Placed value.
content :: Placed t -> t
content (Placed content _) = content
content (Unplaced content) = content


-- |Attach a source position to a data value, if one is available.
maybePlace :: t -> OptPos -> Placed t
maybePlace t (Just pos) = Placed t pos
maybePlace t Nothing    = Unplaced t


-- |Replace the source position of the Placed value with the given position, if
-- one is given; otherwise leave the position it already has.
rePlace :: OptPos -> Placed t -> Placed t
rePlace Nothing    t            = t
rePlace (Just pos) (Placed t _) = Placed t pos
rePlace (Just pos) (Unplaced t) = Placed t pos


-- |Extract the place and payload of a Placed value
unPlace :: Placed t -> (t, OptPos)
unPlace (Placed x pos) = (x, Just pos)
unPlace (Unplaced x)   = (x, Nothing)


-- |Apply a function that takes a thing and an optional place to a
--  placed thing.
placedApply :: (a -> OptPos -> b) -> Placed a -> b
placedApply f placed = f (content placed) (place placed)


-- |Apply a function that takes a thing and an optional place to a placed thing.
--  Use the place attached to the placed thing, if there is one, otherwise use
--  the supplied default place.
defaultPlacedApply :: (a -> OptPos -> b) -> OptPos -> Placed a -> b
defaultPlacedApply f pos placed = f (content placed) (betterPlace pos placed)


-- |Apply a function that takes a thing and an optional place to a
--  placed thing.
placedApplyM :: Monad m => (a -> OptPos -> m b) -> Placed a -> m b
placedApplyM f placed = f (content placed) (place placed)


-- |Apply an operator to the content of a placed thing.
contentApply :: (a->b) -> Placed a -> Placed b
contentApply f (Placed a pos) = Placed (f a) pos
contentApply f (Unplaced a) = Unplaced $ f a



instance Functor Placed where
  fmap f (Placed x pos) = Placed (f x) pos
  fmap f (Unplaced x) = Unplaced $ f x


-- |Apply a monadic function to the payload of a Placed thing
updatePlacedM :: (Monad m) => (a -> m b) -> Placed a -> m (Placed b)
updatePlacedM fn (Placed content pos) = do
    content' <- fn content
    return $ Placed content' pos
updatePlacedM fn (Unplaced content) = do
    content' <- fn content
    return $ Unplaced content'

----------------------------------------------------------------
--                    Compiler monad
----------------------------------------------------------------

-- |The different kinds of compiler messages.
data MessageLevel = Informational | Warning | Error
                  deriving (Eq, Ord, Show)


-- |The state of a compilation, used by the Compiler monad.  Because
--  this language allows mutually recursive module dependencies,
--  compilation is bit tricky.  To compile a module and its
--  dependencies, we first load the module.  Then for each
--  dependency we have not yet compiled and are not already in the
--  process of compiling, we compile the dependency, and retain only
--  the module's interface (this avoids having the source or compiled
--  version of too many modules in memory at once).  Dependencies we
--  are in the process of compiling, we collect in a list.  Once we
--  finish compiling a module's dependencies, we compile the list of
--  that module's strongly-connected component collected while
--  compiling the module's dependencies.
data CompilerState = Compiler {
  options :: Options,            -- ^compiler options specified on command line
  tmpDir  :: FilePath,           -- ^tmp directory for this build
  msgs :: [Message],             -- ^warnings, error messages, and info messages
  errorState :: Bool,            -- ^whether or not we've seen any errors
  modules :: Map ModSpec Module, -- ^all known modules except what we're loading
  underCompilation :: [Module],  -- ^the modules in the process of being compiled
  unchangedMods :: Set ModSpec   -- ^record mods that are loaded from object
                                 --  and unchanged.
}

-- |The compiler monad is a state transformer monad carrying the
--  compiler state over the IO monad.
type Compiler = StateT CompilerState IO

-- |Run a compiler function from outside the Compiler monad.
runCompiler :: Options -> Compiler t -> IO t
runCompiler opts comp = evalStateT comp
                        (Compiler opts "" [] False Map.empty [] Set.empty)


-- |Apply some transformation function to the compiler state.
updateCompiler :: (CompilerState -> CompilerState) -> Compiler ()
updateCompiler updater = do
    state <- get
    put $ updater state

-- |Apply a monadic transformation function to the compiler state.
updateCompilerM :: (CompilerState -> Compiler CompilerState) -> Compiler ()
updateCompilerM updater = do
    state <- get
    state' <- updater state
    put state'

updateAllProcs :: (ProcDef -> ProcDef) -> Compiler ()
updateAllProcs fn =
    updateImplementations
    (\imp -> imp { modProcs = Map.map (List.map fn) $ modProcs imp })


-- |Return Just the specified module, if already loaded or currently
-- being loaded, otherwise Nothing.  Takes care to handle it if the
-- specified module is under compilation.
getLoadingModule :: ModSpec -> Compiler (Maybe Module)
getLoadingModule modspec = do
    underComp <- gets underCompilation
    case find ((==modspec) . modSpec) underComp of
      Just mod -> return $ Just mod
      Nothing  -> getLoadedModule modspec


-- |Return Just the specified module, if already fully loaded; else return
-- Nothing.
getLoadedModule :: ModSpec -> Compiler (Maybe Module)
getLoadedModule modspec = do
    logAST $ "Get loaded module " ++ showModSpec modspec
    maybeMod <- gets (Map.lookup modspec . modules)
    logAST $ if isNothing maybeMod then " got nothing!" else " worked"
    return maybeMod


-- |Apply the given function to the specified module, if it has been loaded;
-- does nothing if not.  Takes care to handle it if the specified
-- module is under compilation.
updateLoadedModule :: (Module -> Module) -> ModSpec -> Compiler ()
updateLoadedModule updater modspec = do
    underComp <- gets underCompilation
    let (found,underComp') =
            mapAccumL (\found m -> if not found && modSpec m == modspec
                                   then (True, updater m)
                                   else (found, m))
            False underComp
    if found
    then updateCompiler (\st -> st { underCompilation = underComp' })
    else updateCompiler (\st -> st { modules = Map.adjust updater modspec $
                                               modules st })


-- |Apply the given function to the specified module, if it has been loaded;
-- does nothing if not.  Takes care to handle it if the specified
-- module is under compilation.
updateLoadedModuleM :: (Module -> Compiler Module) -> ModSpec -> Compiler ()
updateLoadedModuleM updater modspec = do
    underComp <- gets underCompilation
    let (before,rest) = span ((/=modspec) . modSpec) underComp
    case rest of
      (mod:tail) -> do
                mod' <- updater mod
                let underComp' = before ++ (mod':tail)
                updateCompiler (\st -> st { underCompilation = underComp' })
      [] ->
          updateCompilerM
          (\st -> do
                let mods = modules st
                let maybeMod = Map.lookup modspec mods
                case maybeMod of
                    Nothing -> return st
                    Just mod -> do
                        mod' <- updater mod
                        return st { modules = Map.insert modspec mod' mods})


-- |Return the ModuleImplementation of the specified module.  An error
-- if the module is not loaded or does not have an implementation.
getLoadedModuleImpln :: ModSpec -> Compiler ModuleImplementation
getLoadedModuleImpln modspec = do
    mod <- trustFromJustM ("unknown module " ++ showModSpec modspec) $
           getLoadingModule modspec
    return $ trustFromJust ("unimplemented module " ++ showModSpec modspec) $
           modImplementation mod



-- |Return the ModuleImplementation of the specified module.  An error
-- if the module is not loaded or does not have an implementation.
updateLoadedModuleImpln :: (ModuleImplementation -> ModuleImplementation) ->
                           ModSpec -> Compiler ()
updateLoadedModuleImpln updater =
    updateLoadedModule (\m -> m { modImplementation =
                                      updater <$> modImplementation m })


-- |Return the ModuleImplementation of the specified module.  An error
-- if the module is not loaded or does not have an implementation.
--     (ModuleImplementation -> Compiler (ModuleImplementation, a)) ->
--     ModSpec -> Compiler a
updateLoadedModuleImplnM ::
    (ModuleImplementation -> Compiler ModuleImplementation) ->
    ModSpec -> Compiler ()
updateLoadedModuleImplnM updater =
    updateLoadedModuleM
    (\m -> do
        let maybeImpln = modImplementation m
        case maybeImpln of
            Nothing -> return m
            Just imp -> do
                updated <- updater imp
                return m { modImplementation = Just updated }
    )



-- |Apply some transformation to the map of compiled modules.
updateModules :: (Map ModSpec Module -> Map ModSpec Module) -> Compiler ()
updateModules updater =
    modify (\bs -> bs { modules = updater $ modules bs })

-- |Apply some transformation to the map of compiled modules.
updateImplementations :: (ModuleImplementation -> ModuleImplementation) ->
                         Compiler ()
updateImplementations updater =
    updateModules (Map.map (\m -> m { modImplementation =
                                       updater <$> modImplementation m }))

-- |Return the module currently being compiled.  The argument says where
-- this function is called from for error-reporting purposes.
-- |Return some function of the module currently being compiled.
getModule :: (Module -> t) -> Compiler t
getModule getter = do
    mods <- gets underCompilation
    case mods of
      [] -> shouldnt "getModule called when not currently compiling a module."
      (mod:_) -> return $ getter mod


-- |Transform the module currently being compiled.
updateModule :: (Module -> Module) -> Compiler ()
updateModule updater =
    modify (\comp ->
              case underCompilation comp of
                [] -> shouldnt "updateModule with no current module"
                (mod1:mods) -> comp { underCompilation = updater mod1:mods })


-- |Transform the module currently being compiled.
updateModuleM :: (Module -> Compiler Module) -> Compiler ()
updateModuleM updater =
    updateCompilerM
    (\comp -> case underCompilation comp of
        [] -> shouldnt "updateModuleM with no current module"
        (mod1:mods) -> do
          mod' <- updater mod1
          return comp { underCompilation = mod':mods })


-- |Return some function of the specified module.  Error if it's not a module.
getSpecModule :: String -> (Module -> t) -> ModSpec -> Compiler t
getSpecModule context getter spec = do
    let msg = context ++ " looking up module " ++ showModSpec spec
    underComp <- gets underCompilation
    let curr = List.filter ((==spec) . modSpec) underComp
    logAST $ "Under compilation: " ++ showModSpecs (modSpec <$> underComp)
    logAST $ "found " ++ show (length curr) ++
      " matching modules under compilation"
    case curr of
        []    -> gets (maybe (error msg) getter . Map.lookup spec . modules)
        [mod] -> return $ getter mod
        _     -> shouldnt "getSpecModule: multiple modules with same spec"


-- | Is the specified module a type?  Determined by checking if it has a
-- known representation.
moduleIsType :: ModSpec -> Compiler Bool
moduleIsType mspec = do
    foundMod <- getSpecModule "moduleIsType" modSpec mspec
    isType <- getSpecModule "moduleIsType" modIsType mspec
    logAST $ "Module " ++ showModSpec mspec ++ " (found "
             ++ showModSpec foundMod ++ ") "
             ++ (if isType then "IS" else "is NOT")
             ++ " a type"
    return isType


-- |Prepare to compile a module by setting up a new Module on the
--  front of the list of modules underCompilation.  Match this with
--  a later call to exitModule.
enterModule :: FilePath -> ModSpec -> Maybe ModSpec -> Compiler ()
enterModule source modspec rootMod = do
    -- First make sure there's not already such a module
    oldMod <- getLoadingModule modspec
    when (isJust oldMod)
      $ shouldnt $ "enterModule " ++ showModSpec modspec ++ " already exists"
    logAST $ "Entering module " ++ showModSpec modspec
    logAST $ "From file " ++ source
    logAST $ "Root module " ++ maybe "<none>" showModSpec rootMod
    absSource <- liftIO $ makeAbsolute source
    modify (\comp -> let newMod = emptyModule
                                  { modOrigin        = absSource
                                  , modRootModSpec   = rootMod
                                  , modSpec          = modspec
                                  }
                         mods = newMod : underCompilation comp
                     in  comp { underCompilation = mods })


moduleIsPackage :: ModSpec -> Compiler Bool
moduleIsPackage spec =  do
    maybeMod <- getLoadedModule spec
    case maybeMod of
        Nothing -> return False
        Just m -> return $ isPackage m


-- |Go back to compiling a module we have previously finished with.
-- Trusts that the modspec really does specify a module.  Match this
-- with a later call to reexitModule.
reenterModule :: ModSpec -> Compiler ()
reenterModule modspec = do
    logAST $ "reentering module " ++ showModSpec modspec
    mod <- getSpecModule "reenterModule" id modspec
    modify (\comp -> comp { underCompilation = mod : underCompilation comp })


-- |Finish compilation of the current module.  This matches an earlier
-- call to enterModule.
exitModule :: Compiler ()
exitModule = do
    currMod <- getModuleSpec
    imports <- getModuleImplementationField (Map.assocs . modImports)
    logAST $ "Exiting module " ++ showModSpec currMod
              ++ " with imports:\n        "
              ++ intercalate "\n        "
                 [showUse 20 mod dep | (mod, (dep, _)) <- imports]
    reexitModule


-- |Finish a module reentry, returning to the previous module.  This
-- matches an earlier call to reenterModule.
reexitModule :: Compiler ()
reexitModule = do
    mod <- getModule id
    modify
      (\comp -> comp { underCompilation = List.tail (underCompilation comp) })
    updateModules $ Map.insert (modSpec mod) mod
    logAST $ "Reexiting module " ++ showModSpec (modSpec mod)


-- | evaluate expr in the context of module mod.  Ie, reenter mod,
-- evaluate expr, and finish the module.
inModule :: Compiler a -> ModSpec -> Compiler a
inModule expr mod = do
    reenterModule mod
    val <- expr
    reexitModule
    return val


-- |Return the directory of the current module.
getDirectory :: Compiler FilePath
getDirectory = takeDirectory <$> getOrigin

-- |Return the absolute path of the file the module was loaded from.  This may
-- be a source file or an object file or a directory.
getOrigin :: Compiler FilePath
getOrigin = getModule modOrigin

-- |Return the absolute path of the file the source code for the current module
-- *should* be in.  It might not actually be there. For package, it returns the
-- path to the directory
getSource :: Compiler FilePath
getSource = do
    isPkg <- getModule isPackage
    if isPkg
    then getOrigin
    else (-<.> sourceExtension) <$> getOrigin

-- |Return the module spec of the current module.
getModuleSpec :: Compiler ModSpec
getModuleSpec = getModule modSpec

-- |Return the interface of the current module.
getModuleInterface :: Compiler ModuleInterface
getModuleInterface = getModule modInterface

-- |Return the implementation of the current module.
getModuleImplementation :: Compiler (Maybe ModuleImplementation)
getModuleImplementation = getModule modImplementation

-- |Return some function applied to the implementation of the current module.
getModuleImplementationField :: (ModuleImplementation -> t) -> Compiler t
getModuleImplementationField getter = do
  imp <- getModuleImplementation
  case imp of
      Nothing -> shouldnt "current module missing implementation"
      Just imp' -> return $ getter imp'

-- |Return some function applied to the implementation of the current module
getModuleImplementationMaybe :: (ModuleImplementation -> Maybe t) ->
                               Compiler (Maybe t)
getModuleImplementationMaybe fn = do
  imp <- getModuleImplementation
  case imp of
      Nothing -> return Nothing
      Just imp' -> return $ fn imp'


-- |Return a new, unused proc name.
genProcName :: ProcName -> Compiler ProcName
genProcName pname = do
  names <- getModule procNames
  let ctr = 1 + Map.findWithDefault 0 pname names
  updateModule (\mod -> mod {procNames = Map.alter (const $ Just ctr) pname names })
  return $ specialName2 pname $ show ctr

-- |Apply the given function to the current module interface if the
--  specified visibility is Public.
updateInterface :: Visibility -> (ModuleInterface -> ModuleInterface) ->
                  Compiler ()
updateInterface Private interfaceOp = return ()  -- do nothing
updateInterface Public interfaceOp =            -- update the interface
    updateModule (\mod -> mod { modInterface = interfaceOp $ modInterface mod })

-- |Apply the given function to the current module implementation, if
--  there is one.
updateImplementation :: (ModuleImplementation -> ModuleImplementation) ->
                       Compiler ()
updateImplementation implOp = do
    oldmod <- getModule id
    case modImplementation oldmod of
        Nothing -> return ()
        Just impl ->
            updateModule (\mod -> mod { modImplementation = Just $ implOp impl })

-- | Apply the given type modifiers to the current module interface
updateTypeModifiers :: TypeModifiers -> Compiler ()
updateTypeModifiers typeMods =
    updateModInterface $ \int -> int {typeModifiers = typeMods}

-- |Add the specified type/module parameters to the current module.
addParameters :: [TypeVarName] -> OptPos -> Compiler ()
addParameters params pos = do
    currMod <- getModuleSpec
    currParams <- getModule modParams
    when (nub params /= params)
      $ errmsg pos
           $ "duplicated type/module parameter in: "
           ++ intercalate ", " (show <$> params)
    unless (List.null currParams)
      $ errmsg pos
           $ "repeated parameter declaration: "
           ++ intercalate ", " (show <$> params)
    updateModule (\m -> m { modParams = params })


-- |Add the specified type representation to the current module.  This makes the
-- module a type.  Checks that the type doesn't already have a representation or
-- constructors defined.
addTypeRep :: TypeRepresentation -> OptPos -> Compiler ()
addTypeRep repn pos = do
    currMod <- getModuleSpec
    hasRepn <- isJust <$> getModule modTypeRep
    hasCtors <- isJust <$> getModuleImplementationField modConstructors
    if hasRepn
      then errmsg pos
           $ "Multiple representations specified for type " ++ show currMod
      else if hasCtors
      then errmsg pos
           $ "Can't declare representation of type " ++ show currMod
             ++ " with constructors"
      else do setTypeRep repn
              addKnownType currMod

-- |Set the type representation of the current module.
setTypeRep :: TypeRepresentation -> Compiler ()
setTypeRep repn = updateModule (\m -> m { modTypeRep = Just repn
                                        , modIsType  = True })


-- |Add the specified data constructor to the current module.  This makes the
-- module a type.  Also verify that all mentioned type variables are parameters
-- of this type.
addConstructor :: Visibility -> Placed ProcProto -> Compiler ()
addConstructor vis pctor = do
    let pos = place pctor
    let ctor = content pctor
    currMod <- getModuleSpec
    hasRepn <- isJust <$> getModule modTypeRep
    when hasRepn
      $ errmsg pos
           $ "Declaring constructor for type " ++ showModSpec currMod
           ++ " with declared representation"
    pctors <- fromMaybe [] <$> getModuleImplementationField modConstructors
    let redundant =
          any (\c -> procProtoName c == procProtoName ctor
                && length (procProtoParams c) == length (procProtoParams ctor))
          $ content . snd <$> pctors
    when redundant
      $  errmsg pos
           $ "Declaring constructor for type " ++ showModSpec currMod
           ++ " with repeated name/arity"
    -- isUnique <- getModule (typeModifiers . modInterface)
    let params = procProtoParams ctor
    -- unless (tmUniqueness isUnique) -- if not unique, params can't be, either
    --   $ mapM_ (ensureNotUnique pos) params
    let typeVars = Set.unions (typeVarSet . paramType . content <$> params)
    missingParams <- Set.difference typeVars . Set.fromList
                     <$> getModule modParams
    unless (Set.null missingParams)
      $ errmsg pos
            $ "Constructors for type " ++ showModSpec currMod
              ++ " use unbound type variable(s) "
              ++ intercalate ", " (("?"++) . show <$> Set.toList missingParams)
    updateImplementation (\m -> m { modConstructors =
                                    Just ((vis,pctor):pctors) })
    updateModule (\m -> m { modIsType  = True })
    addKnownType currMod


-- |Record that the specified type is known in the current module.
addKnownType :: ModSpec -> Compiler ()
addKnownType mspec = do
    currMod <- getModuleSpec
    let name = last mspec
    logAST $ "In module " ++ showModSpec currMod
             ++ ", adding type " ++ showModSpec mspec
    newSet <- Set.insert mspec . Map.findWithDefault Set.empty name
              <$> getModuleImplementationField modKnownTypes
    updateImplementation
      (\imp -> imp {modKnownTypes = Map.insert name newSet (modKnownTypes imp)})



-- |Find the definition of the specified type visible from the current module.
lookupType :: String -> OptPos -> TypeSpec -> Compiler TypeSpec
lookupType context pos ty = do
    (msgs, ty') <- lookupType' context pos ty
    mapM_ queueMessage msgs
    return ty'


-- |Find the definition of the specified type visible from the current module.
-- Errors relating to the lookup are returned along with the looked-up type
lookupType' :: String -> OptPos -> TypeSpec -> Compiler ([Message], TypeSpec)
lookupType' _ _ AnyType = return ([], AnyType)
lookupType' _ _ InvalidType = return ([], InvalidType)
lookupType' _ _ ty@TypeVariable{} = return ([], ty)
lookupType' _ _ ty@Representation{} = return ([], ty)
lookupType' context pos ty@HigherOrderType{higherTypeParams=typeFlows} = do
    (msgs, types) <- unzip <$> mapM (lookupType' context pos . typeFlowType) typeFlows
    return (concat msgs,
            ty{higherTypeParams=zipWith TypeFlow types (typeFlowMode <$> typeFlows)})
lookupType' context pos ty@(TypeSpec [] typename args)
  | typename == currentModuleAlias = do
    currMod <- getModuleSpec
    return ([], TypeSpec (init currMod) (last currMod) args)
lookupType' context pos ty@(TypeSpec mod name args) = do
    currMod <- getModuleSpec
    logAST $ "In module " ++ showModSpec currMod
             ++ ", looking up type " ++ show ty
    mspecs <- refersTo mod name modKnownTypes init
    logAST $ "Candidates: " ++ showModSpecs (Set.toList mspecs)
    case Set.size mspecs of
        0 -> do
            let msg = "In " ++ context ++ ", unknown type " ++ show ty
            return ([Message Error pos msg], InvalidType)
        1 -> do
            let mspec = Set.findMin mspecs
            maybeMod <- getLoadingModule mspec
            let params = maybe [] modParams maybeMod
            if not $ maybe False modIsType maybeMod
            then shouldnt $ "Found type isn't a type: " ++ show mspec
            else if length params == length args
            then do
                (msgs, args') <- unzip <$> mapM (lookupType' context pos) args
                let matchingType = TypeSpec (init mspec) (last mspec) args'
                logAST $ "Matching type = " ++ show matchingType
                return (concat msgs, matchingType)
            else do
                let msg = "In " ++ context
                        ++ ", type '" ++ name ++ "' expects "
                        ++ show (length params)
                        ++ " arguments, but " ++ show (length args)
                        ++ " was given"
                return ([Message Error pos msg], InvalidType)
        _ -> do
            let msg = "In " ++ context ++ ", type " ++ show ty ++
                      " could refer to: " ++ showModSpecs (Set.toList mspecs)
            return ([Message Error pos msg], InvalidType)


-- | Check if a type is unique
typeIsUnique :: TypeSpec -> Compiler Bool
typeIsUnique TypeSpec { typeMod = mod, typeName = name } = do
    let mod' = mod ++ [name]
    getSpecModule "typeIsUnique" (tmUniqueness . typeModifiers . modInterface)
                  mod'
typeIsUnique _ = return False


-- |Add the specified resource to the current module.
addSimpleResource :: ResourceName -> ResourceImpln -> Visibility -> Compiler ()
addSimpleResource name impln@(SimpleResource ty _ pos) vis = do
    currMod <- getModuleSpec
    let rspec = ResourceSpec currMod name
    let rdef = Map.singleton rspec impln
    modRess <- getModuleImplementationField modResources
    if name `Map.member` modRess
    then errmsg pos $ "Duplicate declaration of resource '" ++ name ++ "'"
    else if genericType ty
    then errmsg pos $ "Resource type cannot contain type variables: " ++ show ty
    else do
        updateImplementation
            (\imp -> imp { modResources = Map.insert name rdef $ modResources imp,
                           modKnownResources = setMapInsert name rspec
                                             $ modKnownResources imp })
        updateInterface vis $ updatePubResources $ Map.insert name rspec


-- |Find the definition of the specified resource visible in the current module.
lookupResource :: ResourceSpec -> Compiler (Maybe ResourceDef)
lookupResource res@(ResourceSpec mod name) = do
    logAST $ "Looking up resource " ++ show res
    rspecs <- refersTo mod name modKnownResources resourceMod
    logAST $ "Candidates: " ++ show rspecs
    case (Set.size rspecs, Map.lookup name specialResources) of
        (0, Just (_,ty)) | List.null mod ->
            return $ Just $ Map.singleton res
                   $ SimpleResource ty Nothing Nothing
        (0, _) -> return Nothing
        (1,_) -> do
            let rspec = Set.findMin rspecs
            maybeMod <- getLoadingModule $ resourceMod rspec
            let maybeDef = maybeMod >>= modImplementation >>=
                        Map.lookup (resourceName rspec) . modResources
            logAST $ "Found resource:  " ++ show maybeDef
            let rdef = trustFromJust "lookupResource" maybeDef
            logAST $ "  with definition:  " ++ show rdef
            return $ Just rdef
        _   -> return Nothing


-- |All the "special" resources, which Wybe automatically generates where they
-- are used, if necessary.
specialResources :: Map VarName (Placed Stmt -> Exp,TypeSpec)
specialResources =
    let cStrType = TypeSpec ["wybe"] "c_string" []
        intType = TypeSpec ["wybe"] "int" []
    in Map.fromList [
        ("call_source_file_name",(callFileName,cStrType)),
        ("call_source_file_full_name",(callFileFullName,cStrType)),
        ("call_source_line_number",(callLineNumber,intType)),
        ("call_source_column_number",(callColumnNumber,intType)),
        ("call_source_location",(callSourceLocation False,cStrType)),
        ("call_source_full_location",(callSourceLocation True,cStrType))
        ]


-- | The set of ResourceSpec that correspond to sepcial resources
specialResourcesSet :: Set ResourceSpec
specialResourcesSet = Set.map (ResourceSpec []) $ keysSet specialResources


-- | Test if ResourceSpec refers to a special resource
isSpecialResource :: ResourceSpec -> Bool
isSpecialResource res = res `Set.member` specialResourcesSet


callFileName :: Placed Stmt -> Exp
callFileName pstmt =
    (`StringValue` CString)
    $ maybe "Unknown file" (takeBaseName . sourceName) (place pstmt)

callFileFullName :: Placed Stmt -> Exp
callFileFullName pstmt =
    (`StringValue` CString)
    $ maybe "Unknown file" sourceName (place pstmt)

callLineNumber :: Placed Stmt -> Exp
callLineNumber pstmt =
    IntValue $ fromIntegral $ maybe 0 sourceLine (place pstmt)

callColumnNumber :: Placed Stmt -> Exp
callColumnNumber pstmt =
    IntValue $ fromIntegral $ maybe 0 sourceColumn (place pstmt)

callSourceLocation :: Bool -> Placed Stmt -> Exp
callSourceLocation full pstmt =
    (`StringValue` CString)
    $ maybe "unknown location" (showSourcePos full) (place pstmt)


-- |Is the specified resource exported by the current module.
publicResource :: Ident -> Compiler Bool
publicResource name = getModule (Map.member name . pubResources . modInterface)


-- |Add the specified module spec as an import of the current module.
addImport :: ModSpec -> ImportSpec -> Compiler ()
addImport modspec imports = do
    modspec' <- resolveModuleM modspec
    updateImplementation
        (updateModImports
            (Map.alter (\case
                Nothing ->
                    Just (imports, Nothing)
                Just (imports', hash) ->
                    Just (combineImportSpecs imports' imports, hash)
            ) modspec'))
    when (isUniv $ importPublic imports) $
      updateInterface Public (updateDependencies (Set.insert modspec))


-- | Represent any user-declared or inferred properties of a proc.
data ProcModifiers = ProcModifiers {
    modifierDetism::Determinism,   -- ^ The proc determinism
    modifierInline::Inlining,      -- ^ Aggresively inline this proc?
    modifierImpurity::Impurity,    -- ^ Don't assume purity when optimising
    modifierVariant::ProcVariant,  -- ^ Is proc actually a constructor?
    modifierResourceful::Bool      -- ^ Can this procedure use resources?
} deriving (Eq, Ord, Generic)


data Inlining = Inline | MayInline | NoInline
    deriving (Eq, Ord, Generic, Show)


-- | The printable modifier name for a Impurity, as specified by the user.
inliningName :: Inlining -> String
inliningName Inline     = "inline"
inliningName MayInline  = ""
inliningName NoInline   = "noinline"


-- | The Wybe impurity system.
data Impurity = PromisedPure  -- ^The proc is pure despite having impure parts
              | Pure          -- ^The proc is pure, and so are its parts
              | Semipure      -- ^The proc is not pure, but callers can be pure
              | Impure        -- ^The proc is impure and makes its callers so
    deriving (Eq, Ord, Show, Generic)


-- | The printable modifier name for a purity, as specified by the user.
impurityName :: Impurity -> String
impurityName PromisedPure = "pure"
impurityName Pure         = ""
impurityName Semipure     = "semipure"
impurityName Impure       = "impure"


-- | The Impurity of a sequence of two statements with the specified purities.
impuritySeq :: Impurity -> Impurity -> Impurity
impuritySeq = max


-- | Given a proc with the specified declared Impurity, the greatest p
expectedImpurity :: Impurity -> Impurity
expectedImpurity PromisedPure = Impure  -- If proc is promised pure,
                                        -- definition is allowed to be impure
expectedImpurity Pure = Semipure        -- Semipure is OK for pure procs
expectedImpurity _ = Impure             -- Otherwise, OK for defn to be impure


resourcefulName :: Bool -> String
resourcefulName False = ""
resourcefulName True  = "resource"


showResourceSets :: (Set ResourceSpec, Set ResourceSpec) -> String
showResourceSets (ins, outs) = "{" ++ showSet ins ++ ";" ++ showSet outs ++ "}"
  where showSet = intercalate "," . List.map show . Set.toList


-- | The default Det, non-inlined, pure ProcModifiers.
defaultProcModifiers :: ProcModifiers
defaultProcModifiers = ProcModifiers Det MayInline Pure RegularProc False


-- | Set the modifierDetism attribute of a ProcModifiers.
setDetism :: Determinism -> ProcModifiers -> ProcModifiers
setDetism detism mods = mods {modifierDetism=detism}


-- | Set the modifierInline attribute of a ProcModifiers.
setInline :: Inlining -> ProcModifiers -> ProcModifiers
setInline inlining mods = mods {modifierInline=inlining}


-- | Set the modifierImpurity attribute of a ProcModifiers.
setImpurity :: Impurity -> ProcModifiers -> ProcModifiers
setImpurity impurity mods = mods {modifierImpurity=impurity}


-- | Mark the ProcModifiers to indicate a constructor.
setVariant :: ProcVariant -> ProcModifiers -> ProcModifiers
setVariant variant mods = mods {modifierVariant=variant}


-- | How to display ProcModifiers
showProcModifiers :: ProcModifiers -> String
showProcModifiers (ProcModifiers detism inlining impurity _ res) =
    showFlags $ List.filter (not . List.null) [d,i,p,r]
    where d = determinismName detism
          i = inliningName inlining
          p = impurityName impurity
          r = resourcefulName res


-- | How to display ProcModifiers, with a space
showProcModifiers' :: ProcModifiers -> String
showProcModifiers' mods = mods' ++ if List.null mods' then "" else " "
  where mods' = showProcModifiers mods


-- | Display a list of strings separated by commas and surrounded with braces,
-- or nothing if the list is empty.
showFlags :: [String] -> String
showFlags [] = ""
showFlags flags = "{" ++ intercalate "," flags ++ "}"


-- | Display a list of strings separated by commas and surrounded with braces
-- and followed by a space, or nothing if the list is empty.
showFlags' :: [String] -> String
showFlags' flags = showFlags flags ++ if List.null flags then "" else " "


-- |Add the specified proc definition to the current module.
addProc :: Int -> Item -> Compiler ()
addProc tmpCtr (ProcDecl vis mods proto stmts pos) = do
    let name = procProtoName proto
    let ProcModifiers detism inlining impurity variant _ = mods
    let procDef = ProcDef name proto (ProcDefSrc stmts) pos tmpCtr 0 Map.empty
                  vis detism inlining impurity variant (initSuperprocSpec vis) Map.empty
    void $ addProcDef procDef
addProc _ item =
    shouldnt $ "addProc given non-Proc item " ++ show item


addProcDef :: ProcDef -> Compiler ProcSpec
addProcDef procDef = do
    let name = procName procDef
    let vis = procVis procDef
    currMod <- getModuleSpec
    procs <- getModuleImplementationField (findWithDefault [] name . modProcs)
    let procs' = procs ++ [procDef]
    let spec = ProcSpec currMod name (length procs) generalVersion
    updateImplementation
      (\imp ->
        let known = findWithDefault Set.empty name $ modKnownProcs imp
            known' = Set.insert spec known
        in imp { modProcs = Map.insert name procs' $ modProcs imp,
                 modKnownProcs = Map.insert name known' $ modKnownProcs imp })
    updateInterface vis (updatePubProcs (Map.alter (\case
                Nothing -> Just $ Map.singleton spec Unknown
                Just m  -> Just $ Map.insert spec Unknown m
        ) name))
    logAST $ "Adding definition of " ++ show spec ++ ":" ++
      showProcDef 4 procDef
    return spec


getParams :: ProcSpec -> Compiler [Param]
getParams pspec =
    -- XXX shouldn't have to grovel in implementation to find prototype
    (content <$>) . procProtoParams . procProto <$> getProcDef pspec


getPrimParams :: ProcSpec -> Compiler [PrimParam]
getPrimParams pspec =
    primProtoParams . procImplnProto . procImpln <$> getProcDef pspec


getDetism :: ProcSpec -> Compiler Determinism
getDetism pspec =
    -- XXX shouldn't have to grovel in implementation to find prototype
    procDetism <$> getProcDef pspec


getProcDef :: ProcSpec -> Compiler ProcDef
getProcDef (ProcSpec modSpec procName procID _) = do
    mod <- trustFromJustM ("no such module " ++ showModSpec modSpec) $
           getLoadingModule modSpec
    let impl = trustFromJust ("unimplemented module " ++ showModSpec modSpec) $
               modImplementation mod
    logAST $ "Looking up proc '" ++ procName ++ "' ID " ++ show procID ++ " in " ++ showModSpec modSpec
    let proc = modProcs impl ! procName !! procID
    logAST $ "  proc = " ++ showProcDef 9 proc
    return proc


getProcPrimProto :: ProcSpec -> Compiler PrimProto
getProcPrimProto pspec = do
    def <- getProcDef pspec
    case procImpln def of
        impln@ProcDefPrim{ procImplnProcSpec = pspec2, procImplnProto = proto}
            | pspec == pspec2 -> return proto
            | procSpecMod pspec == procSpecMod pspec2
                && procSpecName pspec == procSpecName pspec2
                && procSpecID pspec == procSpecID pspec2 -> do
                let impln' = impln{procImplnProcSpec = pspec}
                updateProcDef (const def {procImpln = impln'}) pspec
                return proto
            | otherwise ->
                shouldnt $ "get compiled proc but procSpec not matching: " ++
                           show pspec ++ ", " ++ show pspec2
        _ -> shouldnt $ "get prim proto of uncompiled proc " ++ show pspec


updateProcDef :: (ProcDef -> ProcDef) -> ProcSpec -> Compiler ()
updateProcDef updater pspec@(ProcSpec modspec procName procID _) =
    updateLoadedModuleImpln
    (\imp -> imp { modProcs =
                       Map.adjust
                       (\l -> case List.splitAt procID l of
                           (front,this:back) -> front ++ updater this:back
                           _ -> shouldnt $ "invalid proc spec " ++ show pspec)
                       procName (modProcs imp) })
    modspec


updateProcDefM :: (ProcDef -> Compiler ProcDef) -> ProcSpec -> Compiler ()
updateProcDefM updater pspec@(ProcSpec modspec procName procID _) =
    updateLoadedModuleImplnM
    (\imp -> do
       let procs = modProcs imp
       case Map.lookup procName procs of
         Nothing -> shouldnt ("proc not found by name: " ++ show procName)
         Just defs -> do
           let (front,back) = List.splitAt procID defs
           case back of
             [] -> shouldnt $ "invalid proc spec " ++ show pspec
             (this:rest) -> do
               updated <- updater this
               logAST $ "updated ProcDef: proto = " ++ show (procProto updated) ++ " implnProto = " ++ show (procImplnProto (procImpln updated))
               let defs' = front ++ updated:rest
               let procs' = Map.insert procName defs' procs
               return $ imp { modProcs = procs' })
    modspec



-- |Prepend the provided elt to mapping for the specified key in the map.
mapSetInsert :: (Ord a, Ord b) => a -> b -> Map a (Set b) -> Map a (Set b)
mapSetInsert key elt =
    Map.alter (Just . Set.insert elt . fromMaybe Set.empty) key


-- |Return the definition of the specified proc in the current module.
lookupProc :: Ident -> Compiler (Maybe [ProcDef])
lookupProc name =
    getModuleImplementationMaybe (Map.lookup name . modProcs)


-- |Is the specified proc exported from the current module?
publicProc :: Ident -> Compiler Bool
publicProc name = Map.member name . pubProcs <$> getModuleInterface


-- |Return some function applied to the user's specified compiler options.
option :: (Options -> t) -> Compiler t
option opt = do
    opts <- gets options
    return $ opt opts

-- |If the specified Boolean option is selected, print out the result
--  of applying the compiler state state output function.
optionallyPutStr :: (Options -> Bool) -> Compiler String -> Compiler ()
optionallyPutStr opt strcomp = do
    check <- option opt
    str <- strcomp
    when check ((liftIO . putStrLn) str)


----------------------------------------------------------------
--                            AST Types
----------------------------------------------------------------

-- |Holds everything needed to compile a module
data Module = Module {
  modOrigin :: FilePath,           -- ^Absolute path module is loaded from
  modRootModSpec :: Maybe ModSpec, -- ^Root module of the file, if it's a file
  isPackage :: Bool,               -- ^Is module actually a package
  modSpec :: ModSpec,              -- ^The module path name
  modParams :: [TypeVarName],      -- ^The type parameters, if a type
  modIsType :: Bool,               -- ^Is this module a type, defined early
  modTypeRep :: Maybe TypeRepresentation, -- ^Type representation, when known
  modInterface :: ModuleInterface, -- ^The public face of this module
  modInterfaceHash :: InterfaceHash,
                                   -- ^Hash of the "modInterface" above
  modImplementation :: Maybe ModuleImplementation,
                                   -- ^the module's implementation
  procNames :: Map.Map ProcName Int,
                                   -- ^a counter for gensym-ed proc names
  stmtDecls :: [Placed Stmt],      -- ^top-level statements in this module
  itemsHash :: Maybe String        -- ^map of proc name to its hash
  } deriving (Generic)


-- | Empty deafult for Module.
emptyModule :: Module
emptyModule = Module
    { modOrigin         = error "No Default module origin"
    , modRootModSpec    = error "No Default root modspec"
    , isPackage         = False
    , modSpec           = error "No Default Modspec"
    , modParams         = []
    , modIsType         = False
    , modTypeRep        = Nothing
    , modInterface      = emptyInterface
    , modInterfaceHash  = Nothing
    , modImplementation = Just emptyImplementation
    , procNames         = Map.empty
    , stmtDecls         = []
    , itemsHash         = Nothing
    }


isRootModule :: ModSpec -> Compiler Bool
isRootModule modspec =
    maybe False ((Just modspec ==) . modRootModSpec) <$> getLoadedModule modspec


parentModule :: ModSpec -> Maybe ModSpec
parentModule []  = Nothing
parentModule [m] = Nothing
parentModule modspec = Just $ init modspec


-- | Collect all the descendent modules of the given modspec.
descendentModules :: ModSpec -> Compiler [ModSpec]
descendentModules mspec = do
    subMods <- Map.elems . modSubmods <$> getLoadedModuleImpln mspec
    desc <- concat <$> mapM descendentModules subMods
    return $ subMods ++ desc


-- | Collect all the descendent modules of the given modspec that come from
-- the same origin and hence should go in the same target file.
sameOriginModules :: ModSpec -> Compiler [ModSpec]
sameOriginModules mspec = do
    let origin m = modOrigin . trustFromJust "sameOriginModules"
                   <$> getLoadedModule m
    file <- origin mspec
    subMods <- Map.elems . modSubmods <$> getLoadedModuleImpln mspec
    sameOriginSubMods <- filterM (((== file) <$>) . origin) subMods
    (sameOriginSubMods ++) . concat <$> mapM sameOriginModules sameOriginSubMods


-- |The set of defining modules that the given (possibly
--  module-qualified) name could possibly refer to from the current
--  module.  This may include the current module, or any module it may
--  be imported from.  The implMapFn is a Module selector function that
--  produces a map that tells whether that module exports that name,
--  and specModFn specifies which module implementation defines that
--  thing.  The reference to this name occurs in the current module.
refersTo :: Ord b => ModSpec -> Ident ->
            (ModuleImplementation -> Map Ident (Set b)) ->
            (b -> ModSpec) -> Compiler (Set b)
refersTo modspec name implMapFn specModFn = do
    currMod <- getModuleSpec
    let modspec' = if not (List.null modspec)
                        && head modspec == currentModuleAlias
                   then currMod ++ tail modspec
                   else modspec
    logAST $ "Finding visible symbol " ++ maybeModPrefix modspec' ++
      name ++ " from module " ++ showModSpec currMod
    defined <- getModuleImplementationField
               (Map.findWithDefault Set.empty name . implMapFn)
    -- imports <- getModuleImplementationField (Map.assocs . modImports)
    -- imported <- mapM getLoadingModule imports
    -- let visible = defined `Set.union` imported
    logAST $ "*** ALL matching visible modules: "
        ++ showModSpecs (Set.toList (Set.map specModFn defined))
    return $ Set.filter ((modspec' `isSuffixOf`) . specModFn) defined


-- |Returns a list of the potential targets of a proc call.
callTargets :: ModSpec -> ProcName -> Compiler [ProcSpec]
callTargets modspec name = do
    pspecs <- Set.toList <$> refersTo modspec name modKnownProcs procSpecMod
    logAST $ "   name '" ++ name ++ "' for module spec '" ++
      showModSpec modspec ++ "' matches: " ++
      intercalate ", " (List.map show pspecs)
    return pspecs


-- |Apply the given function to the current module implementation.
updateModImplementation :: (ModuleImplementation -> ModuleImplementation) ->
                          Compiler ()
updateModImplementation fn =
    updateModule
      (\mod -> case modImplementation mod of
            Nothing -> mod
            Just impl ->
                mod { modImplementation = Just $ fn impl })

-- |Apply the given monadic function to the current module implementation.
updateModImplementationM ::
    (ModuleImplementation -> Compiler ModuleImplementation) -> Compiler ()
updateModImplementationM fn =
    updateModuleM
      (\mod -> case modImplementation mod of
            Nothing -> return mod
            Just impl -> do
                impl' <- fn impl
                return $ mod { modImplementation = Just impl' })

-- |Apply the given function to the current module interface.
updateModInterface :: (ModuleInterface -> ModuleInterface) ->
                     Compiler ()
updateModInterface fn =
    updateModule (\mod -> mod { modInterface = fn $ modInterface mod })


-- Hash of the "ModuleInterface"
type InterfaceHash = Maybe String


-- |Holds everything needed to compile code that uses a module
-- XXX Currently, the data in it is never used (except for computing the
--     interface hash). We should revise the design of this, and make the
--     "compileModSCC" in Builder.hs only gets other modules' data from this
--     instead of extracting directly form "ModuleImplementation".
data ModuleInterface = ModuleInterface {
    pubResources :: Map ResourceName ResourceSpec,
                                     -- ^The resources this module exports
    pubProcs :: ProcDictionary,
                                     -- ^The procs this module exports
    pubSubmods   :: Map Ident ModSpec, -- ^The submodules this module exports
    dependencies :: Set ModSpec,      -- ^The other modules that must be linked
                                      --  in by modules that depend on this one
    typeModifiers :: TypeModifiers    -- ^The extra information of the type
    }
    deriving (Eq, Generic)

emptyInterface :: ModuleInterface
emptyInterface =
    ModuleInterface Map.empty Map.empty Map.empty Set.empty defaultTypeModifiers


-- |Holds information describing public procedures of a module.
type ProcDictionary = Map ProcName (Map ProcSpec PubProcInfo)


-- |Describing a public procedure. Should contains all the information needed
-- for other modules to use the procedure.
data PubProcInfo
    = Unknown          -- ^A placeholder for uncompiled proc
    | ReexportedProc   -- ^The proc is reexported, should refer to the
                       -- corresponding module for the info.
    | InlineProc PrimProto ProcBody
                       -- ^A proc that should be inlined at the call site.
                       -- Its whole implementation is stored.
    | NormalProc PrimProto ProcAnalysis
                       -- ^A normal proc, its analysis results are stored.
    deriving (Eq, Generic)


-- These functions hack around Haskell's terrible setter syntax

-- |Update the public resources of a module interface.
updatePubResources :: (Map Ident ResourceSpec -> Map Ident ResourceSpec) ->
                      ModuleInterface -> ModuleInterface
updatePubResources fn modint = modint {pubResources = fn $ pubResources modint}

-- |Update the public procs of a module interface.
updatePubProcs :: (ProcDictionary
                -> ProcDictionary)
                -> ModuleInterface -> ModuleInterface
updatePubProcs fn modint = modint {pubProcs = fn $ pubProcs modint}

-- |Update the set of all dependencies of a module interface.
updateDependencies :: (Set ModSpec -> Set ModSpec) ->
                      ModuleInterface -> ModuleInterface
updateDependencies fn modint = modint {dependencies = fn $ dependencies modint}

-- |Holds everything needed to compile the module itself
data ModuleImplementation = ModuleImplementation {
    modPragmas   :: Set Pragma,               -- ^pragmas for this module
    modImports   :: Map ModSpec (ImportSpec, InterfaceHash),
                                              -- ^This module's imports
    modNestedIn  :: Maybe ModSpec,            -- ^Module's parent, if nested
    modSubmods   :: Map Ident ModSpec,        -- ^This module's submodules
    modResources :: Map Ident ResourceDef,    -- ^Resources defined by this mod
    modProcs     :: Map Ident [ProcDef],      -- ^Procs defined by this module
    modConstructors :: Maybe [(Visibility,Placed ProcProto)],
                                              -- ^reversed list of data
                                              -- constructors for this
                                              -- type, if it is a type
    modKnownTypes:: Map Ident (Set ModSpec),  -- ^Types visible to this module
    modKnownResources :: Map Ident (Set ResourceSpec),
                                              -- ^Resources visible to this mod
    modKnownProcs:: Map Ident (Set ProcSpec), -- ^Procs visible to this module
    modForeignObjects:: Set FilePath,         -- ^Foreign object files used
    modForeignLibs:: Set String,              -- ^Foreign libraries used
    modLLVM :: Maybe LLVMAST.Module           -- ^Module's LLVM representation
    } deriving (Generic)

emptyImplementation :: ModuleImplementation
emptyImplementation =
    ModuleImplementation Set.empty Map.empty Nothing Map.empty Map.empty
                         Map.empty Nothing Map.empty Map.empty Map.empty
                         Set.empty Set.empty Nothing


-- These functions hack around Haskell's terrible setter syntax

-- |Update the dependencies of a module implementation.
updateModImports :: (Map ModSpec (ImportSpec, InterfaceHash)
                    -> Map ModSpec (ImportSpec, InterfaceHash))
                    -> ModuleImplementation -> ModuleImplementation
updateModImports fn modimp = modimp {modImports = fn $ modImports modimp}

-- |Update the map of submodules of a module implementation.
updateModSubmods :: (Map Ident ModSpec -> Map Ident ModSpec) ->
                   ModuleImplementation -> ModuleImplementation
updateModSubmods fn modimp = modimp {modSubmods = fn $ modSubmods modimp}

-- |Update the map of resources of a module implementation.
updateModResources :: (Map Ident ResourceDef -> Map Ident ResourceDef) ->
                     ModuleImplementation -> ModuleImplementation
updateModResources fn modimp = modimp {modResources = fn $ modResources modimp}

-- |Update the map of proc definitions of a module implementation.
updateModProcs :: (Map Ident [ProcDef] -> Map Ident [ProcDef]) ->
                 ModuleImplementation -> ModuleImplementation
updateModProcs fn modimp = modimp {modProcs = fn $ modProcs modimp}

-- |Update the map of proc definitions of a module implementation.
updateModProcsM :: (Map Ident [ProcDef] -> Compiler (Map Ident [ProcDef])) ->
                 ModuleImplementation -> Compiler ModuleImplementation
updateModProcsM fn modimp = do
    procs' <- fn $ modProcs modimp
    return $ modimp {modProcs = procs'}

-- |Add a file to the set of foreign files used by the current module
addForeignImport :: Ident -> Compiler ()
addForeignImport objName = do
    let fl = objName -<.> objectExtension
    updateModImplementation
        (\imp ->
           imp { modForeignObjects = Set.insert fl $ modForeignObjects imp })

-- |Add a file to the set of foreign files used by the current module
addForeignLib :: Ident -> Compiler ()
addForeignLib lib = do
    let arg = "-l" ++ lib
    updateModImplementation
        (\imp ->
           imp { modForeignLibs = Set.insert arg $ modForeignLibs imp })


-- | Given a type spec, find its internal representation (a string),
--   if possible.
lookupTypeRepresentation :: TypeSpec -> Compiler (Maybe TypeRepresentation)
lookupTypeRepresentation AnyType = return $ Just defaultTypeRepresentation
lookupTypeRepresentation InvalidType = return Nothing
lookupTypeRepresentation TypeVariable{} =
    return $ Just defaultTypeRepresentation
lookupTypeRepresentation Representation{typeSpecRepresentation=rep} =
    return $ Just rep
lookupTypeRepresentation (TypeSpec modSpec name _) =
    lookupModuleRepresentation $ modSpec ++ [name]
lookupTypeRepresentation (HigherOrderType ProcModifiers{modifierDetism=detism} tfs) = do
    mbInReps <- sequenceRepFlowTypes ins
    mbOutReps <- sequenceRepFlowTypes outs
    return $ Func <$> mbInReps
                  <*> ((++ [Signed 1 | detism == SemiDet])
                  <$> mbOutReps)
  where
    ins = List.filter (flowsIn . typeFlowMode) tfs
    outs = List.filter (flowsOut . typeFlowMode) tfs
    sequenceRepFlowTypes = (sequence <$>) . mapM lookupTypeRepresentation
                                          . (typeFlowType <$>)


-- |Given a module spec, find its representation, if it is a type.
lookupModuleRepresentation :: ModSpec -> Compiler (Maybe TypeRepresentation)
lookupModuleRepresentation =
    getSpecModule "lookupModuleRepresentation" modTypeRep


-- |An identifier.
type Ident = String

-- |A variable name.
type VarName = Ident

-- |A proc name.
type ProcName = Ident

-- |A resource name.
type ResourceName = Ident

-- |A type variable name.
-- Real type variables represent type variables specified by the programmer;
-- faux type variables are generated by the compiler.
data TypeVarName
    = RealTypeVar Ident
    | FauxTypeVar Int
  deriving (Eq, Ord, Generic)

instance Show TypeVarName where
    show (RealTypeVar v) = v
    show (FauxTypeVar i) = show i

-- |A module specification, as a list of module names; module a.b.c would
--  be represented as ["a","b","c"].
type ModSpec = [Ident]


-- |The uses one module makes of another; first the public imports,
--  then the privates.  Each is either Nothing, meaning all exported
--  names are imported, or Just a set of the specific names to import.
data ImportSpec = ImportSpec {
    importPublic::UnivSet Ident,
    importPrivate::UnivSet Ident
    } deriving (Show, Generic)


-- |Create an import spec to import the identifiers specified by the
--  first argument (or everything public if it is Nothing), either
--  publicly or privately, as specified by the second argument.
importSpec :: Maybe [Ident] -> Visibility -> ImportSpec
importSpec Nothing Public =
    ImportSpec UniversalSet  (FiniteSet Set.empty)
importSpec Nothing Private =
    ImportSpec (FiniteSet Set.empty) UniversalSet
importSpec (Just items) Public =
    ImportSpec (FiniteSet $ Set.fromList items) (FiniteSet Set.empty)
importSpec (Just items) Private =
    ImportSpec (FiniteSet Set.empty) (FiniteSet $ Set.fromList items)


-- |Merge two import specs to create a single one that imports
--  exactly what the two together specify.
combineImportSpecs :: ImportSpec -> ImportSpec -> ImportSpec
combineImportSpecs (ImportSpec pub1 priv1) (ImportSpec pub2 priv2) =
    ImportSpec (USet.union pub1 pub2) (USet.union priv1 priv2)


-- |Actually import into the current module.  The ImportSpec says what
-- to import.
doImport :: ModSpec -> (ImportSpec, InterfaceHash) -> Compiler ()
doImport mod (imports, _) = do
    currMod <- getModuleSpec
    impl <- getModuleImplementationField id
    logAST $ "Handle importation from " ++ showModSpec mod ++
      " into " ++
      let modStr = showModSpec currMod
      in modStr ++ ":  " ++ showUse (27 + length modStr) mod imports
    fromIFace <- modInterface . trustFromJust "doImport"
                 <$> getLoadingModule mod
    let pubImports = importPublic imports
    let allImports = USet.union pubImports $ importPrivate imports
    let importedModsAssoc =
            (last mod,mod):
            Map.toAscList (importsSelected allImports $ pubSubmods fromIFace)
    importedTypesAssoc <- filterM (moduleIsType . snd) importedModsAssoc
    let importedResources = importsSelected allImports $ pubResources fromIFace
    let importedProcs = Map.map Map.keysSet
                            $ importsSelected allImports $ pubProcs fromIFace
    logAST $ "    importing types    : "
             ++ showModSpecs (snd <$> importedTypesAssoc)
    logAST $ "    importing resources: "
             ++ intercalate ", " (Map.keys importedResources)
    logAST $ "    importing procs    : "
             ++ intercalate ", " (Map.keys importedProcs)
    -- XXX Must report error for imports of non-exported items
    let knownTypes = Map.unionWith Set.union (modKnownTypes impl)
                     $ Map.fromAscList
                     $ List.map (mapSnd Set.singleton) importedTypesAssoc
    let knownResources =
            Map.unionWith Set.union (modKnownResources impl) $
            Map.map Set.singleton importedResources
    let knownProcs = Map.unionWith Set.union (modKnownProcs impl) importedProcs
    -- Update what's visible in the module
    updateModImplementation (\imp -> imp { modKnownTypes = knownTypes,
                                           modKnownResources = knownResources,
                                           modKnownProcs = knownProcs })
    logAST $ "New exports from module " ++ showModSpec mod ++ ":"
    let exportedMods = importsSelected pubImports
                       $ Map.insert (last mod) mod $ pubSubmods fromIFace
    logAST $ "    modules  : " ++ showModSpecs (Map.elems exportedMods)
    let exportedResources = importsSelected pubImports $ pubResources fromIFace
    logAST $ "    resources: " ++ intercalate ", " (Map.keys exportedResources)
    let exportedProcs = importsSelected pubImports $ pubProcs fromIFace
    logAST $ "    procs    : " ++ intercalate ", " (Map.keys exportedProcs)
    updateModInterface
      (\i -> i {pubSubmods = Map.union (pubSubmods i) exportedMods,
                pubResources = Map.union (pubResources i) exportedResources,
                pubProcs = Map.unionWith Map.union (pubProcs i) exportedProcs })
    -- Update what's exported from the module
    return ()


-- |Import known types, resources, and procs from the specified module into the
-- current one.  This is used to give a nested submodule access to its parent's
-- members.  It's also used to give the executable module access to the main
-- module of the application.
importFromSupermodule :: ModSpec -> Compiler ()
importFromSupermodule modspec = do
    impl       <- getLoadedModuleImpln modspec
    kTypes     <- getModuleImplementationField modKnownTypes
    kResources <- getModuleImplementationField modKnownResources
    kProcs     <- getModuleImplementationField modKnownProcs
    let knownTypes = Map.unionWith Set.union (modKnownTypes impl) kTypes
    let knownResources =
            Map.unionWith Set.union (modKnownResources impl) kResources
    let knownProcs = Map.unionWith Set.union (modKnownProcs impl) kProcs
    updateModImplementation (\imp -> imp { modKnownTypes = knownTypes,
                                           modKnownResources = knownResources,
                                           modKnownProcs = knownProcs })


-- | Resolve a (possibly) relative module spec into an absolute one.  The
-- first argument is a possibly relative module spec and the second is an
-- absolute one which the first argument should be interpreted relative to.
resolveModule :: ModSpec -> ModSpec -> Maybe ModSpec
resolveModule ("^":_) [] = Nothing
resolveModule ("^":relspec) absspec@(_:_) =
    resolveModule' relspec $ init absspec
resolveModule modspec _ = Just modspec

resolveModule' :: ModSpec -> ModSpec -> Maybe ModSpec
resolveModule' [] spec = Just spec
resolveModule' ("^":relspec) absspec@(_:_) =
    resolveModule' relspec $ init absspec
resolveModule' relspec absspec = Just $ absspec ++ relspec

resolveModuleM :: ModSpec -> Compiler ModSpec
resolveModuleM mod = do
    currMod <- getModuleSpec
    case resolveModule mod currMod of
      Nothing -> do
        message Error ("unresolvable relative module spec '" ++
                        showModSpec mod ++ "'") Nothing
        return mod
      Just m -> return m


importsSelected :: UnivSet Ident -> Map Ident a -> Map Ident a
importsSelected imports items =
    Map.filterWithKey (\k _ -> USet.member k imports) items


-- | Pragmas that can be specified for a module
data Pragma = NoStd        -- ^ Don't import that standard library for this mod
   deriving (Eq,Ord,Generic)

instance Show Pragma where
    show NoStd = "no_standard_library"


-- |Specify a pragma for the current module
addPragma :: Pragma -> Compiler ()
addPragma prag =
    updateModImplementation
    (\imp -> imp { modPragmas = Set.insert prag $ modPragmas imp })


-- |A type definition, including the number of type parameters and an
--  optional source position.
data TypeDef = TypeDef {
    typeDefVis    :: Visibility,                  -- type visibility
    typeDefParams :: [Ident],                     -- the type parameters
    typeDefRepresentation :: Maybe TypeRepresentation,
                                                  -- low level representation
    typeDefMembers :: [Placed ProcProto],         -- high level representation
    typeDefMemberVis :: Visibility,               -- are members public?
    typeDefModifiers :: TypeModifiers,            -- type modifiers
    typeDefOptPos :: OptPos,                      -- source position of decl
    typeDefItems  :: [Item]                       -- other items in decl
    } deriving (Eq, Generic)


-- |A resource interface: everything a module needs to know to use
--  this resource.  Since a resource may be compound (composed of
--  other resources), this is basically a set of resource specs, each
--  with an associated type.
type ResourceIFace = Map ResourceSpec TypeSpec


resourceDefToIFace :: ResourceDef -> ResourceIFace
resourceDefToIFace = Map.map resourceType


-- |A resource definition.  Since a resource may be defined as a
--  collection of other resources, this is a set of resources (for
--  simple resources, this will be a singleton), each with type and
--  possibly an initial value.  There's also an optional source
-- position.
type ResourceDef = Map ResourceSpec ResourceImpln

data ResourceImpln =
    SimpleResource {
        resourceType::TypeSpec,
        resourceInit::Maybe (Placed Exp),
        resourcePos::OptPos
        } deriving (Generic)


-- | A list of the initialised resources defined by the current module.
initialisedResources :: Compiler ResourceDef
initialisedResources = do
    modRes <- getModuleImplementationField modResources
    logAST $ "Getting initialised resources = " ++ show modRes
    logAST $ "                       unions = " ++ show (Map.unions modRes)
    return $ Map.filter (isJust . resourceInit) $ Map.unions modRes

-- |A proc definition, including the ID, prototype, the body,
--  normalised to a list of primitives, and an optional source
--  position.
data ProcDef = ProcDef {
    procName :: ProcName,       -- ^the proc's name
    procProto :: ProcProto,     -- ^the proc's prototype
    procImpln :: ProcImpln,     -- ^the actual implementation
    procPos :: OptPos,          -- ^where this proc is defined
    procTmpCount :: Int,        -- ^the next temp variable number to use
    procCallSiteCount :: CallSiteID,
                                -- ^the next call site id to use
    procCallers :: Map ProcSpec Int,
                                -- ^callers to this proc from this mod in the
                                -- source code (before inlining) and the count
                                -- of calls for each caller
                                -- XXX We never actually use this map, we just
                                -- add up the call counts, so we might as well
                                -- keep just a count
    procVis :: Visibility,      -- ^what modules should be able to see this?
    procDetism :: Determinism,  -- ^can this proc fail?
    procInlining :: Inlining,   -- ^should we inline calls to this proc?
    procImpurity :: Impurity,   -- ^ Is this proc pure?
    procVariant :: ProcVariant, -- ^ How is this proc manifested in the source code
    procSuperproc :: SuperprocSpec,
                                -- ^the proc this should be part of, if any
    procVariableFlows :: Map PrimVarName GlobalFlows
                                -- ^ The currently known global flows of each
                                -- variable in this proc. If a variable is not
                                -- contained in the map, the flows are not
                                -- known, and can be assumed to be universal
}
             deriving (Eq, Generic)

-- | Takes in a monadic function that transforms a ProcDef, and a module spec
--   whose ProcDefs we apply the transforming function on.
transformModuleProcs :: (ProcDef -> Int -> Compiler ProcDef) -> ModSpec ->
                        Compiler ()
transformModuleProcs trans thisMod = do
    reenterModule thisMod
    -- (names, procs) <- :: StateT CompilerState IO ([Ident], [[ProcDef]])
    (names,procs) <- unzip <$>
                     getModuleImplementationField (Map.toList . modProcs)
    -- for each name we have a list of procdefs, so we must double map
    procs' <- mapM (zipWithM (flip trans) [0..]) procs
    updateImplementation
        (\imp -> imp { modProcs = Map.union
                                  (Map.fromList $ zip names procs')
                                  (modProcs imp) })
    reexitModule

-- |Whether this proc should definitely be inlined, either because the user said
-- to, or because we inferred it would be a good idea.
procInline :: ProcDef -> Bool
procInline = (==Inline) . procInlining


-- | What are the GlobalFLows of the given ProcSpec
getProcGlobalFlows :: ProcSpec -> Compiler GlobalFlows
getProcGlobalFlows pspec = do
    pDef <- getProcDef pspec
    case procImpln pDef of
      ProcDefSrc _ ->
            let ProcProto _ params resFlows = procProto pDef
                paramFlows 
                    | any (isResourcefulHigherOrder . paramType . content) params
                    = UniversalSet
                    | otherwise
                    = emptyUnivSet
            in return $ (makeGlobalFlows [] resFlows){globalFlowsParams=paramFlows}
      ProcDefPrim _ (PrimProto _ _ gFlows) _ _ _ -> return gFlows


-- | How many static calls to this proc from the same module have we seen?  This
-- won't be correct for public procs.
procCallCount :: ProcDef -> Int
procCallCount proc = Map.foldr (+) 0 $ procCallers proc


-- | What is the Impurity of the given Prim?
primImpurity :: Prim -> Compiler Impurity
primImpurity (PrimCall _ pspec impurity _ _) = return impurity
primImpurity (PrimHigher _ (ArgClosure pspec _ _) impurity _)
    = max impurity . procImpurity <$> getProcDef pspec
primImpurity (PrimHigher _ ArgVar{argVarType=HigherOrderType
                    ProcModifiers{modifierImpurity=modimpurity} _} impurity _)
    = return $ max impurity modimpurity
primImpurity (PrimHigher _ fn _ _)
    = shouldnt $ "primImpurity of" ++ show fn
primImpurity (PrimForeign _ _ flags _)
    = return $ flagsImpurity flags


-- | Return the impurity level specified by the given foriegn flags list
flagsImpurity :: [String] -> Impurity
flagsImpurity = List.foldl flagImpurity Pure


-- | Gather the impurity of a flag
flagImpurity :: Impurity -> String -> Impurity
flagImpurity _ "impure"   = Impure
flagImpurity _ "semipure" = Semipure
flagImpurity _ "pure"     = PromisedPure
flagImpurity impurity _   = impurity


-- | Return the impurity level specified by the given foriegn flags list
flagsDetism :: [String] -> Determinism
flagsDetism = List.foldl flagDetism Det


-- | Gather the Determinism of a flag
flagDetism :: Determinism  -> String -> Determinism
flagDetism _ "terminal" = Terminal
flagDetism _ "failing"  = Failure
flagDetism _ "det"      = Det
flagDetism _ "semidet"  = SemiDet
flagDetism detism _     = detism


data ProcVariant
    = RegularProc
    | ConstructorProc ProcName
    | DeconstructorProc ProcName
    | GetterProc VarName TypeSpec
    | SetterProc VarName TypeSpec
    | GeneratedProc
    | AnonymousProc
    | ClosureProc ProcSpec
    deriving (Eq, Ord, Show, Generic)


-- |LLVM block structure allows many blocks per procedure, where blocks can
--  jump to one another in complex ways.  When converting our LPVM format
--  to blocks, we want to merge any proc that is only called from one proc,
--  and only called as a tail call, into its caller.  We determine this by
--  scanning every proc definition; this type is used to hold intermediate
--  and final subproc info for each proc.  SuperprocIs p means we have
--  seen only tail calls to this proc, and only from p.  NoSuperproc means
--  this proc is public, or we have seen calls from multiple callers, or in
--  positions.
data SuperprocSpec
    = NoSuperproc             -- ^Cannot be a subproc
    | AnySuperproc            -- ^Could be a subproc of any proc
    | SuperprocIs ProcSpec    -- ^May only be a subproc of specified proc
    deriving (Eq, Show, Generic)


-- |The appropriate initial SuperprocSpec given the proc's visibility
initSuperprocSpec :: Visibility -> SuperprocSpec
initSuperprocSpec vis = if isPublic vis then NoSuperproc else AnySuperproc


-- |How to dump a SuperprocSpec
showSuperProc :: SuperprocSpec -> String
showSuperProc NoSuperproc = ""
showSuperProc AnySuperproc = ""
showSuperProc (SuperprocIs super) = " (subproc of " ++ show super ++ ")"


-- |Maybe get the ProcSpec of a ClosureOf Proc via a ProcSpec
maybeGetClosureOf :: ProcSpec -> Compiler (Maybe ProcSpec)
maybeGetClosureOf pspec = do
    variant <- procVariant <$> getProcDef pspec
    return $ case variant of
        ClosureProc cls -> Just cls
        _ -> Nothing


-- |Check if a ProcSpec refers to a closure proc
isClosureProc :: ProcSpec -> Compiler Bool
isClosureProc pspec = isClosureVariant . procVariant <$> getProcDef pspec


isClosureVariant :: ProcVariant -> Bool
isClosureVariant (ClosureProc _) = True
isClosureVariant _               = False

isConstructorVariant :: ProcVariant -> Bool
isConstructorVariant (ConstructorProc _) = True
isConstructorVariant _                   = False


-- |A procedure definition body.  Initially, this is in a form similar
-- to what is read in from the source file.  As compilation procedes,
-- this is gradually refined and constrained, until it is converted
-- into a ProcBody, which is a clausal, logic programming form.
-- Finally it is turned into SSA form (LLVM).
data ProcImpln
    = ProcDefSrc [Placed Stmt]           -- ^defn in source-like form
    | ProcDefPrim {
        procImplnProcSpec :: ProcSpec,
        procImplnProto :: PrimProto,
        procImplnBody :: ProcBody,       -- ^defn in LPVM (clausal) form
        procImplnAnalysis :: ProcAnalysis,
        procImplnSpeczBodies :: SpeczProcBodies
    }
    deriving (Eq,Generic)


-- | Represents a set of globals flowing in and out.
data GlobalFlows
    = GlobalFlows {
        globalFlowsIn :: UnivSet GlobalInfo,
        -- ^ The set of globals that flow in
        globalFlowsOut :: UnivSet GlobalInfo,
        -- ^ The set of globals that flow out
        globalFlowsParams :: UnivSet ParameterID
        -- ^ The set of parameters (by ID) that effect the global flwos
    }
    deriving (Eq, Ord, Generic)


instance Show GlobalFlows where
    show (GlobalFlows ins outs params) =
        "<" ++ showUnivSet show ins
        ++ "; " ++ showUnivSet show outs
        ++ "; " ++ showUnivSet show params
        ++ ">"


-- | An empty set of GlobalFlows
emptyGlobalFlows :: GlobalFlows
emptyGlobalFlows = GlobalFlows emptyUnivSet emptyUnivSet emptyUnivSet


-- | The set of all GlobalFlows
univGlobalFlows :: GlobalFlows
univGlobalFlows = GlobalFlows UniversalSet UniversalSet UniversalSet


-- | Given a list of Types and a set of ResourceFlowSpecs, make a GlobalFlows.
-- If any of the TypeSpecs are resourceful higher order, this is the
-- univGlobalFlows, otherwise this is derived from the resources and flows.
--
-- In the case we have a higher order resourceful argument, we may not know
-- exactly which global variables flow into or out of a procedure, and as such
-- we take a conservative approach and assume all do.
makeGlobalFlows :: [(ParameterID, PrimParam)] -> Set ResourceFlowSpec -> GlobalFlows
makeGlobalFlows params resFlows =
    Set.fold addGlobalResourceFlows 
        (emptyGlobalFlows{globalFlowsParams=pFlows}) resFlows
  where
    pFlows = FiniteSet $ Set.fromList $ catMaybes $ List.map (uncurry paramFlow) params
    paramFlow i PrimParam{primParamName=name, primParamType=ty, primParamFlow=flow}
        | isInputFlow flow && (isResourcefulHigherOrder ||| genericType) ty
        = Just i
        | otherwise = Nothing


-- |Add flows associated with a given resource to a set of GlobalFlows
addGlobalResourceFlows :: ResourceFlowSpec -> GlobalFlows -> GlobalFlows
addGlobalResourceFlows (ResourceFlowSpec res flow) gFlows
    | isSpecialResource res = gFlows
    | otherwise = List.foldr (addGlobalFlow (GlobalResource res)) gFlows
                $ [FlowIn | flowsIn flow] ++ [FlowOut | flowsOut flow]


-- | Add a GlobalInfo to the set of global flows associated with the given flow
addGlobalFlow :: GlobalInfo -> PrimFlow -> GlobalFlows -> GlobalFlows
addGlobalFlow info FlowIn gFlows@GlobalFlows{globalFlowsIn=ins}
    = gFlows{globalFlowsIn=whenFinite (Set.insert info) ins}
addGlobalFlow info FlowOut gFlows@GlobalFlows{globalFlowsOut=outs}
    = gFlows{globalFlowsOut=whenFinite (Set.insert info) outs}
-- global flows don't use this flow type
addGlobalFlow info FlowOutByReference gFlows = gFlows
addGlobalFlow info FlowTakeReference gFlows = gFlows

-- | Test if the given flow of a global exists in the global flow set
hasGlobalFlow :: GlobalFlows -> PrimFlow -> GlobalInfo -> Bool
hasGlobalFlow gFlows@GlobalFlows{globalFlowsParams=params} _ _
    | not (USet.isEmpty params) = True
hasGlobalFlow GlobalFlows{globalFlowsIn=ins, globalFlowsOut=outs} flow info
    | isInputFlow flow
    = USet.member info ins
    | otherwise
    = USet.member info outs


-- | Take the union of the sets of two global flows
globalFlowsUnion :: GlobalFlows -> GlobalFlows -> GlobalFlows
globalFlowsUnion (GlobalFlows ins1 outs1 params1) (GlobalFlows ins2 outs2 params2)
    = GlobalFlows 
        (USet.union ins1 ins2) 
        (USet.union outs1 outs2) 
        (USet.union params1 params2)

globalFlowsUnions :: [GlobalFlows] -> GlobalFlows
globalFlowsUnions = List.foldr globalFlowsUnion emptyGlobalFlows


-- | Take the intersection of the sets of two global flows
globalFlowsIntersection :: GlobalFlows -> GlobalFlows -> GlobalFlows
globalFlowsIntersection (GlobalFlows ins1 outs1 params1) 
                        (GlobalFlows ins2 outs2 params2)
    = GlobalFlows 
        (USet.intersection ins1 ins2) 
        (USet.intersection outs1 outs2) 
        (USet.intersection params1 params2)


-- |An ID for a parameter of a proc
type ParameterID = Int


-- |Convert "ParameterID" to "PrimVarName"
parameterIDToVarName :: PrimProto -> ParameterID -> PrimVarName
parameterIDToVarName proto paramID =
    let params = primProtoParams proto in
    primParamName (params !! paramID)


-- |Convert "PrimVarName" to "ParameterID"
parameterVarNameToID :: PrimProto -> PrimVarName -> ParameterID
parameterVarNameToID proto varName =
    let params = primProtoParams proto in
    let idx = List.findIndex ((== varName) . primParamName) params in
    trustFromJust "parameterVarNameToID" idx


-- |Used for describing a specific specialized version
-- Removing one "CallProperty" should only make the specialization a bit
-- more general and shouldn't break it. ie. the empty set signifies no
-- specialization and should be valid for all call site.
type SpeczVersion = Set CallProperty


-- "SpeczVersion" for the general(standard) version.
generalVersion :: SpeczVersion
generalVersion = Set.empty


-- |Each one represents some additional information about the specialization.
data CallProperty
-- "NonAliasedParam v1" is used for global CTGC, it means that the argument
-- passed to parameter v1 is nonaliased.
    = NonAliasedParam ParameterID
    -- Remove the placeholder below and add more items when adding new
    -- specializations. The placeholder is used to avoid overlapping-patterns
    -- warning as well as the suggestion of using newtype instead of data from
    -- linter.
    | CallPropertyPlaceholder
    deriving (Eq, Ord, Show, Generic)

-- XXX Those should be put in "BinaryFactory.hs". However we need to compute the
-- hash of "SpeczVersion" in "AST.hs".
instance Data.Binary.Binary CallProperty


-- |Convert a "SpeczVersion" to a string as part of the proc identifier.
-- It's first 40 bits (out of 160 bits) of the sha1 hash. Collision will be
-- detected in "Blocks.hs".
speczVersionToId :: SpeczVersion -> String
speczVersionToId = List.take 10 . show . sha1 . Data.Binary.encode
    where
        sha1 :: BL.ByteString -> Digest SHA1
        sha1 = hashlazy


-- | A map contains different specialization versions.
-- The key is the id of each version and the value is the
-- actual implementation. A procBody can be "Nothing" when it's required but
-- haven't been generated. All procBody will be generated before converting to
-- llvm code.
type SpeczProcBodies = Map SpeczVersion (Maybe ProcBody)


-- | Use to record the alias relation between arguments of a procedure.
type AliasMap = DisjointSet PrimVarName


-- | a synonym function to hide the impletation of how unionfind is printed
showAliasMap :: AliasMap -> String
showAliasMap aliasMap = show $ aliasMapToAliasPairs aliasMap


-- | a synonym function to hide the impletation of how unionfind is converted to
-- alias pairs
aliasMapToAliasPairs :: AliasMap -> [(PrimVarName, PrimVarName)]
aliasMapToAliasPairs aliasMap = Set.toList $ dsToTransitivePairs aliasMap


-- |Infomation about specialization versions the current proc directly uses.
-- It's a mapping from call sites to the callee's "ProcSpec" and a set of
-- "CallSiteProperty".
-- For a given specialization version of the current proc, this info should be
-- enough to compute all specz versions it required. A sample case is
-- "expandSpeczVersionsAlias" in "Transform.hs".
type MultiSpeczDepInfo =
        Map CallSiteID (ProcSpec, Set CallSiteProperty)


-- |Specific items for "MultiSpeczDepInfo", it describing the information about
-- the related call site.
data CallSiteProperty
    -- "NonAliasedParamCond calleeParam [callerParam]" is used for global CTGC.
    -- eg. NonAliasedParamCond v1 [v2, v3] means that if the paramenters v2, v3
    -- of the caller proc is nonaliased, then the parameter v1 of the callee is
    -- nonaliased and we could specialize it.
    = NonAliasedParamCond ParameterID [ParameterID]
    -- Refer to `CallProperty` for information regarding this placeholder
    | CallSitePropertyPlaceholder
    deriving (Eq, Generic, Ord, Show)


-- |Describing the interestingness of a proc. if something is interesting, that
-- means if we could provide some information about that thing, then we can
-- generate more specialized code.
data InterestingCallProperty
    -- "InterestingUnaliased v" means that if parameter v is known as unaliased,
    -- then we can make use of it.
    = InterestingUnaliased ParameterID
    -- Refer to `CallProperty` for information regarding this placeholder
    | InterestingCallPropertyPlaceholder
    deriving (Eq, Generic, Ord, Show)


-- | Stores whatever analysis results we infer about a proc definition.
data ProcAnalysis = ProcAnalysis {
    procArgAliasMap               :: AliasMap,
    procInterestingCallProperties :: Set InterestingCallProperty,
    procMultiSpeczDepInfo         :: MultiSpeczDepInfo
} deriving (Eq,Generic)


-- | The empty ProcAnalysis
emptyProcAnalysis :: ProcAnalysis
emptyProcAnalysis = ProcAnalysis emptyDS Set.empty Map.empty


isCompiled :: ProcImpln -> Bool
isCompiled ProcDefPrim {} = True
isCompiled (ProcDefSrc _) = False

instance Show ProcImpln where
    show (ProcDefSrc stmts) = showBody 4 stmts
    show (ProcDefPrim pSpec proto body analysis speczVersions) =
        let speczBodies = Map.toList speczVersions
                |> List.map (\(ver, body) ->
                        "\n [" ++ speczVersionToId ver ++ "] "
                        ++ show (Set.toList ver) ++ " :"
                        ++ case body of
                            Nothing -> " Missing"
                            Just body -> showBlock 4 body)
                |> intercalate "\n"
        in  show pSpec ++ "\n" ++ show proto ++ ":"
                    ++ show analysis
                    ++ showBlock 4 body ++ speczBodies


instance Show ProcAnalysis where
    show (ProcAnalysis aliasMap interestingCallProperties multiSpeczDepInfo) =
        let multiSpeczDepInfo' = Map.toList multiSpeczDepInfo
                |> List.filter (not . List.null . snd)
        in
        "\n  AliasPairs: " ++ showAliasMap aliasMap
        ++ "\n  InterestingCallProperties: "
        ++ show (Set.toAscList interestingCallProperties)
        ++ if List.null multiSpeczDepInfo'
            then ""
            else "\n  MultiSpeczDepInfo: " ++ show multiSpeczDepInfo'



-- |A Primitve procedure body.  In principle, a body is a set of clauses, each
-- possibly containg some guards.  Each guard is a test that succeeds
-- iff the specified variable holds the specified value.  For each
-- guard in a clause, it is required that there are other clauses that
-- are identical up to that guard, and specify each of the other
-- possible values for that variable.  This ensures that the clauses
-- are exhaustive.  It is also required that any two clauses contain
-- guards specifying distinct values, up to which the two clauses are
-- identical.  This ensures the set of clauses is mutually exclusive.
--
-- In practice, we adopt a structure that ensures these constraints,
-- and avoids duplicating the initial code that is common to a number
-- of claues.  Thus a procedure body contains a list of primitives
-- (the common code) followed by a fork, where the code splits into
-- multiple different clauses, one for each possible value of a
-- specified unsigned integer variable.  If the value of the variable
-- is equal or greater than the number of clauses, behaviour is
-- undefined.  To allow clauses to support multiple guards, each of
-- the clauses is itself a procedure body.

data ProcBody = ProcBody {
      bodyPrims::[Placed Prim],
      bodyFork::PrimFork}
              deriving (Eq, Show, Generic)

-- | A primitive switch.  This only appears at the end of a ProcBody.
-- This specifies that if forkVar is 0, the first body in forkBodies
-- should be executed; if it's 1, the second body should be executed, and
-- so on.  If it's greater or equal to the length of the list, the last
-- body should be executed.  The forkVar is always treated as an unsigned
-- integer type.  If forkVarLast is True, then this is the last occurrence
-- of that variable.
data PrimFork =
    NoFork |
    PrimFork {
      forkVar::PrimVarName,     -- ^The variable that selects branch to take
      forkVarType::TypeSpec,    -- ^The Wybe type of the forkVar
      forkVarLast::Bool,        -- ^Is this the last occurrence of forkVar
      forkBodies::[ProcBody],   -- ^one branch for each value of forkVar
      forkDefault::Maybe ProcBody -- ^branch to take if forkVar is out of range
    }
    deriving (Eq, Show, Generic)


data LLBlock = LLBlock {
    llInstrs::[LLInstr],
    llTerm::LLTerm
    } deriving (Eq, Show)


data LLInstr = LLNop
  -- LLInstr {
  --   llTarget::Maybe PrimVarName,
  --   llOpr::[String],
  --   llOperands::[(PrimVar,PrimType)]
             deriving (Eq, Show)


data LLTerm = TermNop
            deriving (Eq, Show)

-- |The variable name for the temporary variable whose number is given.
mkTempName :: Int -> String
mkTempName ctr = specialName2 "tmp" $ show ctr

-- |Make a default LLBlock
defaultBlock :: LLBlock
defaultBlock =  LLBlock { llInstrs = [], llTerm = TermNop }


-- |Fold over a list of statements in a pre-order left-to-right traversal.
-- Takes two folding functions, one for statements and one for expressions.
foldStmts :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a) -> a
          -> [Placed Stmt] -> a
foldStmts sfn efn = List.foldl (placedApply . foldStmt sfn efn)


-- |Fold over the specified statement and all the statements nested within it,
-- in a pre-order left-to-right traversal. Takes two folding functions, one for
-- statements and one for expressions.
foldStmt :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a) -> a
         -> Stmt -> OptPos -> a
foldStmt sfn efn val stmt pos = foldStmt' sfn efn (sfn val stmt pos) stmt pos


-- |Fold over all the statements nested within the given statement,
-- but not the statement itself, in a pre-order left-to-right traversal.
-- Takes two folding functions, one for statements and one for expressions.
foldStmt' :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a) -> a
          -> Stmt -> OptPos -> a
foldStmt' sfn efn val (ProcCall (First _ _ _) _ _ args) pos =
    foldExps sfn efn pos val args
foldStmt' sfn efn val (ProcCall (Higher fn) _ _ args) pos =
    foldExps sfn efn pos val (fn:args)
foldStmt' sfn efn val (ForeignCall _ _ _ args) pos =
    foldExps sfn efn pos val args
foldStmt' sfn efn val (Cond tst thn els _ _ _) pos = val4
    where val2 = defaultPlacedApply (foldStmt sfn efn val) pos tst
          val3 = foldStmts sfn efn val2 thn
          val4 = foldStmts sfn efn val3 els
foldStmt' sfn efn val (Case exp cases deflt) pos = val4
    where val2 = defaultPlacedApply (foldExp sfn efn val) pos exp
          val3 = List.foldl (foldCase sfn efn) val2 cases
          val4 = maybe val3 (foldStmts sfn efn val3) deflt
foldStmt' sfn efn val (And stmts) pos = foldStmts sfn efn val stmts
foldStmt' sfn efn val (Or stmts _ _) pos = foldStmts sfn efn val stmts
foldStmt' sfn efn val (Not negated) pos =
    defaultPlacedApply (foldStmt sfn efn val) pos negated
foldStmt' sfn efn val (TestBool exp) pos = foldExp sfn efn val exp Nothing
foldStmt' _   _   val Nop pos = val
foldStmt' _   _   val Fail pos = val
foldStmt' sfn efn val (Loop body _ _) pos = foldStmts sfn efn val body
foldStmt' sfn efn val (UseResources _ _ body) pos = foldStmts sfn efn val body
foldStmt' sfn efn val (For generators body) pos = val3
    where val1 = foldExps sfn efn pos val  $ loopVar . content <$> generators
          val2 = foldExps sfn efn pos val1 $ genExp  . content <$> generators
          val3 = foldStmts sfn efn val2 body
foldStmt' _ _ val Break pos = val
foldStmt' _ _ val Next pos = val


-- |Fold over a list of expressions in a pre-order left-to-right traversal.
-- Takes two folding functions, one for statements and one for expressions, plus
-- the position of the outer expression, to be used if the inner expression
-- doesn't have a position.
foldExps :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a) -> OptPos
         -> a -> [Placed Exp] -> a
foldExps sfn efn pos =
    List.foldl (\acc pexp -> defaultPlacedApply (foldExp sfn efn acc) pos pexp)


-- |Fold over an expression and all its subexpressions, in a pre-order
-- left-to-right traversal.  Takes two folding functions, one for statements and
-- one for expressions.
foldExp :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a) -> a
        -> Exp -> OptPos -> a
foldExp sfn efn val exp pos = foldExp' sfn efn (efn val exp pos) exp pos


-- |Fold over all the subexpressions of the given expression, but not the
-- expression itself, in a pre-order left-to-right traversal.
-- Takes two folding functions, one for statements and one for expressions.
foldExp' :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a) -> a
         -> Exp -> OptPos -> a
foldExp' _   _   val IntValue{} pos = val
foldExp' _   _   val FloatValue{} pos = val
foldExp' _   _   val StringValue{} pos = val
foldExp' _   _   val CharValue{} pos = val
foldExp' _   _   val Var{} pos = val
foldExp' _   _   val (Global _) pos = val
foldExp' sfn efn val (Closure _ es) pos = foldExps sfn efn pos val es
foldExp' sfn efn val (AnonProc _ _ pstmts _ _) pos = foldStmts sfn efn val pstmts
foldExp' sfn efn val (AnonFunc exp) _ = placedApply (foldExp sfn efn val) exp
foldExp' sfn efn val (Typed exp _ _) pos = foldExp sfn efn val exp pos
foldExp' _   _   val AnonParamVar{} pos = val
foldExp' sfn efn val (Where stmts exp) pos =
    let val1 = foldStmts sfn efn val stmts
    in  defaultPlacedApply (foldExp sfn efn val1) pos exp
foldExp' sfn efn val (DisjExp e1 e2) pos =
    defaultPlacedApply (foldExp sfn efn (defaultPlacedApply (foldExp sfn efn val) pos e1)) pos e2
foldExp' sfn efn val (CondExp stmt e1 e2) pos =
    let val1 = defaultPlacedApply (foldStmt sfn efn val) pos stmt
        val2 = placedApply (foldExp sfn efn val1) e1
    in         defaultPlacedApply (foldExp sfn efn val2) pos e2
foldExp' sfn efn val (Fncall _ _ _ exps) pos = foldExps sfn efn pos val exps
foldExp' sfn efn val (ForeignFn _ _ _ exps) pos = foldExps sfn efn pos val exps
foldExp' sfn efn val (CaseExp exp cases deflt) pos =
    let val1 = defaultPlacedApply (foldExp sfn efn val) pos exp
        val2 = List.foldl (foldCaseExp sfn efn) val1 cases
    in maybe val2 (defaultPlacedApply (foldExp sfn efn val2) pos) deflt

-- | Fold over the cases in a case statement
foldCase :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a) -> a
         -> (Placed Exp,[Placed Stmt]) -> a
foldCase sfn efn val (pexp, body) =
    foldStmts sfn efn (placedApply (foldExp sfn efn val) pexp) body


-- | Fold over the cases in a case expression
foldCaseExp :: (a -> Stmt -> OptPos -> a) -> (a -> Exp -> OptPos -> a)
            -> a -> (Placed Exp,Placed Exp) -> a
foldCaseExp sfn efn val (pexp, pval) =
    placedApply (foldExp sfn efn (placedApply (foldExp sfn efn val) pexp)) pval

-- |Fold over a ProcBody applying the primFn to each Prim, and
-- combining the results for a sequence of Prims with the abConj
-- function, and combining the results for the arms of a fork with the
-- abDisj function.  The first argument to the abstract primitive
-- operation is a boolean indicating whether the primitive is the last
-- one in the clause.
foldBodyPrims :: (Bool -> Prim -> a -> a) -> a ->
                 (a -> a -> a) -> ProcBody -> a
foldBodyPrims primFn emptyConj abDisj (ProcBody pprims fork) =
    let final  = fork == NoFork
        common = List.foldl
                 (\a tl -> case tl of
                     []       -> a
                     (pp:pps) -> primFn (final && List.null pps) (content pp) a)
                 emptyConj $ tails pprims
    in case fork of
      NoFork -> common
      PrimFork _ _ _ [] _ -> shouldnt "empty clause list in a PrimFork"
      PrimFork _ _ _ (body:bodies) deflt ->
          List.foldl (\a b -> abDisj a $ foldBodyPrims primFn common abDisj b)
                (foldBodyPrims primFn common abDisj body)
                $ bodies ++ maybeToList deflt


-- |Similar to foldBodyPrims, except that it assumes that abstract
-- conjunction distributes over abstract disjunction.  It also ensures
-- that each primitive in the body is abstracted only once by
-- respecting the tree structure of a ProcBody.  The common prims in
-- the body are processed first; then each alternative in the fork is
-- processed, the results are combined with abstract disjunction, and
-- this result is combined with abstraction of the body prims using
-- the abstract conjunction operation.
foldBodyDistrib :: (Bool -> Prim -> a -> a) -> a -> (a -> a -> a) ->
                 (a -> a -> a) -> ProcBody -> a
foldBodyDistrib primFn emptyConj abDisj abConj (ProcBody pprims fork) =
    let final  = fork == NoFork
        common = List.foldl
                 (\a tl -> case tl of
                     []       -> a
                     (pp:pps) -> primFn (final && List.null pps) (content pp) a)
                 emptyConj $ tails pprims
    in case fork of
      NoFork -> common
      PrimFork _ _ _ [] _ -> shouldnt "empty clause list in a PrimFork"
      PrimFork _ _ _ (body:bodies) deflt ->
        abConj common $
        List.foldl (\a b -> abDisj a $ foldBodyDistrib primFn common abDisj abConj b)
        (foldBodyPrims primFn common abDisj body)
        $ bodies ++ maybeToList deflt


-- |Info about a proc call, including the ID, prototype, and an
--  optional source position.
data ProcSpec = ProcSpec {
      procSpecMod :: ModSpec,
      procSpecName :: ProcName,
      procSpecID :: ProcID,
      procSpeczVersion :: SpeczVersion}
                deriving (Eq,Ord,Generic)

instance Show ProcSpec where
    show (ProcSpec mod name pid speczId) =
        showModSpec mod ++ "." ++ name ++ "<" ++ show pid ++ ">"
                ++ if speczId == generalVersion
                   then ""
                   else "[" ++ speczVersionToId speczId ++ "]"

-- |An ID for a proc.
type ProcID = Int

-- |A type specification:  the type name and type parameters.  Also could be
--  AnyType or InvalidType, the top and bottom of the type lattice,
--  respectively.  Finally, it could be a type variable, which can have
--  different representations, so the whole type is parametric in the type of
--  type variables.
data TypeSpec = TypeSpec {
    typeMod::ModSpec,
    typeName::Ident,
    typeParams::[TypeSpec]
    }
    | HigherOrderType {
        higherTypeModifiers::ProcModifiers,
        higherTypeParams::[TypeFlow]
    }
    | TypeVariable { typeVariableName :: TypeVarName }
    | Representation { typeSpecRepresentation :: TypeRepresentation }
    -- the top or bottom of the type lattice, respectively
    | AnyType | InvalidType
              deriving (Eq,Ord,Generic)

-- |Return the set of type variables appearing (recursively) in a TypeSpec.
typeVarSet :: TypeSpec -> Set TypeVarName
typeVarSet TypeSpec{typeParams=params}
    = List.foldr (Set.union . typeVarSet) Set.empty params
typeVarSet HigherOrderType{higherTypeParams=params}
    = List.foldr ((Set.union . typeVarSet) . typeFlowType) Set.empty params
typeVarSet (TypeVariable v) = Set.singleton v
typeVarSet Representation{} = Set.empty
typeVarSet AnyType = Set.empty
typeVarSet InvalidType = Set.empty

genericType :: TypeSpec -> Bool
genericType TypeSpec{typeParams=params} = any genericType params
genericType HigherOrderType{higherTypeParams=params}
    = any (genericType . typeFlowType) params
genericType TypeVariable{}   = True
genericType Representation{} = False
genericType AnyType          = False
genericType InvalidType      = False


-- |Return true if the type is a higher order type or a parameter is a higher
-- order type
higherOrderType :: TypeSpec -> Bool
higherOrderType TypeSpec{typeParams=params} = any higherOrderType params
higherOrderType HigherOrderType{} = True
higherOrderType TypeVariable{}   = False
higherOrderType Representation{} = False
higherOrderType AnyType          = False
higherOrderType InvalidType      = False


-- |Return true if the given type spec is a HigherOrderType
isHigherOrder :: TypeSpec -> Bool
isHigherOrder HigherOrderType{} = True
isHigherOrder _                 = False


-- |Return true if the given type contains a HigherOrderType that is resourceful
isResourcefulHigherOrder :: TypeSpec -> Bool
isResourcefulHigherOrder (HigherOrderType ProcModifiers{modifierResourceful=resful} tfs) =
    resful || any isResourcefulHigherOrder (typeFlowType <$> tfs)
isResourcefulHigherOrder (TypeSpec _ _ tys) =
    any isResourcefulHigherOrder tys
isResourcefulHigherOrder _ = False


-- | Return the module of the specified type, if it has one.
typeModule :: TypeSpec -> Maybe ModSpec
typeModule (TypeSpec mod name _) = Just $ mod ++ [name]
typeModule HigherOrderType{}     = Nothing
typeModule TypeVariable{}        = Nothing
typeModule Representation{}      = Nothing
typeModule AnyType               = Nothing
typeModule InvalidType           = Nothing


-- |This type keeps track of the types of source variables.
type VarDict = Map VarName TypeSpec


data ResourceSpec = ResourceSpec {
    resourceMod::ModSpec,
    resourceName::ResourceName
    } deriving (Eq, Ord, Generic)

instance Show ResourceSpec where
    show (ResourceSpec mod name) =
        maybeModPrefix mod ++ name

data ResourceFlowSpec = ResourceFlowSpec {
    resourceFlowRes::ResourceSpec,
    resourceFlowFlow::FlowDirection
    } deriving (Eq, Ord, Generic)

instance Show ResourceFlowSpec where
    show (ResourceFlowSpec resource dir) =
        flowPrefix dir ++ show resource


-- |A manifest constant.
data Constant = Int Int
              | Float Double
              | Char Char
              | String String
                deriving (Show,Eq)

-- |A proc or func prototype, including name and formal parameters.
data ProcProto = ProcProto {
    procProtoName::ProcName,
    procProtoParams::[Placed Param],
    procProtoResources::Set.Set ResourceFlowSpec
    } deriving (Eq, Generic)


-- |A proc prototype, including name and formal parameters.
data PrimProto = PrimProto {
    primProtoName::ProcName,
    primProtoParams::[PrimParam],
    primProtoGlobalFlows::GlobalFlows
    } deriving (Eq, Generic)


instance Show PrimProto where
    show (PrimProto name params gFlows) =
        name ++ "(" ++ intercalate ", " (List.map show params) ++ ")"
             ++ show gFlows


-- |A formal parameter, including name, type, and flow direction.
data Param = Param {
    paramName::VarName,
    paramType::TypeSpec,
    paramFlow::FlowDirection,
    paramFlowType::ArgFlowType
    } deriving (Eq, Ord, Generic)


-- |The type and mode (flow) of a single argument or parameter
data TypeFlow = TypeFlow {
  typeFlowType :: TypeSpec,
  typeFlowMode :: FlowDirection
  } deriving (Eq, Ord, Generic)

instance Show TypeFlow where
    show (TypeFlow ty fl) = flowPrefix fl ++ show ty


-- |A formal parameter, including name, type, and flow direction.
data PrimParam = PrimParam {
    primParamName::PrimVarName,
    primParamType::TypeSpec,
    primParamFlow::PrimFlow,
    primParamFlowType::ArgFlowType,
    primParamInfo::ParamInfo        -- ^What we've inferred about this param
    } deriving (Eq, Generic)


-- |Info inferred about a single proc parameter
data ParamInfo = ParamInfo {
        paramInfoUnneeded :: Bool, -- ^Can this parameter be eliminated?
        paramInfoGlobalFlows :: GlobalFlows 
    } deriving (Eq,Generic)

-- |A dataflow direction:  in, out, both, or neither.
data FlowDirection = ParamIn | ParamOut | ParamInOut
                   deriving (Show,Eq,Ord,Generic)

-- | A printable version of a flow direction
showFlowName :: FlowDirection -> String
showFlowName ParamIn    = "input"
showFlowName ParamOut   = "output (?)"
showFlowName ParamInOut = "in/output (!)"

-- |A primitive dataflow direction
data PrimFlow =
    --  in or out
    FlowIn | FlowOut
    -- Two "special" flows used to improve last-call optimization.
    -- Users cannot (at present) manually refer to these flows
    | FlowOutByReference | FlowTakeReference
                   deriving (Show,Eq,Ord,Generic)


-- |Set the type of the given Param
setParamType :: TypeSpec -> Param -> Param
setParamType t p = p{paramType=t}

paramIsResourceful :: Param -> Bool
paramIsResourceful (Param _ ty _ _) = isResourcefulHigherOrder ty


-- |Set the type of the given PrimParam
setPrimParamType :: TypeSpec -> PrimParam -> PrimParam
setPrimParamType t p = p{primParamType=t}


-- |Return the TypeSpec and FlowDirection of a Param
paramTypeFlow :: Param -> TypeFlow
paramTypeFlow Param{paramType=ty, paramFlow=fl} = TypeFlow ty fl


-- |Return the TypeSpec and FlowDirection of a PrimParam
primParamTypeFlow :: PrimParam -> TypeFlow
primParamTypeFlow PrimParam{primParamType=ty, primParamFlow=fl}
    = TypeFlow ty $ primFlowToFlowDir fl


-- |Set the ArgFlowType of the given Param
setParamArgFlowType :: ArgFlowType -> Param -> Param
setParamArgFlowType ft p = p{paramFlowType=ft}


-- |Convert a Param to a Var
paramToVar :: Param -> Placed Exp
paramToVar (Param n t f ft)
    = Unplaced $ Typed (Var n f ft) t Nothing


-- |Convert a PrimParam to a PrimArg
primParamToArg :: PrimParam -> PrimArg
primParamToArg (PrimParam nm ty fl ft _) = ArgVar nm ty fl ft False


-- |Set the TypeSpec of a given TypeFlow
setTypeFlowType :: TypeSpec -> TypeFlow -> TypeFlow
setTypeFlowType t tf = tf{typeFlowType=t}

-- |Return the TypeSpec and FlowDirection of a TypeFlow
unzipTypeFlow :: TypeFlow -> (TypeSpec, FlowDirection)
unzipTypeFlow (TypeFlow ty flow) = (ty, flow)


-- |Return the TypeSpecs and FlowDirections of a list of TypeFlows
unzipTypeFlows :: [TypeFlow] -> ([TypeSpec], [FlowDirection])
unzipTypeFlows = unzip . (unzipTypeFlow <$>)


-- |Does the specified flow direction flow in?
flowsIn :: FlowDirection -> Bool
flowsIn ParamIn    = True
flowsIn ParamOut   = False
flowsIn ParamInOut = True


-- |Does the specified flow direction flow out?
flowsOut :: FlowDirection -> Bool
flowsOut ParamIn = False
flowsOut ParamOut = True
flowsOut ParamInOut = True


-- |Translate a PrimFlow to a corresponding FlowDirection
primFlowToFlowDir :: PrimFlow -> FlowDirection
primFlowToFlowDir FlowIn  = ParamIn
primFlowToFlowDir FlowOut = ParamOut
primFlowToFlowDir FlowOutByReference = ParamOut
primFlowToFlowDir FlowTakeReference = ParamIn


-- Returns true if the flow is conceptually an "output"
isInputFlow :: PrimFlow -> Bool
isInputFlow = not . isOutputFlow


-- Returns true if the flow is conceptually an "output"
isOutputFlow :: PrimFlow -> Bool
isOutputFlow FlowOut = True
isOutputFlow FlowOutByReference = True
isOutputFlow FlowTakeReference  = False
isOutputFlow FlowIn  = False


-- |Source program statements.  These will be normalised into Prims.
data Stmt
     -- |A Wybe procedure call, with module, proc name, proc ID, determinism,
     --   and args.  We assume every call is Det until type checking.
     --   The Bool flag indicates that the proc is allowed to use resources.
     = ProcCall ProcFunctor Determinism Bool [Placed Exp]
     -- |A foreign call, with language, foreign name, tags, and args
     | ForeignCall Ident ProcName [Ident] [Placed Exp]
     -- |Do nothing (and succeed)
     | Nop
     -- |Do nothing (and fail)
     | Fail

     -- After unbranching, this can only appear as the last Stmt in a body.

     -- |A conditional; execute the first (SemiDet) Stmt; if it succeeds,
     --  execute the second Stmts, else execute the third.  The VarDicts hold
     --  the variables generated by the condition, and the variables generated
     --  both branches of the conditional, with their types.
     | Cond (Placed Stmt) [Placed Stmt] [Placed Stmt]
            (Maybe VarDict) (Maybe VarDict) (Maybe (Set ResourceSpec))


     -- All the following are eliminated during unbranching.

     -- | A scoped construct for resources.  This creates a context in which the
     --   listed resources can be used, and in which those resources do not
     --   change value. This statement is eliminated during resource processing.
     | UseResources [ResourceSpec] (Maybe VarDict) [Placed Stmt]
     -- |A case statement, which selects the statement sequence corresponding to
     -- the first expression that matches the value of the first argument.  This
     -- is transformed to nested Cond statements.
     | Case (Placed Exp) [(Placed Exp,[Placed Stmt])] (Maybe [Placed Stmt])
     -- |A test that succeeds iff the expression is true
     | TestBool Exp
     -- |A test that succeeds iff all of the enclosed tests succeed
     | And [Placed Stmt]
     -- |A test that succeeds iff any of the enclosed tests succeed; the VarDict
     -- indicates the variables defined after all disjuncts
     | Or [Placed Stmt] (Maybe VarDict) (Maybe (Set ResourceSpec))
     -- |A test that succeeds iff the enclosed test fails
     | Not (Placed Stmt)

     -- |A loop body; the loop is controlled by Breaks and Nexts.  The VarDict
     -- holds the variables that are generated by the loop and their types.
     | Loop [Placed Stmt] (Maybe VarDict) (Maybe (Set ResourceSpec))
     -- |A for loop has multiple generators, which is a variable-iterator pair
     -- and a list of statements in the body
     | For [Placed Generator] [Placed Stmt]
     -- |Immediately exit the enclosing loop; only valid in a loop
     | Break  -- holds the variable versions before the break
     -- |Immediately jump to the top of the enclosing loop; only valid in a loop
     | Next  -- holds the variable versions before the next
     deriving (Eq,Ord,Generic)


instance Show Stmt where
  show s = "{" ++ showStmt 4 s ++ "}"

-- |Produce a single statement comprising the conjunctions of the statements
--  in the supplied list.
seqToStmt :: [Placed Stmt] -> Placed Stmt
seqToStmt [] = Unplaced $ TestBool
               $ Typed (IntValue 1) AnyType $ Just $ TypeSpec ["wybe"] "bool" []
seqToStmt [stmt] = stmt
seqToStmt stmts = Unplaced $ And stmts

-- | Find the Impurity of a sequence of Stmts, the maximum impurity of all
-- statements
stmtsImpurity :: [Placed Stmt] -> Compiler Impurity
stmtsImpurity stmts = List.foldl max PromisedPure
                   <$> mapM (stmtImpurity . content) stmts

-- | The Impurity of a statement
stmtImpurity :: Stmt -> Compiler Impurity
stmtImpurity (ProcCall (First mod name mbId) _ _ _) =
    procImpurity <$> getProcDef
                        (ProcSpec mod name
                            (trustFromJust "stmtImpurity" mbId) generalVersion)
stmtImpurity (ProcCall (Higher fn) _ _ _) =
    case content fn of
        Typed _ (HigherOrderType mods _) _ -> return $ modifierImpurity mods
        _ -> return Impure -- assume the worst case
stmtImpurity (ForeignCall _ _ flags _) = return $ flagsImpurity flags
stmtImpurity (Cond cond thn els _ _ _) = stmtsImpurity $ cond:thn ++ els
stmtImpurity (UseResources _ _ stmts) = stmtsImpurity stmts
stmtImpurity (Case _ cases _) =
    stmtsImpurity . concat $ snd <$> cases
stmtImpurity (And stmts) = stmtsImpurity stmts
stmtImpurity (Or stmts _ _) = stmtsImpurity stmts
stmtImpurity (Not stmt) = stmtImpurity $ content stmt
stmtImpurity (Loop stmts _ _) = stmtsImpurity stmts
stmtImpurity (For _ stmts) = stmtsImpurity stmts
stmtImpurity (TestBool _) = return Pure
stmtImpurity Nop = return Pure
stmtImpurity Fail = return Pure
stmtImpurity Break = return Pure
stmtImpurity Next = return Pure



data ProcFunctor
    = First ModSpec ProcName (Maybe Int)
       -- ^ A first-order procedure
    | Higher (Placed Exp)
       -- ^ A higher-order procedure
    deriving (Eq, Ord, Generic)


regularProc :: ProcName -> ProcFunctor
regularProc name = First [] name Nothing

regularModProc :: ModSpec -> ProcName -> ProcFunctor
regularModProc mod name = First mod name Nothing

-- |An expression.  These are all normalised into statements.
data Exp
      = IntValue Integer
      | FloatValue Double
      | CharValue Char
      | StringValue String StringVariant
      | Var VarName FlowDirection ArgFlowType
      | Closure ProcSpec [Placed Exp]
      | Typed Exp TypeSpec (Maybe TypeSpec)
               -- ^explicitly typed expr giving the type of the expression, and,
               -- if it is a cast, the type of the Exp argument.  If not a cast,
               -- these two must be the same.
      | Global GlobalInfo
      -- The following are eliminated during flattening
      | AnonProc ProcModifiers [Param] [Placed Stmt] (Maybe VarDict) (Maybe (Set ResourceFlowSpec))
      | AnonFunc (Placed Exp)
      | AnonParamVar (Maybe Integer) FlowDirection
      | Where [Placed Stmt] (Placed Exp)
      | DisjExp (Placed Exp) (Placed Exp)
      | CondExp (Placed Stmt) (Placed Exp) (Placed Exp)
      | Fncall ModSpec ProcName Bool [Placed Exp]
      -- ^Bool indicates if the fncall has a !
      | ForeignFn Ident ProcName [Ident] [Placed Exp]
      --- | An expression that matches the first expression against each of the
      --  fst expressions in the list, returning the value of the snd expression
      --  corresponding to the first match; if no match, return the value of
      --  last expr, if there is one, otherwise fail (if no default provided,
      --  the expression is partial)
      | CaseExp (Placed Exp) [(Placed Exp,Placed Exp)] (Maybe (Placed Exp))
     deriving (Eq,Ord,Generic)

-- | Represents which variant a string literal is
data StringVariant = WybeString | CString
   deriving (Eq,Ord,Generic)


-- Information about a global variable.
-- A global variable is a variable that is available everywhere,
-- and can be access via an LPVM load instruction, or written to via an LPVM store
data GlobalInfo = GlobalResource { globalResourceSpec :: ResourceSpec }
    deriving (Eq, Ord, Generic)


-- | Return if the Exp is a Var
expIsVar :: Exp -> Bool
expIsVar Var{}           = True
expIsVar AnonParamVar{}  = True
expIsVar (Typed exp _ _) = expIsVar exp
expIsVar _               = False


-- | Return the FlowDirection of an Exp, assuming it has been flattened.
flattenedExpFlow :: Exp -> FlowDirection
flattenedExpFlow (IntValue _)          = ParamIn
flattenedExpFlow (FloatValue _)        = ParamIn
flattenedExpFlow (CharValue _)         = ParamIn
flattenedExpFlow (StringValue _ _)     = ParamIn
flattenedExpFlow AnonProc{}            = ParamIn
flattenedExpFlow (Closure _ _)         = ParamIn
flattenedExpFlow (Var _ flow _)        = flow
flattenedExpFlow (AnonParamVar _ flow) = flow
flattenedExpFlow (Typed exp _ _)       = flattenedExpFlow exp
flattenedExpFlow otherExp =
    shouldnt $ "Getting flow direction of unflattened exp " ++ show otherExp


-- | If the input is a constant value, return it (with any Typed wrapper
-- removed).  Return Nothing if it's not a constant.
expIsConstant :: Exp -> Maybe Exp
expIsConstant exp@IntValue{}         = Just exp
expIsConstant exp@FloatValue{}       = Just exp
expIsConstant exp@CharValue{}        = Just exp
expIsConstant exp@StringValue{}      = Just exp
expIsConstant exp@(Closure _ closed)
    | all (isJust . expIsConstant . content) closed = Just exp
    | otherwise                                     = Nothing
expIsConstant (Typed exp _ _)        = expIsConstant exp
expIsConstant _                      = Nothing


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

maybeExpType :: Exp -> Maybe TypeSpec
maybeExpType (Typed _ ty _) = Just ty
maybeExpType _              = Nothing

-- | Extract the inner expression (removing any Typed wrapper)
innerExp :: Exp -> Exp
innerExp (Typed exp _ _) = innerExp exp
innerExp exp = exp


setExpFlowType :: Exp -> ArgFlowType -> Exp
setExpFlowType (Typed exp ty cast) ft = Typed (setExpFlowType exp ft) ty cast
setExpFlowType (Var name dir _)    ft = Var name dir ft
setExpFlowType exp                 _  = exp


-- |Is it unnecessary to actually pass an argument (in or out) for this param?
paramIsPhantom :: PrimParam -> Compiler Bool
paramIsPhantom param = typeIsPhantom (primParamType param)


-- |Is the supplied argument a phantom?
argIsPhantom :: PrimArg -> Compiler Bool
argIsPhantom arg = typeIsPhantom $ argType arg


-- |Does the supplied type indicate a phantom?
typeIsPhantom :: TypeSpec -> Compiler Bool
typeIsPhantom ty = do
    rep <- lookupTypeRepresentation ty
    let result = isJust rep && repIsPhantom (fromJust rep)
    logAST $ "Type " ++ show ty ++ " is "
             ++ (if result then "" else "NOT ") ++ "phantom"
    return result


-- |Is the specified type representation a phantom type?
repIsPhantom :: TypeRepresentation -> Bool
repIsPhantom (Bits 0) = True
repIsPhantom _        = False  -- Only 0 bit unsigned ints are phantoms


-- |Get proto param names in a list
primProtoParamNames :: PrimProto -> [PrimVarName]
primProtoParamNames proto = primParamName <$> primProtoParams proto
    -- let formalParams = primProtoParams proto
    -- in [primParamName primParam | primParam <- formalParams]


-- |Get names of proto params that will turn into actual arguments,
--  ie, params that are not phantoms and are not unneeded
protoRealParams :: PrimProto -> Compiler [PrimParam]
protoRealParams = realParams . primProtoParams


-- |Filter a list of params down to the ones that are actually useful,
--  ie, params that are not phantoms and are not unneeded.
realParams :: [PrimParam] -> Compiler [PrimParam]
realParams = filterM paramIsReal


-- |The param actually needs to be passed; ie, it is needed and not phantom.
paramIsReal :: PrimParam -> Compiler Bool
paramIsReal param =
    (paramIsNeeded param &&) . not <$> paramIsPhantom param

paramIsNeeded :: PrimParam -> Bool
paramIsNeeded = not . paramInfoUnneeded . primParamInfo

-- |Get names of proto input params
-- XXX: is this really just input params? or all params
--      was changed in this commit:
--      https://github.com/pschachte/wybe/commit/99749ad485a760813ac63e2addcf8745a824a6e9
protoInputParamNames :: PrimProto -> Compiler [PrimVarName]
protoInputParamNames proto = (primParamName <$>) <$> protoRealParams proto

-- | Get all params matching certain criteria
protoRealParamsWhere :: (PrimParam -> Bool) -> PrimProto -> Compiler [PrimParam]
protoRealParamsWhere f proto = do
    realParams <- protoRealParams proto
    return $ List.filter f realParams

-- |Is the supplied argument a parameter of the proc proto
isProcProtoArg :: [PrimVarName] -> PrimArg -> Bool
isProcProtoArg paramNames arg@ArgVar {} = argVarName arg `elem` paramNames
isProcProtoArg _ _ = False


-- |A loop generator (ie, an iterator).  These need to be
--  generalised, allowing them to be user-defined.
data Generator
      = In { loopVar :: Placed Exp,  -- ^ The variable holding each value
             genExp :: Placed Exp -- ^ The generator being looped over
        } deriving (Eq,Ord,Generic)

-- |A variable name in SSA form, ie, a name and an natural number suffix,
--  where the suffix is used to specify which assignment defines the value.

-- A variable name with an integer suffix to distinguish different
-- values for the same name.  As a special case, a suffix of -1
-- specifies the ultimate, final value for that name.
data PrimVarName =
  PrimVarName {
    primVarName :: VarName,
    primVarNum :: Int
    } deriving (Eq, Ord, Generic)

-- |A primitive statment, including those that can only appear in a
--  loop.
data Prim
     = PrimCall CallSiteID ProcSpec Impurity [PrimArg] GlobalFlows
     | PrimHigher CallSiteID PrimArg Impurity [PrimArg]
     | PrimForeign Ident ProcName [Ident] [PrimArg]
     deriving (Eq,Ord,Generic)

instance Show Prim where
    show = showPrim

-- |An id for each call site, should be unique within a proc.
type CallSiteID = Int


-- |The allowed arguments in primitive proc or foreign proc calls,
--  just variables and constants.
data PrimArg
     = ArgVar {argVarName     :: PrimVarName,  -- ^Name of argument variable
               argVarType     :: TypeSpec,     -- ^Its type
               argVarFlow     :: PrimFlow,     -- ^Its flow direction
               argVarFlowType :: ArgFlowType,  -- ^Its flow type
               argVarFinal    :: Bool          -- ^Is this a definite last use
                                               -- (one use in the last statement
                                               -- to use the variable)
              }
     | ArgInt Integer TypeSpec                 -- ^Constant integer arg
     | ArgFloat Double TypeSpec                -- ^Constant floating point arg
     | ArgString String StringVariant TypeSpec -- ^Constant string arg
     | ArgChar Char TypeSpec                   -- ^Constant character arg
     | ArgClosure ProcSpec [PrimArg] TypeSpec  -- ^Closure, with closed args
     | ArgGlobal GlobalInfo TypeSpec           -- ^Constant global reference
     | ArgUnneeded PrimFlow TypeSpec           -- ^Unneeded input or output
     | ArgUndef TypeSpec                       -- ^Undefined variable, used
                                               --  in failing cases
     deriving (Eq,Ord,Generic)


-- |Returns a list of all arguments to a prim, including global flows
primArgs :: Prim -> ([PrimArg], GlobalFlows)
primArgs (PrimCall _ _ _ args gFlows) = (args, gFlows)
primArgs (PrimHigher _ fn _ args)
    = (fn:args, if isResourcefulHigherOrder $ argType fn
                then univGlobalFlows else emptyGlobalFlows)
primArgs (PrimForeign "lpvm" "load" _ args@[ArgGlobal info _, _])
    = (args, addGlobalFlow info FlowIn emptyGlobalFlows)
primArgs (PrimForeign "lpvm" "store" _ args@[_, ArgGlobal info _])
    = (args, addGlobalFlow info FlowOut emptyGlobalFlows)
primArgs prim@(PrimForeign _ _ _ args) = (args, emptyGlobalFlows)


-- |Replace a Prim's args and global flows with a list of args and global flows
replacePrimArgs :: Prim -> [PrimArg] -> GlobalFlows -> Prim
replacePrimArgs (PrimCall id pspec impurity _ _) args gFlows
    = PrimCall id pspec impurity args gFlows
replacePrimArgs (PrimHigher id _ _ _) [] _
    = shouldnt "replacePrimArgs of higher call with not enough args"
replacePrimArgs (PrimHigher id _ impurity _) (fn:args) _
    = PrimHigher id fn impurity args
replacePrimArgs (PrimForeign lang nm flags _) args _
    = PrimForeign lang nm flags args

-- |Return the GlobalFlows of a prim, given the currently known GlobalFlows 
-- of variables
primGlobalFlows :: Map PrimVarName GlobalFlows -> Prim -> Compiler GlobalFlows
primGlobalFlows varFlows prim@(PrimHigher _ ArgVar{argVarName=name} _ _)
    = return $ Map.findWithDefault (snd $ primArgs prim) name varFlows
primGlobalFlows varFlows prim = do
    let (args, gFlows) = primArgs prim
    argFlows <- argsGlobalFlows varFlows args
    return $ effectiveGlobalFlows argFlows gFlows


-- |Return the GlobalFlows of a PrimArg, given the currently known GlobalFlows 
-- of variables 
argGlobalFlow :: Map PrimVarName GlobalFlows -> PrimArg -> Compiler GlobalFlows
argGlobalFlow varFlows (ArgVar name ty _ _ _) 
    = return $ Map.findWithDefault univGlobalFlows name varFlows
argGlobalFlow varFlows (ArgClosure pspec args _) = do
    params <- getPrimParams pspec 
    let nArgs = length args
        (closedParams, freeParams) = List.splitAt nArgs params
    if any (\(PrimParam _ ty flow _ _) -> 
            isInputFlow flow && isResourcefulHigherOrder ty) freeParams
    then return univGlobalFlows
    else do
        gFlows <- getProcGlobalFlows pspec
        argFlows <- argsGlobalFlows varFlows args
        return $ effectiveGlobalFlows argFlows gFlows
argGlobalFlow _ _ = return emptyGlobalFlows

-- Get the corresponding GlobalFlows and Flows of the given PrimArgs
argsGlobalFlows :: Map PrimVarName GlobalFlows -> [PrimArg] -> Compiler [(GlobalFlows, PrimFlow)]
argsGlobalFlows varFlows 
    = mapM (\a -> (, argFlowDirection a) <$> argGlobalFlow varFlows a)


-- | Gather the effective GlobalFLows of a given set of GlobalGlows, 
-- using the GlobalFlows of the arguments corresponding to each parameter
effectiveGlobalFlows :: [(GlobalFlows, PrimFlow)] -> GlobalFlows -> GlobalFlows
effectiveGlobalFlows argFlows primFlows@(GlobalFlows _ _ UniversalSet) 
    = globalFlowsUnions $ primFlows{globalFlowsParams=emptyUnivSet}
                        : List.map fst (List.filter (isInputFlow . snd) argFlows)
effectiveGlobalFlows argFlows primFlows@(GlobalFlows _ _ (FiniteSet ids)) 
    = globalFlowsUnions $ primFlows{globalFlowsParams=emptyUnivSet}
                        : List.map (fst . (argFlows !!)) (Set.toList ids)


-- | Test if a PrimArg is a variable.
argIsVar :: PrimArg -> Bool
argIsVar ArgVar{} = True
argIsVar _ = False


-- | Test if a PrimArg is a compile-time constant.
argIsConst :: PrimArg -> Bool
argIsConst ArgVar{}            = False
argIsConst ArgInt{}            = True
argIsConst ArgFloat{}          = True
argIsConst ArgString{}         = True
argIsConst ArgChar{}           = True
argIsConst (ArgClosure _ as _) = all argIsConst as
argIsConst ArgGlobal{}         = False
argIsConst ArgUnneeded{}       = False
argIsConst ArgUndef{}          = False


-- | Return Just the integer constant value if a PrimArg iff it is an integer
-- constant.
argIntegerValue :: PrimArg -> Maybe Integer
argIntegerValue (ArgInt val _) = Just val
argIntegerValue _              = Nothing


-- |Relates a primitive argument to the corresponding source argument
data ArgFlowType = Ordinary        -- ^An argument/parameter as written by user
                 | Resource ResourceSpec
                                   -- ^An argument to pass a resource
                 | Free            -- ^An argument to be passed in the closure
                                   -- environment
     deriving (Eq,Ord,Generic)

instance Show ArgFlowType where
    show Ordinary = ""
    show (Resource _) = "%"
    show Free = "^"


-- |The dataflow direction of an actual argument.
argFlowDirection :: PrimArg -> PrimFlow
argFlowDirection ArgVar{argVarFlow=flow} = flow
argFlowDirection ArgInt{} = FlowIn
argFlowDirection ArgFloat{} = FlowIn
argFlowDirection ArgString{} = FlowIn
argFlowDirection ArgChar{} = FlowIn
argFlowDirection ArgClosure{} = FlowIn
argFlowDirection ArgGlobal{} = FlowIn
argFlowDirection (ArgUnneeded flow _) = flow
argFlowDirection ArgUndef{} = FlowIn


-- |Extract the Wybe type of a PrimArg.
argType :: PrimArg -> TypeSpec
argType ArgVar{argVarType=typ} = typ
argType (ArgInt _ typ) = typ
argType (ArgFloat _ typ) = typ
argType (ArgString _ _ typ) = typ
argType (ArgChar _ typ) = typ
argType (ArgClosure _ _ typ) = typ
argType (ArgGlobal _ typ) = typ
argType (ArgUnneeded _ typ) = typ
argType (ArgUndef typ) = typ


-- |Set the Wybe type of a PrimArg.
setArgType :: TypeSpec -> PrimArg -> PrimArg
setArgType typ arg@ArgVar{} = arg{argVarType=typ}
setArgType typ (ArgInt i _) = ArgInt i typ
setArgType typ (ArgFloat f _) = ArgFloat f typ
setArgType typ (ArgString s v ty) = ArgString s v typ
setArgType typ (ArgChar c _) = ArgChar c typ
setArgType typ (ArgClosure ms as _) = ArgClosure ms as typ
setArgType typ (ArgGlobal rs _) = ArgGlobal rs typ
setArgType typ (ArgUnneeded u _) = ArgUnneeded u typ
setArgType typ (ArgUndef _) = ArgUndef typ


-- | Set the flow of a prim arg. This is a nop for a non-ArgVar value
setArgFlow :: PrimFlow -> PrimArg -> PrimArg
setArgFlow f arg@ArgVar{} = arg{argVarFlow=f}
setArgFlow _ arg          = arg

-- | Set the flow type of a prim arg. This is a nop for a non-ArgVar value
setArgFlowType :: ArgFlowType -> PrimArg -> PrimArg
setArgFlowType ft arg@ArgVar{} = arg{argVarFlowType=ft}
setArgFlowType _  arg          = arg


-- | Get the flow of a prim arg. Returns Nothing for a non-ArgVar value
maybeArgFlowType :: PrimArg -> Maybe ArgFlowType
maybeArgFlowType ArgVar{argVarFlowType=ft} = Just ft
maybeArgFlowType arg                       = Nothing


argDescription :: PrimArg -> String
argDescription (ArgVar var _ flow ftype _) =
    argFlowDescription flow
    ++ (case ftype of
          Ordinary       -> " variable " ++ primVarName var
          Resource rspec -> " resource " ++ show rspec
          Free           -> " closure argument ")
argDescription (ArgInt val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgFloat val _) = "constant argument '" ++ show val ++ "'"
argDescription arg@ArgString{} = "constant argument " ++ show arg
argDescription (ArgChar val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgClosure ms as _)
    = "closure of '" ++ show ms ++ "' with <"
    ++ intercalate ", " (argDescription <$> as) ++ "> closed arguments"
argDescription (ArgGlobal info _) = "global reference to " ++ show info
argDescription (ArgUnneeded flow _) = "unneeded " ++ argFlowDescription flow
argDescription (ArgUndef _) = "undefined argument"



-- |A printable description of a primitive flow direction
argFlowDescription :: PrimFlow -> String
argFlowDescription FlowIn  = "input"
argFlowDescription FlowOut = "output"
argFlowDescription FlowOutByReference = "outByReference"
argFlowDescription FlowTakeReference = "takeReference"


argIntVal :: PrimArg -> Maybe Integer
argIntVal (ArgInt val _) = Just val
argIntVal _              = Nothing


-- |Return the integer constant from an argument; error if it's not one
trustArgInt :: PrimArg -> Integer
trustArgInt arg = trustFromJust
                  "LPVM instruction argument must be an integer constant."
                  $ argIntVal arg


-- |Convert a statement read as an expression to a Stmt.
expToStmt :: Exp -> Stmt
expToStmt (Fncall [] "&" False args) = And $ List.map (fmap expToStmt) args
expToStmt (Fncall [] "|" False args) = Or (List.map (fmap expToStmt) args) Nothing Nothing
expToStmt (Fncall [] "~" False [arg]) = Not $ fmap expToStmt arg
expToStmt (Fncall [] "~" False args) = shouldnt $ "non-unary 'not' " ++ show args
expToStmt (Fncall maybeMod name bang args) =
    ProcCall (First maybeMod name Nothing) Det bang args
expToStmt (ForeignFn lang name flags args) =
    ForeignCall lang name flags args
expToStmt (Var name ParamIn _) = ProcCall (First [] name Nothing) Det False []
expToStmt (Var name ParamInOut _) = ProcCall (First [] name Nothing) Det True []
expToStmt expr = shouldnt $ "non-Fncall expr " ++ show expr


procCallToExp :: Stmt -> Exp
procCallToExp (ProcCall (First maybeMod name Nothing) _ bang args) =
    Fncall maybeMod name bang args
procCallToExp stmt =
    shouldnt $ "converting non-proccall to expr " ++ showStmt 4 stmt


-- |Return all input variables to each statement in a list of statements
stmtsInputs :: [Placed Stmt] -> Set VarName
stmtsInputs = foldStmts (const . const)
                        ((const .) . (. expInputs) . Set.union)
                        Set.empty


-- |Return the set of variables that might be freshly assigned by the
-- specified expr.
expOutputs :: Exp -> Set VarName
expOutputs (IntValue _) = Set.empty
expOutputs (FloatValue _) = Set.empty
expOutputs (StringValue _ _) = Set.empty
expOutputs (CharValue _) = Set.empty
expOutputs (Var "_" ParamIn _) = Set.singleton "_" -- special _ variable is out
expOutputs (Var name flow _) =
    if flowsOut flow then Set.singleton name else Set.empty
expOutputs (AnonParamVar mbNum flow) =
    if flowsOut flow then Set.singleton ("@" ++ maybe "" show mbNum) else Set.empty
expOutputs (Global _) = Set.empty
expOutputs AnonProc{} = Set.empty
expOutputs AnonFunc{} = Set.empty
expOutputs (Closure _ _) = Set.empty
expOutputs (Typed expr _ _) = expOutputs expr
expOutputs (DisjExp pexp1 pexp2) = pexpListOutputs [pexp1,pexp2]
expOutputs (Where _ pexp) = expOutputs $ content pexp
expOutputs (CondExp _ pexp1 pexp2) = pexpListOutputs [pexp1,pexp2]
expOutputs (Fncall _ _ _ args) = pexpListOutputs args
expOutputs (ForeignFn _ _ _ args) = pexpListOutputs args
expOutputs (CaseExp _ cases deflt) =
    pexpListOutputs $ maybe id (:) deflt (snd <$> cases)


-- |Return the set of variables that will definitely be freshly assigned by
-- the specified list of placed expressions.
pexpListOutputs :: [Placed Exp] -> Set VarName
pexpListOutputs = List.foldr (Set.union . expOutputs . content) Set.empty


-- |Return the set of variables that are inputs to the given expr.
expInputs :: Exp -> Set VarName
expInputs (IntValue _) = Set.empty
expInputs (FloatValue _) = Set.empty
expInputs (StringValue _ _) = Set.empty
expInputs (CharValue _) = Set.empty
expInputs (Var "_" ParamIn _) = Set.empty
expInputs (Var name flow _) =
    if flowsIn flow then Set.singleton name else Set.empty
expInputs (AnonParamVar mbNum flow) =
    if flowsIn flow then Set.singleton (show mbNum) else Set.empty
expInputs (Global _) = Set.empty
expInputs AnonProc{} = Set.empty
expInputs AnonFunc{} = Set.empty
expInputs (Closure _ _) = Set.empty
expInputs (Typed expr _ _) = expInputs expr
expInputs (Where _ pexp) = expInputs $ content pexp
expInputs (DisjExp pexp1 pexp2) = pexpListInputs [pexp1,pexp2]
expInputs (CondExp _ pexp1 pexp2) = pexpListInputs [pexp1,pexp2]
expInputs (Fncall _ _ _ args) = pexpListInputs args
expInputs (ForeignFn _ _ _ args) = pexpListInputs args
expInputs (CaseExp exp cases deflt) =
    expInputs (content exp)
    `Set.union` pexpListInputs (maybe id (:) deflt (snd <$> cases))
    `Set.union` pexpListInputs (fst <$> cases)



-- |Return the set of variables that are inputs to the the specified list of
-- placed expressions.
pexpListInputs :: [Placed Exp] -> Set VarName
pexpListInputs = List.foldr (Set.union . expInputs . content) Set.empty


-- | Apply the specified TypeFlow to the given expression, ensuring they're
-- explicitly attached to the expression.
setExpTypeFlow :: TypeFlow -> Exp -> Exp
setExpTypeFlow typeflow (Typed expr _ castInner)
    = Typed expr' ty' castInner
    where Typed expr' ty' _ = setExpTypeFlow typeflow expr
setExpTypeFlow (TypeFlow ty fl) (Var name _ ftype)
    = Typed (Var name fl ftype) ty Nothing
setExpTypeFlow (TypeFlow ty ParamIn) expr
    = Typed expr ty Nothing
setExpTypeFlow (TypeFlow ty fl) expr
    = shouldnt $ "Cannot set type/flow of " ++ show expr


-- | Apply the specified TypeFlow to the given expression, ensuring they're
-- explicitly attached to the expression.
setPExpTypeFlow :: TypeFlow -> Placed Exp -> Placed Exp
setPExpTypeFlow typeflow pexpr = setExpTypeFlow typeflow <$> pexpr


----------------------------------------------------------------
--                      Variables (Uses and Defs)
--
-- Finding uses and defines of primitive bodies is made a lot easier
-- by single assignment form:  we just need to find all variable uses
-- or definitions.
----------------------------------------------------------------

varsInPrims :: PrimFlow -> [Prim] -> Set PrimVarName
varsInPrims dir =
    List.foldr (Set.union . (varsInPrim dir)) Set.empty

varsInPrim :: PrimFlow -> Prim     -> Set PrimVarName
varsInPrim dir prim      = let (args, globals) = primArgs prim in varsInPrimArgs dir args

varsInPrimArgs :: PrimFlow -> [PrimArg] -> Set PrimVarName
varsInPrimArgs dir =
    List.foldr (Set.union . varsInPrimArg dir) Set.empty

varsInPrimArg :: PrimFlow -> PrimArg -> Set PrimVarName
varsInPrimArg dir ArgVar{argVarName=var,argVarFlow=dir'}
    = if dir == dir' then Set.singleton var else Set.empty
varsInPrimArg dir (ArgClosure _ as _)
    = Set.unions $ Set.fromList (varsInPrimArg dir <$> as)
varsInPrimArg _ ArgInt{}      = Set.empty
varsInPrimArg _ ArgFloat{}    = Set.empty
varsInPrimArg _ ArgString{}   = Set.empty
varsInPrimArg _ ArgChar{}     = Set.empty
varsInPrimArg _ ArgGlobal{} = Set.empty
varsInPrimArg _ ArgUnneeded{} = Set.empty
varsInPrimArg _ ArgUndef{}    = Set.empty

----------------------------------------------------------------
--                       Generating Symbols

-- | The character we include in every generated identifier to prevent capturing
-- a user identifier.  It should not be possible for the user to include this
-- character in an identifier.
specialChar :: Char
specialChar = '#' -- note # is not allowed in backquoted strings


-- | Construct a name can't be a valid Wybe symbol from one user string.
specialName :: String -> String
specialName = (specialChar:)


-- | Construct a name that can't be a valid Wybe symbol from two user strings.
specialName2 :: String -> String -> String
specialName2 front back = front ++ specialChar:back


-- | The full name to give to a PrimVarName, including the variable number
-- suffix.  Use two specialChars to distinguish from special separator.
numberedVarName :: String -> Int -> String
numberedVarName name number = name ++ specialChar:specialChar:show number


-- | The name to give to the output variable when converting a function to a
-- proc.
outputVariableName :: Ident
outputVariableName = specialName "result"


-- | The name to give to the output status variable when converting a test proc to a Det proc.
outputStatusName :: Ident
outputStatusName = specialName "success"


envParamName :: PrimVarName
envParamName = PrimVarName (specialName "env") 0


envPrimParam :: PrimParam
envPrimParam = PrimParam envParamName AnyType FlowIn Ordinary (ParamInfo False emptyGlobalFlows)


makeGlobalResourceName :: ResourceSpec -> String
makeGlobalResourceName spec = specialName2 "resource" $ show spec

----------------------------------------------------------------
--                      Showing Compiler State
--
-- Each module is shown listing submodules, types, resources and procs
-- it exports, then listing the module imports, and the types,
-- resources and procs it defines, including definitions.  Functions
-- are converted to procs.
--
-- Each proc is shown including whether it is public, how many calls to
-- it appear statically in that module, and whether calls to it
-- shoulds be inlined.  Proc signatures are preceded by a number
-- indicating which overloaded version of the proc is defined.  Formal
-- parameters are preceded by ? to indicate an output; in-out
-- parameters have been converted to a single in and a single out.
-- A parameter not used in the proc body is surrounded with [] brackets.
-- Each variable name is suffixed by a # and a number, indicating
-- which static version of the variable is meant.  The body of a proc
-- is a sequence of proc calls.  Arguments are constant literals or
-- variable references.  Variable references preceded with ? indicate
-- an output argument.  References preceded with ~ indicate that this
-- is the last proc call to refer to this variable (ie, it's dead
-- after this call).


----------------------------------------------------------------

-- | How to show an Item.
instance Show Item where
  show (TypeDecl vis name typeModifiers (TypeRepresentation repn) items pos) =
    visibilityPrefix vis ++ "type " ++ show name
    ++ show typeModifiers
    ++ " is" ++ show repn
    ++ showOptPos pos ++ " {\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\n}\n"
  show (TypeDecl vis name typeModifiers (TypeCtors ctorVis ctors) items pos) =
    visibilityPrefix vis ++ "type " ++ show name
    ++ show typeModifiers
    ++ showOptPos pos ++ "\n    "
    ++ visibilityPrefix vis ++ "constructors "
    ++ intercalate "\n  | " 
        (List.map (\(vis, ctor) -> visibilityPrefix vis ++ show ctor) ctors)
    ++ concatMap (("\n  "++) . show) items
    ++ "\n}\n"
  show (RepresentationDecl params typeModifiers repn pos) =
    "representation"
    ++ bracketList "(" ", " ")" (("?"++) <$> params)
    ++ " is " ++ show typeModifiers ++ show repn ++ showOptPos pos ++ "\n"
  show (ConstructorDecl vis params typeModifiers ctors pos) =
    visibilityPrefix vis ++ "constructors"
    ++ bracketList "(" ", " ")" (("?"++) <$> params) ++ " "
    ++ show typeModifiers
    ++ intercalate " | " (show <$> ctors)
    ++ showOptPos pos ++ "\n"
  show (ImportMods vis mods pos) =
      visibilityPrefix vis ++ "use " ++
      showModSpecs mods ++ showOptPos pos ++ "\n  "
  show (ImportItems vis mod specs pos) =
      visibilityPrefix vis ++ "from " ++ showModSpec mod ++
      " use " ++ intercalate ", " specs
      ++ showOptPos pos ++ "\n  "
  show (ImportForeign files pos) =
      "use foreign object " ++ intercalate ", " files
      ++ showOptPos pos ++ "\n  "
  show (ImportForeignLib names pos) =
      "use foreign library " ++ intercalate ", " names
      ++ showOptPos pos ++ "\n  "
  show (ModuleDecl vis name items pos) =
    visibilityPrefix vis ++ "module " ++ show name ++ " is"
    ++ showOptPos pos ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\n}\n"
  show (ResourceDecl vis name typ init pos) =
    visibilityPrefix vis ++ "resource " ++ name ++ ":" ++ show typ
    ++ maybeShow " = " init " "
    ++ showOptPos pos
  show (FuncDecl vis modifiers proto typ exp pos) =
    visibilityPrefix vis
    ++ "def "
    ++ showProcModifiers' modifiers
    ++ show proto ++ ":" ++ show typ
    ++ showOptPos pos
    ++ " = " ++ show exp
  show (ProcDecl vis modifiers proto stmts pos) =
    visibilityPrefix vis
    ++ "def "
    ++ showProcModifiers' modifiers
    ++ show proto
    ++ showOptPos pos
    ++ " {"
    ++ showBody 4 stmts
    ++ "\n  }"
  show (StmtDecl stmt pos) =
    showStmt 4 stmt ++ showOptPos pos
  show (PragmaDecl prag) =
    "pragma " ++ show prag


-- |How to show a type representation
instance Show TypeRepresentation where
  show Address = "address"
  show (Bits bits) = show bits ++ " bit unsigned"
  show (Signed bits) = show bits ++ " bit signed"
  show (Floating bits) = show bits ++ " bit float"
  show (Func ins outs) =
      "function {" ++ intercalate ", " (List.map show outs) ++ "}"
      ++ "(" ++ intercalate ", " (List.map show ins) ++ ")"


-- |How to show a type family
instance Show TypeFamily where
  show IntFamily   = "integer/address type"
  show FloatFamily = "floating point type"


-- |How to show a ModSpec.
showModSpec :: ModSpec -> String
showModSpec spec = intercalate "." $ (\case "" -> "``" ; m -> m) <$> spec


-- |How to show a list of ModSpecs.
showModSpecs :: [ModSpec] -> String
showModSpecs specs = intercalate ", " $ List.map showModSpec specs


-- |Show a module prefix if specified
maybeModPrefix :: ModSpec -> String
maybeModPrefix modSpec =
    if List.null modSpec then [] else showModSpec modSpec ++ "."


-- |How to show a visibility.
visibilityPrefix :: Visibility -> String
visibilityPrefix Public = "public "
visibilityPrefix Private = ""


-- |How to show an import or use declaration.
showUse :: Int -> ModSpec -> ImportSpec -> String
showUse tab mod (ImportSpec pubs privs) =
    let pubstr = showImports "public " mod pubs
        privstr = showImports "" mod privs
    in  if List.null pubstr || List.null privstr
        then pubstr ++ privstr
        else pubstr ++ "\n" ++ replicate tab ' ' ++ privstr
  where showImports prefix mod UniversalSet = prefix ++ "use " ++ showModSpec mod
        showImports prefix mod (FiniteSet set) =
            if Set.null set
            then ""
            else prefix ++ "from " ++ showModSpec mod ++ " use " ++
                 intercalate ", " (Set.toList set)


-- |How to show a type prototype.
instance Show TypeProto where
  show (TypeProto name []) = name
  show (TypeProto name args) = name ++ "(" ++ intercalate "," args ++ ")"

-- |How to show something that may have a source position
instance Show t => Show (Placed t) where
    show (Placed t pos) = show t ++ showOptPos (Just pos)
    show (Unplaced t) =   show t

-- | How to show a type modifier
instance Show TypeModifiers where
    show (TypeModifiers True _)  = "{unique} "
    show (TypeModifiers False _) = "{}"

-- |How to show an optional source position
showOptPos :: OptPos -> String
-- uncomment to turn off annoying source positions
-- showOptPos _ = ""
-- comment to turn off annoying source positions
showOptPos = maybe "" ((" @" ++) . showSourcePos False)


-- |Show a source position, optionally including directory
showSourcePos :: Bool -> SourcePos -> String
showSourcePos full pos =
  (if full then id else takeBaseName) (sourceName pos) ++ ":"
  ++ show (sourceLine pos) ++ ":" ++ show (sourceColumn pos)


-- |How to show a set of identifiers as a comma-separated list
showIdSet :: Set Ident -> String
showIdSet set = intercalate ", " $ Set.elems set

-- |How to show a type definition.
instance Show TypeDef where
  show (TypeDef vis params rep members _ typeMods pos items) =
    visibilityPrefix vis
    ++ (if List.null params then "" else "(" ++ intercalate "," params ++ ")")
    ++ show typeMods
    ++ maybe "" (" is " ++) (show <$> rep)
    ++ " { "
    ++ intercalate " | " (show <$> members)
    ++ " "
    ++ intercalate "\n  " (show <$> items)
    ++ " } "
    ++ showOptPos pos


-- |How to show a resource definition.
instance Show ResourceImpln where
  show (SimpleResource typ init pos) =
    show typ ++ maybeShow " = " init "" ++ showOptPos pos


-- |How to show a list of proc definitions.
showProcDefs :: Int -> [ProcDef] -> String
showProcDefs _ [] = ""
showProcDefs firstID (def:defs) =
    showProcDef firstID def ++ showProcDefs (1+firstID) defs


-- |How to show a proc definition.
showProcDef :: Int -> ProcDef -> String
showProcDef thisID
  procdef@(ProcDef n proto def pos _ _ _ vis detism inline impurity ctor sub _) =
    "\n"
    ++ showProcName n ++ " > "
    ++ visibilityPrefix vis
    ++ showProcModifiers' (ProcModifiers detism inline impurity ctor False)
    ++ "(" ++ show (procCallCount procdef) ++ " calls)"
    ++ showSuperProc sub
    ++ "\n"
    ++ show thisID ++ ": "
    ++ (if isCompiled def then "" else show proto ++ ":")
    ++ show def


-- | A printable version of a proc name or HO term or foreign proc name.  First
-- argument specifies what kind of proc it is.  Handles special empty proc
-- name.
showProcIdentifier :: String -> ProcName -> String
showProcIdentifier _ ""       = "module top-level code"
showProcIdentifier kind name = kind ++ " " ++ name


-- | A printable version of a proc name; handles special empty proc name.
showProcName :: ProcName -> String
showProcName = showProcIdentifier "proc"


-- |How to show a type specification.
instance Show TypeSpec where
  show AnyType              = "any"
  show InvalidType          = "XXX"
  show (TypeVariable name)  = show name
  show (Representation rep) = show rep
  show (TypeSpec optmod ident args) =
      maybeModPrefix optmod ++ ident ++ showArguments args
  show (HigherOrderType mods params) =
      showProcModifiers mods
      ++ "(" ++ intercalate ", " (show <$> params) ++ ")"


-- |Show the use declaration for a set of resources, if it's non-empty.
showResources :: Set.Set ResourceFlowSpec -> String
showResources resources
  | Set.null resources = ""
  | otherwise          = " use " ++ intercalate ", "
                                    (List.map show $ Set.elems resources)


-- |How to show a proc prototype.
instance Show ProcProto where
  show (ProcProto name params resources) =
    name ++ "(" ++ intercalate ", " (List.map show params) ++ ")" ++
    showResources resources

-- |How to show a formal parameter.
instance Show Param where
  show (Param name typ dir flowType) =
    show flowType ++ flowPrefix dir ++ name ++ showTypeSuffix typ Nothing

-- |How to show a formal parameter.
instance Show PrimParam where
  show (PrimParam name typ dir ft (ParamInfo unneeded flows)) =
      let (pre,post) = if unneeded then ("[","]") else ("","")
          flowStr = if flows == emptyGlobalFlows then "" else " " ++ show flows
      in  pre ++ show ft ++ primFlowPrefix dir ++ show name
          ++ showTypeSuffix typ Nothing ++ flowStr ++ post


-- |Show the type of an expression, if it's known.
showTypeSuffix :: TypeSpec -> Maybe TypeSpec -> String
showTypeSuffix AnyType Nothing     = ""
showTypeSuffix typ Nothing         = ":" ++ show typ
showTypeSuffix typ (Just AnyType)  = ":!" ++ show typ
showTypeSuffix typ (Just cast)     = ":" ++ show typ ++ ":!" ++ show cast


-- |How to show a dataflow direction.
flowPrefix :: FlowDirection -> String
flowPrefix ParamIn    = ""
flowPrefix ParamOut   = "?"
flowPrefix ParamInOut = "!"

-- |How to show a *primitive* dataflow direction.
primFlowPrefix :: PrimFlow -> String
primFlowPrefix FlowIn    = ""
primFlowPrefix FlowOut   = "?"
primFlowPrefix FlowOutByReference   = "outByReference "
primFlowPrefix FlowTakeReference   = "takeReference "

-- |Start a new line with the specified indent.
startLine :: Int -> String
startLine ind = "\n" ++ replicate ind ' '

-- |Show a code block (list of primitive statements) with the
--  specified indent.
showBlock :: Int -> ProcBody -> String
showBlock ind (ProcBody stmts fork) =
    showPlacedPrims ind stmts ++ showFork ind fork


-- |Show a primitive fork.
showFork :: Int -> PrimFork -> String
showFork ind NoFork = ""
showFork ind (PrimFork var ty last bodies deflt) =
    startLine ind ++ "case " ++ (if last then "~" else "") ++ show var ++
                  ":" ++ show ty ++ " of" ++
    List.concatMap (\(val,body) ->
                        startLine ind ++ show val ++ ":" ++
                        showBlock (ind+4) body ++ "\n")
    (zip [0..] bodies)
    ++ maybe "" (\b -> startLine ind ++ "else:"
                       ++ showBlock (ind+4) b ++ "\n") deflt


-- |Show a list of placed prims.
showPlacedPrims :: Int -> [Placed Prim] -> String
showPlacedPrims ind = List.concatMap (showPlacedPrim ind)


-- |Show a single primitive statement with the specified indent.
showPlacedPrim :: Int -> Placed Prim -> String
showPlacedPrim ind stmt = showPlacedPrim' ind (content stmt) (place stmt)


-- |Show a single primitive statement with the specified indent and
--  optional source position.
showPlacedPrim' :: Int -> Prim -> OptPos -> String
showPlacedPrim' ind prim pos =
  startLine ind ++ showPrim prim ++ showOptPos pos


-- |Show a single primitive statement.
showPrim :: Prim -> String
showPrim (PrimCall id pspec _ args globalFlows) =
    show pspec ++ showArguments args
        ++ (if globalFlows == emptyGlobalFlows then "" else show globalFlows)
        ++ " #" ++ show id
showPrim (PrimHigher id var _ args) =
    show var ++ showArguments args ++ " #" ++ show id
showPrim (PrimForeign lang name flags args) =
    "foreign " ++ lang ++ " " ++ showFlags' flags
    ++ name ++ showArguments args


-- |Show a variable, with its suffix.
instance Show PrimVarName where
    show (PrimVarName var suffix) = numberedVarName var suffix


-- |Show a single statement.
showStmt :: Int -> Stmt -> String
showStmt _ (ProcCall func detism resourceful args) =
    (if resourceful then "!" else "")
    ++ show func ++ showArguments args
showStmt _ (ForeignCall lang name flags args) =
    "foreign " ++ lang ++ " " ++ showFlags' flags
    ++ name ++ showArguments args
showStmt _ (TestBool test) =
    "testbool " ++ show test
showStmt indent (And stmts) =
    "(   " ++ intercalate ("\n" ++ replicate indent ' ' ++ "& ")
    (List.map (showStmt indent' . content) stmts) ++
    ")"
    where indent' = indent + 4
showStmt indent (Or stmts genVars res) =
    "(   " ++
    intercalate ("\n" ++ replicate indent ' ' ++ "| ")
        (List.map (showStmt indent' . content) stmts) ++
    ")" ++ maybe "" ((" vars -> "++) . showVarMap) genVars
        ++ maybe "" ((" resources -> "++) . simpleShowSet) res
    where indent' = indent + 4
showStmt indent (Not stmt) =
    "~(" ++ showStmt indent' (content stmt) ++ ")"
    where indent' = indent + 2
showStmt indent (Cond condstmt thn els condVars genVars res) =
    "if {" ++ showStmt (indent+4) (content condstmt) ++ "::\n"
    ++ showBody (indent+4) thn
    ++ startLine indent ++ "else::"
    ++ showBody (indent+4) els ++ "\n"
    ++ startLine indent ++ "}"
    ++ maybe "" (("\n   condition -> "++) . showVarMap) condVars
    ++ maybe "" (("\n   then&else -> "++) . showVarMap) genVars
    ++ maybe "" (("\n   resources -> "++) . simpleShowSet) res
showStmt indent (Case val cases deflt) =
    "case " ++ show val ++ " in {" ++ startLine indent
    ++ concatMap
       (\(exp,body) -> "| " ++ show exp ++ "::" ++ showBody (indent+4) body)
       cases
    ++ maybe "" (("  else::" ++) . showBody (indent+4)) deflt
    ++ startLine indent ++ "}"
showStmt indent (Loop lstmts genVars res) =
    "do {" ++  showBody (indent + 4) lstmts
    ++ startLine indent ++ "}"
    ++ maybe "" ((" vars -> "++) . showVarMap) genVars
    ++ maybe "" ((" resources -> "++) . simpleShowSet) res
showStmt indent (UseResources resources vars stmts) =
    "use " ++ intercalate ", " (List.map show resources)
    ++ " in" ++ showBody (indent + 4) stmts
    ++ startLine indent ++ "}"
    ++ maybe "" (("\n   preserving -> "++) . showVarMap) vars
showStmt _ Fail = "fail"
showStmt _ Nop = "pass"
showStmt indent (For generators body) =
  "for "
    ++ intercalate ", " [show var ++ " in " ++ show gen
                        | (In var gen) <- content <$> generators]
    ++ "{\n"
    ++ showBody (indent + 4) body
    ++ "\n}"
showStmt _ Break = "break"
showStmt _ Next = "next"

instance Show ProcFunctor where
    show (First maybeMod name procID) =
        maybeModPrefix maybeMod
        ++ maybe "" (\n -> "<" ++ show n ++ ">") procID
        ++ name
    show (Higher fn) = show fn


-- |Show a proc body, with the specified indent.
showBody :: Int -> [Placed Stmt] -> String
showBody indent = List.concatMap (\s -> startLine indent ++ showStmt indent (content s))


-- |Show a primitive argument.
instance Show PrimArg where
  show (ArgVar name typ dir ftype final) =
      (if final then "~" else "") ++
      primFlowPrefix dir ++
      show ftype ++
      show name ++ showTypeSuffix typ Nothing
  show (ArgInt i typ)    = show i ++ showTypeSuffix typ Nothing
  show (ArgFloat f typ)  = show f ++ showTypeSuffix typ Nothing
  show (ArgString s v typ) = show v ++ show s ++ showTypeSuffix typ Nothing
  show (ArgChar c typ)   = show c ++ showTypeSuffix typ Nothing
  show (ArgClosure ms as typ) = show ms ++ "<" ++ intercalate ", " (show <$> as)
                             ++ ">" ++ showTypeSuffix typ Nothing
  show (ArgGlobal info typ) = show info ++ showTypeSuffix typ Nothing
  show (ArgUnneeded dir typ) =
      primFlowPrefix dir ++ "_" ++ showTypeSuffix typ Nothing
  show (ArgUndef typ)    = "undef" ++ showTypeSuffix typ Nothing


-- |Show a single typed expression.
instance Show Exp where
  show (IntValue i) = show i
  show (FloatValue f) = show f
  show (StringValue s v) = show v ++ show s
  show (CharValue c) = show c
  show (Var name dir flowtype) = show flowtype ++ flowPrefix dir ++ name
  show (Global info) = show info
  show (AnonProc mods params ss _ _) =
      showProcModifiers mods
      ++ "{" ++ intercalate "; " (showStmt 0 . content <$> ss) ++ "}"
  show (AnonFunc exp) = "@(" ++ show exp ++ ")"
  show (Closure ps es) = show ps ++ "<" ++ intercalate ", " (show <$> es) ++ ">"
  show (AnonParamVar num dir) = flowPrefix dir ++ "@" ++ maybe "" show num
  show (Where stmts exp) = show exp ++ " where" ++ showBody 8 stmts
  show (DisjExp e1 e2) =
    "(" ++ show e1 ++ " | " ++ show e2 ++ ")"
  show (CondExp cond thn els) =
    "if {" ++ show cond ++ ":: " ++ show thn ++ " | " ++ show els ++ "}"
  show (Fncall maybeMod fn bang args) =
    (if bang then "!" else "")
    ++ maybeModPrefix maybeMod ++ fn ++ showArguments args
  show (ForeignFn lang fn flags args) =
    "foreign " ++ lang ++ " " ++ fn
    ++ (if List.null flags then "" else " " ++ unwords flags)
    ++ showArguments args
  show (Typed exp typ cast) =
      show exp ++ showTypeSuffix typ cast
  show (CaseExp exp cases deflt) =
      "case " ++ show exp ++ " in {"
      ++ intercalate " | "
         (List.map (\(e,v) -> show e ++ ":: " ++ show v) cases)
      ++ maybe "" (("| " ++) . show) deflt

-- |Show a string variant prefix
instance Show StringVariant where
    show WybeString = ""
    show CString = "c"

instance Show GlobalInfo where
    show (GlobalResource res) = "<<" ++ show res ++ ">>"



showMap :: String -> String -> String -> (k->String) -> (v->String)
        -> Map k v -> String
showMap pre sep post kfn vfn m =
    pre
    ++ intercalate sep (List.map (\(k,v) -> kfn k ++ vfn v) $ Map.toList m)
    ++ post

-- |Show a readable version of a VarDict showVarMap :: VarDict -> String showVarMap = showVarMap

-- |Show a readable version of a Map from variable names to showable things
showVarMap :: Show a => Map VarName a -> String
showVarMap = showMap "{" ", " "}" (++"::") show

-- |Show a readable version of a Map of showable things
simpleShowMap :: (Show k, Show v) => Map k v -> String
simpleShowMap = showMap "{" ", " "}" ((++"::") . show) show


-- |Show a readable version of a Map of showable things
simpleShowSet :: Show a => Set a -> String
simpleShowSet s =
    "{"
    ++ intercalate ", " (List.map show $ Set.toList s)
    ++ "}"


-- |maybeShow pre maybe post
--  if maybe has something, show pre, the maybe payload, and post
--  if the maybe is Nothing, don't show anything
maybeShow :: Show t => String -> Maybe t -> String -> String
maybeShow pre Nothing post = ""
maybeShow pre (Just something) post =
  pre ++ show something ++ post


------------------------------ Error Reporting -----------------------

-- |Report an internal error and abort.
shouldnt :: String -> a
shouldnt what = error $ "Internal error: " ++ what


-- |Report that some feature is not yet implemented and abort.
nyi :: String -> a
nyi what = error $ "Not yet implemented: " ++ what


-- |Check that all is well, else abort.
checkError :: Monad m => String -> Bool -> m ()
checkError msg bad = when bad $ shouldnt msg


-- |Check that a value is OK; if so, return it, else abort.
checkValue :: (t -> Bool) -> String -> t -> t
checkValue tst msg val = if tst val then val else shouldnt msg


-- |Like fromJust, but with its own error message.
trustFromJust :: String -> Maybe t -> t
trustFromJust msg Nothing = shouldnt $ "trustFromJust in " ++ msg
trustFromJust _ (Just val) = val


-- |Monadic version of trustFromJust.
trustFromJustM :: Monad m => String -> m (Maybe t) -> m t
trustFromJustM msg computation = do
    trustFromJust msg <$> computation


data Message = Message {
    messageLevel :: MessageLevel,  -- ^The inportance of the message
    messagePlace :: OptPos,        -- ^The source location the message refers to
    messageText  :: String         -- ^The text of the message
} deriving (Eq, Ord)

-- Not for displaying error messages, just for debugging printouts.
instance Show Message where
    show (Message lvl pos txt) = show lvl ++ " " ++ show pos ++ ": " ++ txt

-- |Add the specified string as a message of the specified severity
--  referring to the optionally specified source location to the
--  collected compiler output messages.
message :: MessageLevel -> String -> OptPos -> Compiler ()
message lvl msg pos = queueMessage $ Message lvl pos msg


-- |Add the specified message to the collected compiler output messages.
queueMessage :: Message -> Compiler ()
queueMessage msg = do
    modify (\bldr -> bldr { msgs = msg : msgs bldr })
    when (messageLevel msg == Error)
         (modify (\bldr -> bldr { errorState = True }))


-- |Add the specified string as an error message referring to the optionally
--  specified source location to the collected compiler output messages.
errmsg :: OptPos -> String -> Compiler ()
errmsg = flip (message Error)


-- |Pretty helper operator for adding messages to the compiler state.
(<!>) :: MessageLevel -> String -> Compiler ()
lvl <!> msg = message lvl msg Nothing
infix 0 <!>


prettyPos :: OptPos -> IO String
prettyPos Nothing = return ""
prettyPos (Just pos) = do
    relFile <- makeRelativeToCurrentDirectory $ sourceName pos
    return $ relFile ++ ":" ++ show (sourceLine pos)
             ++ ":" ++ show (sourceColumn pos)

-- |Construct a message string from the specified text and location.
makeMessage :: OptPos -> String -> IO String
makeMessage Nothing msg    = return msg
makeMessage pos@(Just _) msg = do
    posStr <- prettyPos pos
    return $ posStr ++ ": " ++ msg


-- |Prettify and show compiler messages. Only Error messages are shown always,
-- the other message levels are shown only when the 'verbose' option is set.
showMessages :: Compiler ()
showMessages = do
    opts <- gets options
    let verbose = optVerbose opts
    let noFonts = optNoFont opts 
    messages <- reverse <$> gets msgs -- messages are collected in reverse order
    let filtered =
            if verbose
            then messages
            else List.filter ((>=Warning) . messageLevel) messages
    liftIO $ mapM_ (showMessage noFonts) $ nubOrd $ sortOn messagePlace filtered


-- |Prettify and show one compiler message.
showMessage :: Bool -> Message -> IO ()
showMessage noFont (Message lvl pos msg) = do
    posMsg <- makeMessage pos msg
    let showMsg colour msg =
            if noFont 
                then putStrLn msg
                else do
                    setSGR [SetColor Foreground Vivid colour]
                    putStrLn msg
                    setSGR [Reset]
    case lvl of
      Informational -> putStrLn posMsg
      Warning       -> showMsg Yellow posMsg
      Error         -> showMsg Red posMsg


-- |Check if any errors have been detected, and if so, print the error messages
-- and exit.
stopOnError :: String -> Compiler ()
stopOnError incident = do
    err <- gets errorState
    when err $ do
        liftIO $ putStrLn $ "Error detected during " ++ incident
        showMessages
        liftIO exitFailure


-- |Log a message, if we are logging AST manipulation.
logAST :: String -> Compiler ()
logAST = logMsg AST


-- | Execute the specified Compiler action if the specified compiler phase is
-- being logged.
whenLogging :: LogSelection -> Compiler () -> Compiler ()
whenLogging selector action = do
    loggingSet <- gets (optLogAspects . options)
    when (Set.member selector loggingSet)
      action


-- | Execute the specified Compiler action if either of the specified compiler
-- phased is being logged.
whenLogging2 :: LogSelection -> LogSelection -> Compiler () -> Compiler ()
whenLogging2 selector1 selector2 action = do
    loggingSet <- gets (optLogAspects . options)
    when (Set.member selector1 loggingSet || Set.member selector2 loggingSet)
      action


-- |Write a log message indicating some aspect of the working of the compiler
logMsg :: LogSelection    -- ^ The aspect of the compiler being logged,
                          -- ^ used to decide whether to log the message
          -> String       -- ^ The log message
          -> Compiler ()  -- ^ Works in the Compiler monad
logMsg selector msg = do
    prefix <- makeBold $ show selector ++ ": "
    whenLogging selector $
      liftIO $ hPutStrLn stderr (prefix ++ List.intercalate ('\n':prefix) (lines msg))

-- | Appends a ISO/IEC 6429 code to the given string to print it bold
-- in a terminal output.
makeBold :: String -> Compiler String
makeBold s = do
    noBold <- gets $ optNoFont . options
    return $ if noBold then s else "\x1b[1m" ++ s ++ "\x1b[0m"


-- | Wrap brackets around a list of strings, with a separator.  If the list
-- is empty, just return the empty string.
bracketList :: String -> String -> String -> [String] -> String
bracketList _ _ _ [] = ""
bracketList prefix sep suffix elts = prefix ++ intercalate sep elts ++ suffix


------------------------------ Module Encoding Types -----------------------

data EncodedLPVM = EncodedLPVM [Module]
                   deriving (Generic)

makeEncodedLPVM :: [Module] -> EncodedLPVM
makeEncodedLPVM = EncodedLPVM
