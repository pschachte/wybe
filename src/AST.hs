--  File     : AST.hs
--  Author   : Peter Schachte
--  Purpose  : Wybe Abstract Syntax Tree and LPVM representation
--  Copyright: (c) 2010-2019 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE DeriveGeneric #-}

-- |The abstract syntax tree, and supporting types and functions.
--  This includes the parse tree, as well as the AST types, which
--  are normalised versions of the parse tree types.
--
--  This also includes the Compiler monad and the Module types.
module AST (
  -- *Types just for parsing
  Item(..), Visibility(..), maxVisibility, minVisibility, isPublic,
  Determinism(..), determinismName,
  TypeProto(..), TypeSpec(..), TypeRef(..), TypeImpln(..),
  ProcProto(..), Param(..), TypeFlow(..), paramTypeFlow,
  PrimProto(..), PrimParam(..), ParamInfo(..),
  Exp(..), Generator(..), Stmt(..), detStmt, expIsConstant,
  TypeRepresentation(..), TypeFamily(..), typeFamily,
  defaultTypeRepresentation, typeRepSize, integerTypeRep,
  lookupTypeRepresentation,
  paramIsPhantom, argIsPhantom, typeIsPhantom, repIsPhantom,
  primProtoParamNames,
  protoRealParams, realParams, paramIsReal,
  protoInputParamNames, isProcProtoArg,
  -- *Source Position Types
  OptPos, Placed(..), place, betterPlace, content, maybePlace, rePlace, unPlace,
  placedApply, placedApply1, placedApplyM, makeMessage, updatePlacedM,
  -- *AST types
  Module(..), ModuleInterface(..), ModuleImplementation(..),
  ImportSpec(..), importSpec, Pragma(..), addPragma,
  descendentModules,
  enterModule, reenterModule, exitModule, reexitModule, deferModules, inModule,
  emptyInterface, emptyImplementation,
  getParams, getDetism, getProcDef, getProcPrimProto,
  mkTempName, updateProcDef, updateProcDefM,
  ModSpec, ProcImpln(..), ProcDef(..), procCallCount,
  AliasMap, aliasMapToAliasPairs,
  AliasMultiSpeczInfo, emptyAliasMultiSpeczInfo,
  SpeczVersionId, speczIdToString, SpeczProcBodies,
  ProcAnalysis(..), ProcBody(..), PrimFork(..), Ident, VarName,
  ProcName, TypeDef(..), ResourceDef(..), ResourceIFace(..), FlowDirection(..),
  argFlowDirection, argType, argDescription, flowsIn, flowsOut,
  foldProcCalls, foldBodyPrims, foldBodyDistrib,
  expToStmt, seqToStmt, procCallToExp, expOutputs, pexpListOutputs,
  setExpTypeFlow, setPExpTypeFlow, isHalfUpdate,
  Prim(..), primArgs, replacePrimArgs, argIsVar, ProcSpec(..),
  PrimVarName(..), PrimArg(..), PrimFlow(..), ArgFlowType(..),
  SuperprocSpec(..), initSuperprocSpec, -- addSuperprocSpec,
  -- *Stateful monad for the compilation process
  MessageLevel(..), updateCompiler,
  CompilerState(..), Compiler, runCompiler,
  updateModules, updateImplementations, updateImplementation,
  getExtractedModuleImpln,
  getModuleImplementationField, getModuleImplementation,
  getLoadedModule, getLoadingModule, updateLoadedModule, updateLoadedModuleM,
  getLoadedModuleImpln, updateLoadedModuleImpln, updateLoadedModuleImplnM,
  getModule, getModuleInterface, updateModule, getSpecModule,
  updateModImplementation, updateModImplementationM, updateModLLVM,
  addForeignImport, addForeignLib,
  updateModInterface, updateAllProcs, updateModSubmods,
  getModuleSpec, getModuleParams, option, getOrigin, getSource, getDirectory,
  optionallyPutStr, message, errmsg, (<!>), genProcName,
  addImport, doImport, addType, lookupType, publicType,
  ResourceName, ResourceSpec(..), ResourceFlowSpec(..), ResourceImpln(..),
  addSimpleResource, lookupResource, publicResource,
  addProc, addProcDef, lookupProc, publicProc,
  refersTo, callTargets,
  showBody, showPlacedPrims, showStmt, showBlock, showProcDef, showModSpec,
  showModSpecs, showResources, showMaybeSourcePos, showProcDefs, showUse,
  shouldnt, nyi, checkError, checkValue, trustFromJust, trustFromJustM,
  maybeShow, showMessages, stopOnError, logMsg, whenLogging2, whenLogging,
  -- *Helper functions
  defaultBlock, moduleIsPackage,
  -- *LPVM Encoding types
  EncodedLPVM(..), ModuleIndex, makeEncodedLPVM
  ) where

import           Config (magicVersion, wordSize, objectExtension,
                         sourceExtension)
import           Control.Monad
import           Control.Monad.Trans (lift,liftIO)
import           Control.Monad.Trans.State
import           Data.List as List
import           Data.Map as Map
import           Data.Maybe
import           Data.Set as Set
import           Data.Word (Word8)
import           Numeric          (showHex)
import           Options
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Directory (makeAbsolute)
-- import           Text.ParserCombinators.Parsec.Pos
import           Text.Parsec.Pos
                 ( SourcePos, sourceName, sourceColumn, sourceLine )
import           Util
import           System.Console.ANSI

import           GHC.Generics (Generic)

import qualified LLVM.AST as LLVMAST

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

-- |An item appearing at the top level of a source file.
data Item
     = TypeDecl Visibility TypeProto TypeImpln [Item] OptPos
     | ModuleDecl Visibility Ident [Item] OptPos
     | ImportMods Visibility [ModSpec] OptPos
     | ImportItems Visibility ModSpec [Ident] OptPos
     | ImportForeign [FilePath] OptPos
     | ImportForeignLib [Ident] OptPos
     | ResourceDecl Visibility ResourceName TypeSpec (Maybe (Placed Exp)) OptPos
       -- The Bool in the next two indicates whether inlining is forced
     | FuncDecl Visibility Determinism Bool
       ProcProto TypeSpec (Placed Exp) OptPos
     | ProcDecl Visibility Determinism Bool ProcProto [Placed Stmt] OptPos
     -- | CtorDecl Visibility ProcProto OptPos
     | StmtDecl Stmt OptPos
     | PragmaDecl Pragma
     deriving (Generic, Eq)

-- |The visibility of a file item.  We only support public and private.
data Visibility = Public | Private
                  deriving (Eq, Show, Generic)

data Determinism = Det | SemiDet
                  deriving (Eq, Ord, Show, Generic)
-- Ordering for Determinism is significant. If x is a the Determinism of a
-- calling context and y is the Determinism of the called proc and x < y means
-- there's a determinism error. This will continue to hold when we add a NonDet
-- determism after SemiDet.


determinismName :: Determinism -> String
determinismName Det = "ordinary"
determinismName SemiDet = "test"


-- | Internal representation of data
data TypeRepresentation
    = Address           -- * A pointer; occupies wordSize bits
    | Bits Int          -- * An unsigned integer representation
    | Signed Int        -- * A signed integer representation
    | Floating Int      -- * A floating point representation
    deriving (Eq, Ord, Generic)


-- | Type representation for opaque things
defaultTypeRepresentation :: TypeRepresentation
defaultTypeRepresentation = Bits wordSize


-- | How many bits a type representation occupies
typeRepSize :: TypeRepresentation -> Int
typeRepSize Address         = wordSize
typeRepSize (Bits bits)     = bits
typeRepSize (Signed bits)   = bits
typeRepSize (Floating bits) = bits


-- | The type representation is for a (signed or unsigned) integer type
integerTypeRep :: TypeRepresentation -> Bool
integerTypeRep Address         = False
integerTypeRep (Bits bits)     = True
integerTypeRep (Signed bits)   = True
integerTypeRep (Floating bits) = False


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
               | TypeCtors Visibility [Placed ProcProto]
               deriving (Generic, Eq)


-- |Combine two visibilities, taking the most visible.
maxVisibility :: Visibility -> Visibility -> Visibility
maxVisibility Public _ = Public
maxVisibility _ Public = Public
maxVisibility _      _ = Private


-- |Combine two visibilities, taking the least visible.
minVisibility :: Visibility -> Visibility -> Visibility
minVisibility Private _ = Private
minVisibility _ Private = Private
minVisibility _       _ = Public


-- |Does the specified visibility make the item public?
isPublic :: Visibility -> Bool
isPublic = (==Public)


-- |A type prototype consists of a type name and zero or more type parameters.
data TypeProto = TypeProto Ident [Ident]
                 deriving (Generic, Eq)


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

-- |Attach a source position to a data value, if one is available.
rePlace :: t -> Placed t -> Placed t
rePlace t (Placed _ pos) = Placed t pos
rePlace t (Unplaced _)   = Unplaced t


-- |Extract the place and payload of a Placed value
unPlace :: Placed t -> (t, OptPos)
unPlace (Placed x pos) = (x, Just pos)
unPlace (Unplaced x)   = (x, Nothing)


-- |Apply a function that takes a thing and an optional place to a
--  placed thing.
placedApply :: (a -> OptPos -> b) -> Placed a -> b
placedApply f placed = f (content placed) (place placed)


-- |Apply a function that takes a thing and an optional place to a
--  placed thing.
placedApply1 :: (c -> a -> OptPos -> b) -> c -> Placed a -> b
placedApply1 f x placed = f x (content placed) (place placed)


-- |Apply a function that takes a thing and an optional place to a
--  placed thing.
placedApplyM :: Monad m => (a -> OptPos -> m b) -> Placed a -> m b
placedApplyM f placed = f (content placed) (place placed)


instance Functor Placed where
  fmap f (Placed x pos) = Placed (f x) pos
  fmap f (Unplaced x) = Unplaced $ f x


-- |Apply a monadic function to the payload of a Placed thing
updatePlacedM :: (t -> Compiler t) -> Placed t -> Compiler (Placed t)
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
  tmpDir  :: FilePath,             -- ^tmp directory for this build
  msgs :: [(MessageLevel, String)],  -- ^warnings, error messages, and info messages
  errorState :: Bool,            -- ^whether or not we've seen any errors
  modules :: Map ModSpec Module, -- ^all known modules except what we're loading
  loadCount :: Int,              -- ^counter of module load order
  underCompilation :: [Module],  -- ^the modules in the process of being compiled
  deferred :: [Module],          -- ^modules in the same SCC as the current one
  extractedMods :: Map ModSpec Module
}

-- |The compiler monad is a state transformer monad carrying the
--  compiler state over the IO monad.
type Compiler = StateT CompilerState IO

-- |Run a compiler function from outside the Compiler monad.
runCompiler :: Options -> Compiler t -> IO t
runCompiler opts comp = evalStateT comp
                        (Compiler opts "" [] False Map.empty 0 [] [] Map.empty)


-- |Apply some transformation function to the compiler state.
-- XXX updateCompiler :: (CompilerState -> (CompilerState, a)) -> Compiler a
updateCompiler :: (CompilerState -> CompilerState) -> Compiler ()
updateCompiler updater = do
    state <- get
    put $ updater state

-- |Apply a monadic transformation function to the compiler state.
-- XXX updateCompilerM :: (CompilerState -> Compiler (CompilerState, a)) -> Compiler a
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
-- XXX updateLoadedModule :: (Module -> (Module, a)) -> ModSpec -> Compiler a
updateLoadedModule :: (Module -> Module) -> ModSpec -> Compiler ()
updateLoadedModule updater modspec = do
    underComp <- gets underCompilation
    let (found,underComp') =
            mapAccumL (\found m -> if (not found) && modSpec m == modspec
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
-- XXX updateLoadedModuleM :: (Module -> Compiler (Module, a)) -> ModSpec -> Compiler a
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
           getLoadedModule modspec
    return $ trustFromJust ("unimplemented module " ++ showModSpec modspec) $
           modImplementation mod



-- |Return the ModuleImplementation of the specified module.  An error
-- if the module is not loaded or does not have an implementation.
updateLoadedModuleImpln :: (ModuleImplementation -> ModuleImplementation) ->
                           ModSpec -> Compiler ()
updateLoadedModuleImpln updater modspec =
    updateLoadedModule (\m -> m { modImplementation =
                                      fmap updater $ modImplementation m })
    modspec


-- |Return the ModuleImplementation of the specified module.  An error
-- if the module is not loaded or does not have an implementation.
-- XXX updateLoadedModuleImplnM ::
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
updateModules updater = do
    modify (\bs -> bs { modules = updater $ modules bs })

-- |Apply some transformation to the map of compiled modules.
updateImplementations :: (ModuleImplementation -> ModuleImplementation) ->
                         Compiler ()
updateImplementations updater = do
    updateModules (Map.map (\m -> m { modImplementation =
                                           (fmap updater) $
                                           modImplementation m }))

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
getSpecModule :: String -> ModSpec -> (Module -> t) -> Compiler t
getSpecModule context spec getter = do
    let msg = context ++ " looking up module " ++ show spec
    underComp <- gets underCompilation
    let curr = List.filter ((==spec) . modSpec) underComp
    logAST $ "Under compilation: " ++ showModSpecs (modSpec <$> underComp)
    logAST $ "found " ++ show (length curr) ++
      " matching modules under compilation"
    case curr of
        []    -> gets (maybe (error msg) getter . Map.lookup spec . modules)
        [mod] -> return $ getter mod
        _     -> shouldnt "getSpecModule: multiple modules with same spec"

-- -- |Return some function of the specified module; returns a Maybe
-- findSpecModule :: ModSpec -> (Module -> t) -> Compiler (Maybe t)
-- findSpecModule spec getter =
--     gets (fmap getter . Map.lookup spec . modules)

-- -- |Transform the specified module.  Does nothing if it does not exist.
-- updateSpecModule :: ModSpec -> (Module -> Module) -> Compiler ()
-- updateSpecModule spec updater = do
--     modify
--       (\comp -> comp { modules = Map.adjust updater spec (modules comp) })


-- -- |Transform the specified module.  An error if it does not exist.
-- updateSpecModuleM :: (Module -> Compiler Module) -> ModSpec -> Compiler ()
-- updateSpecModuleM updater spec =
--     updateCompilerM
--       (\comp -> do
--             let mods = modules comp
--             let mod = Map.lookup spec mods
--             case mod of
--                 Nothing -> shouldnt $ "nonexistent module " ++ show spec
--                 Just m -> do
--                     m' <- updater m
--                     return $ comp {modules = Map.insert spec m' mods})


-- |Prepare to compile a module by setting up a new Module on the
--  front of the list of modules underCompilation.  Match this with
--  a later call to exitModule.
enterModule :: FilePath -> ModSpec -> Maybe ModSpec -> Maybe [Ident]
            -> Compiler ()
enterModule source modspec rootMod params = do
    -- First make sure there's not already such a module
    oldMod <- getLoadingModule modspec
    when (isJust oldMod)
      $ shouldnt $ "enterModule " ++ showModSpec modspec ++ " already exists"
    count <- gets ((1+) . loadCount)
    modify (\comp -> comp { loadCount = count })
    logAST $ "Entering module " ++ showModSpec modspec
             ++ " with count " ++ show count
    absSource <- liftIO $ makeAbsolute source
    modify (\comp -> let newMod = emptyModule
                                  { modOrigin        = absSource
                                  , modRootModSpec   = rootMod
                                  , modSpec          = modspec
                                  , modParams        = params
                                  , thisLoadNum      = count
                                  , minDependencyNum = count
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
    mod <- getSpecModule "reenterModule" modspec id
    modify (\comp -> comp { underCompilation = mod : underCompilation comp })


-- |Finish compilation of the current module.  This matches an earlier
-- call to enterModule.
exitModule :: Compiler [ModSpec]
exitModule = do
    currMod <- getModuleSpec
    imports <- getModuleImplementationField (Map.assocs . modImports)
    logAST $ "Exiting module " ++ showModSpec currMod
              ++ " with imports:\n        "
              ++ intercalate "\n        "
                 [showUse 20 mod dep | (mod,dep) <- imports]
    mod <- reexitModule
    let num = thisLoadNum mod
    logAST $ "Exiting module " ++ showModSpec (modSpec mod)
    logAST $ "    loadNum = " ++ show num ++
           ", minDependencyNum = " ++ show (minDependencyNum mod)
    if minDependencyNum mod < num
      then do
        logAST $ "not finished with module SCC: deferring module "
                 ++ showModSpec (modSpec mod)
        deferModules [mod]
        return []
      else do
        deferred <- gets deferred
        let (bonus,rest) = span ((==num) . minDependencyNum) deferred
        logAST $ "finished with module SCC "
                 ++ showModSpecs (List.map modSpec $ mod:bonus)
        logAST $ "remaining deferred modules: "
                 ++ showModSpecs (List.map modSpec rest)
        modify (\comp -> comp { deferred = rest })
        return $ List.map modSpec $ mod:bonus


-- |Finish a module reentry, returning to the previous module.  This
-- matches an earlier call to reenterModule.
reexitModule :: Compiler Module
reexitModule = do
    mod <- getModule id
    modify
      (\comp -> comp { underCompilation = List.tail (underCompilation comp) })
    updateModules $ Map.insert (modSpec mod) mod
    logAST $ "Reexiting module " ++ showModSpec (modSpec mod)
    return mod


-- |Add the specified module to the list of deferred modules, ie, the
-- modules in the same module dependency SCC as the current one.  This
-- is used for submodules, since they can access stuff in the parent
-- module, and the parent module can access public stuff in submodules.
deferModules :: [Module] -> Compiler ()
deferModules mods = do
    logAST $ "deferred modules "
             ++ showModSpecs (List.map modSpec mods)
    modify (\comp -> comp { deferred = mods ++ deferred comp })


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
-- be a source file or an object file.
getOrigin :: Compiler FilePath
getOrigin = getModule modOrigin

-- |Return the absolute path of the file the source code for the current module
-- *should* be in.  It might not actually be there.
getSource :: Compiler FilePath
getSource = (-<.> sourceExtension) <$> getOrigin

-- |Return the module spec of the current module.
getModuleSpec :: Compiler ModSpec
getModuleSpec = getModule modSpec

-- |Return the module (type) parameters of the current module.
getModuleParams :: Compiler (Maybe [Ident])
getModuleParams = getModule modParams

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


getExtractedModuleImpln :: ModSpec -> Compiler (Maybe ModuleImplementation)
getExtractedModuleImpln mspec = do
    maybeMod <- Map.lookup mspec <$> gets extractedMods
    case maybeMod of
        Nothing -> return Nothing
        Just m -> return $ modImplementation m




-- |Add the specified string as a message of the specified severity
--  referring to the optionally specified source location to the
--  collected compiler output messages.
message :: MessageLevel -> String -> OptPos -> Compiler ()
message lvl msg pos = do
    let posMsg = makeMessage pos msg
    modify (\bldr ->
                bldr { msgs = msgs bldr ++ [(lvl, posMsg)] })
    when (lvl == Error) (modify (\bldr -> bldr { errorState = True }))


-- |Add the specified string as an error message referring to the optionally
--  specified source location to the collected compiler output messages.
errmsg :: String -> OptPos -> Compiler ()
errmsg = message Error


-- |Pretty helper operator for adding messages to the compiler state.
(<!>) :: MessageLevel -> String -> Compiler ()
lvl <!> msg = message lvl msg Nothing
infix 0 <!>

-- |Construct a message string from the specified text and location.
makeMessage :: OptPos -> String -> String
makeMessage Nothing msg = msg
makeMessage (Just pos) msg =
  sourceName pos ++ ":" ++
  show (sourceLine pos) ++ ":" ++
  show (sourceColumn pos) ++ ": " ++
  msg



-- |Return a new, unused proc name.
genProcName :: Compiler ProcName
genProcName = do
  ctr <- getModule procCount
  updateModule (\mod -> mod {procCount = ctr + 1 })
  return $ "gen$" ++ show (ctr + 1)

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

-- |Add the specified type definition to the current module.
addType :: Ident -> TypeDef -> Compiler TypeSpec
addType name def@(TypeDef vis params rep _ _ _ _) = do
    currMod <- getModuleSpec
    let spec = TypeSpec currMod name [] -- XXX what about type params?
    updateImplementation
      (\imp ->
        let set = Set.singleton spec
        in imp { modTypes = Map.insert name def $ modTypes imp,
                 modKnownTypes = Map.insert name set $ modKnownTypes imp })
    updateInterface vis (updatePubTypes (Map.insert name (spec,rep)))
    return spec



-- |Find the definition of the specified type visible from the current module.

lookupType :: TypeSpec -> OptPos -> Compiler (Maybe TypeSpec)
lookupType AnyType _ = return $ Just AnyType
lookupType InvalidType _ = return $ Just InvalidType
lookupType ty@(TypeSpec mod name args) pos = do
    logAST $ "Looking up type " ++ show ty
    tspecs <- refersTo mod name modKnownTypes typeMod
    logAST $ "Candidates: "
             ++ intercalate ", " (List.map show $ Set.toList tspecs)
    case Set.size tspecs of
        0 -> do
            message Error ("Unknown type " ++ show ty) pos
            return Nothing
        1 -> do
            let tspec = Set.findMin tspecs
            maybeMod <- getLoadingModule $ typeMod tspec
            let maybeDef = maybeMod >>= modImplementation >>=
                        (Map.lookup (typeName tspec) . modTypes)
            let def = trustFromJust "lookupType" maybeDef
            if length (typeDefParams def) == length args
              then do
                args' <- fmap catMaybes $ mapM (flip lookupType pos) args
                let matchingMod = maybe (shouldnt "lookupType") modSpec maybeMod
                let matchingType = TypeSpec matchingMod name args'
                logAST $ "Matching type = " ++ show matchingType
                return $ Just matchingType
              else do
                message Error
                  ("Type '" ++ name ++ "' expects "
                   ++ show (length $ typeDefParams def) ++
                   " arguments, but " ++ show (length args) ++ " were given")
                  pos
                logAST "Type constructor arities don't match!"
                return Nothing
        _   -> do
            message Error ("Ambiguous type " ++ show ty ++
                           " defined in modules: " ++
                           showModSpecs (List.map typeMod $
                                         Set.toList tspecs))
              pos
            return Nothing


-- |Is the specified type exported by the current module.
publicType :: Ident -> Compiler Bool
publicType name = do
  int <- getModuleInterface
  return $ Map.member name (pubTypes int)

-- |Add the specified resource to the current module.
addSimpleResource :: ResourceName -> ResourceImpln -> Visibility -> Compiler ()
addSimpleResource name impln vis = do
    currMod <- getModuleSpec
    let rspec = ResourceSpec currMod name
    let rdef = maybePlace (Map.singleton rspec $ Just impln) $
               resourcePos impln
    updateImplementation
      (\imp -> imp { modResources = Map.insert name rdef $ modResources imp,
                     modKnownResources = setMapInsert name rspec $
                                         modKnownResources imp })
    updateInterface vis $ updatePubResources $ Map.insert name rspec


-- |Find the definition of the specified resource visible in the current module.
lookupResource :: ResourceSpec -> OptPos
               -> Compiler (Maybe (ResourceSpec,ResourceIFace))
lookupResource res@(ResourceSpec mod name) pos = do
    logAST $ "Looking up resource " ++ show res
    rspecs <- refersTo mod name modKnownResources resourceMod
    logAST $ "Candidates: " ++ show rspecs
    case Set.size rspecs of
        0 -> do
            message Error ("Unknown resource " ++ show res) pos
            return Nothing
        1 -> do
            let rspec = Set.findMin rspecs
            maybeMod <- getLoadingModule $ resourceMod rspec
            let maybeDef = maybeMod >>= modImplementation >>=
                        (Map.lookup (resourceName rspec) . modResources)
            let iface = resourceDefToIFace $
                        trustFromJust "lookupResource" maybeDef
            return $ Just (rspec,iface)
        _   -> do
            message Error ("Ambiguous resource " ++ show res ++
                           " defined in modules: " ++
                           showModSpecs (List.map resourceMod $
                                         Set.toList rspecs))
              pos
            return Nothing


-- |Is the specified resource exported by the current module.
publicResource :: Ident -> Compiler Bool
publicResource name = getModule (Map.member name . pubResources . modInterface)


-- |Add the specified module spec as an import of the current module.
addImport :: ModSpec -> ImportSpec -> Compiler ()
addImport modspec imports = do
    modspec' <- resolveModuleM modspec
    updateImplementation
      (updateModImports
       (\moddeps ->
         let imports' =
                 case Map.lookup modspec' moddeps of
                     Nothing -> imports
                     Just imports'' -> combineImportSpecs imports'' imports
         in Map.insert modspec' imports' moddeps))
    when (isNothing $ importPublic imports) $
      updateInterface Public (updateDependencies (Set.insert modspec))
    maybeMod <- gets (List.find ((==modspec) . modSpec) . underCompilation)
    currMod <- getModuleSpec
    logAST $ "Noting import of " ++ showModSpec modspec ++
           ", " ++ (if isNothing maybeMod then "NOT " else "") ++
           "currently being loaded, into " ++ showModSpec currMod
    case maybeMod of
        Nothing -> return ()  -- not currently loading dependency
        Just mod' -> do
            logAST $ "Limiting minDependencyNum to " ++
                    show (thisLoadNum mod')
            updateModule (\m -> m { minDependencyNum =
                                        min (thisLoadNum mod')
                                            (minDependencyNum m) })



-- |Add the specified proc definition to the current module.
addProc :: Int -> Item -> Compiler ()
addProc tmpCtr (ProcDecl vis detism inline proto stmts pos) = do
    let name = procProtoName proto
    let procDef = ProcDef name proto (ProcDefSrc stmts) pos tmpCtr
                  Map.empty vis detism inline $ initSuperprocSpec vis
    addProcDef procDef
addProc _ item =
    shouldnt $ "addProc given non-Proc item " ++ show item


addProcDef :: ProcDef -> Compiler ()
addProcDef procDef = do
    let name = procName procDef
    let vis = procVis procDef
    currMod <- getModuleSpec
    procs <- getModuleImplementationField (findWithDefault [] name . modProcs)
    let procs' = procs ++ [procDef]
    let spec = ProcSpec currMod name (length procs) Nothing
    updateImplementation
      (\imp ->
        let known = findWithDefault Set.empty name $ modKnownProcs imp
            known' = Set.insert spec known
        in imp { modProcs = Map.insert name procs' $ modProcs imp,
                 modKnownProcs = Map.insert name known' $ modKnownProcs imp })
    updateInterface vis (updatePubProcs (mapSetInsert name spec))
    logAST $ "Adding definition of " ++ show spec ++ ":" ++
      showProcDef 4 procDef
    return ()


getParams :: ProcSpec -> Compiler [Param]
getParams pspec =
    -- XXX shouldn't have to grovel in implementation to find prototype
    procProtoParams . procProto <$> getProcDef pspec


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
    logAST $ "Looking up proc '" ++ procName ++ "' ID " ++ show procID
    let proc = (modProcs impl ! procName) !! procID
    logAST $ "  proc = " ++ showProcDef 9 proc
    return proc


getProcPrimProto :: ProcSpec -> Compiler PrimProto
getProcPrimProto pspec = do
    def <- getProcDef pspec
    case procImpln def of
        ProcDefPrim proto _ _ _-> return proto
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


-- XXX updateProcDefM :: (ProcDef -> Compiler (ProcDef, a)) -> ProcSpec -> Compiler a
updateProcDefM :: (ProcDef -> Compiler ProcDef) -> ProcSpec -> Compiler ()
updateProcDefM updater pspec@(ProcSpec modspec procName procID _) =
    updateLoadedModuleImplnM
    (\imp -> do
       let procs = modProcs imp
       case Map.lookup procName procs of
         Nothing -> return imp
         Just defs -> do
           let (front,back) = List.splitAt procID defs
           case back of
             [] -> shouldnt $ "invalid proc spec " ++ show pspec
             (this:rest) -> do
               updated <- updater this
               let defs' = front ++ updated:rest
               let procs' = Map.insert procName defs' procs
               return $ imp { modProcs = procs' })
    modspec



-- |Prepend the provided elt to mapping for the specified key in the map.
mapSetInsert :: (Ord a, Ord b) => a -> b -> Map a (Set b) -> Map a (Set b)
mapSetInsert key elt =
    Map.alter (\maybe -> Just $ Set.insert elt $ fromMaybe Set.empty maybe) key


-- |Return the definition of the specified proc in the current module.
lookupProc :: Ident -> Compiler (Maybe [ProcDef])
lookupProc name =
    getModuleImplementationMaybe (\imp -> Map.lookup name $ modProcs imp)


-- |Is the specified proc exported from the current module?
publicProc :: Ident -> Compiler Bool
publicProc name = do
  int <- getModuleInterface
  return $ Map.member name $ pubProcs int


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
  modParams :: Maybe [Ident],      -- ^The type parameters, if a type
  modInterface :: ModuleInterface, -- ^The public face of this module
  modImplementation :: Maybe ModuleImplementation,
                                   -- ^the module's implementation
  thisLoadNum :: Int,              -- ^the loadCount when loading this module
  minDependencyNum :: Int,         -- ^the smallest loadNum of all dependencies
  procCount :: Int,                -- ^a counter for gensym-ed proc names
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
    , modParams         = Nothing
    -- , modConstants      = 0
    -- , modNonConstants   = 0
    , modInterface      = emptyInterface
    , modImplementation = Just emptyImplementation
    , thisLoadNum       = 0
    , minDependencyNum  = 0
    , procCount         = 0
    , stmtDecls         = []
    , itemsHash         = Nothing
    }



descendantModuleOf :: ModSpec -> ModSpec -> Bool
descendantModuleOf sub [] = True
descendantModuleOf (a:as) (b:bs)
  | a == b = descendantModuleOf as bs
descendantModuleOf _ _ = False

parentModule :: ModSpec -> Maybe ModSpec
parentModule []  = Nothing
parentModule [m] = Nothing
parentModule modspec = Just $ init modspec

-- | Collect all the descendent modules of the given modspec.
descendentModules :: ModSpec -> Compiler [ModSpec]
descendentModules mspec = do
    subMods <- fmap (Map.elems . modSubmods) $ getLoadedModuleImpln mspec
    desc <- fmap concat $ mapM descendentModules subMods
    return $ subMods ++ desc



-- |The list of defining modules that the given (possibly
--  module-qualified) name could possibly refer to from the current
--  module.  This may include the current module, or any module it may
--  be imported from.  The implMapFn is a Module selector function that
--  produces a map that tells whether that module exports that name,
--  and implMapFn tells whether a module implementation defines that
--  name.  The reference to this name occurs in the current module.
refersTo :: Ord b => ModSpec -> Ident ->
            (ModuleImplementation -> Map Ident (Set b)) ->
            (b -> ModSpec) -> Compiler (Set b)
refersTo modspec name implMapFn specModFn = do
    currMod <- getModuleSpec
    logAST $ "Finding visible symbol " ++ maybeModPrefix modspec ++
      name ++ " from module " ++ showModSpec currMod
    defined <- getModuleImplementationField
               (Map.findWithDefault Set.empty name . implMapFn)
    -- imports <- getModuleImplementationField (Map.assocs . modImports)
    -- imported <- mapM getLoadingModule imports
    -- let visible = defined `Set.union` imported
    let visible = defined
    logAST $ "*** ALL visible modules: "
        ++ showModSpecs (Set.toList (Set.map specModFn visible))
    let matched = Set.filter ((modspec `isSuffixOf`) . specModFn) visible
    case parentModule currMod of
        Just par -> Set.union matched
                    <$>
                    (refersTo modspec name implMapFn specModFn) `inModule` par
        Nothing -> return matched



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

-- |Holds everything needed to compile code that uses a module
data ModuleInterface = ModuleInterface {
    pubTypes :: Map Ident (TypeSpec,Maybe TypeRepresentation),
                                     -- ^The types this module exports
    pubResources :: Map ResourceName ResourceSpec,
                                     -- ^The resources this module exports
    pubProcs :: Map Ident (Set ProcSpec), -- ^The procs this module exports
    pubDependencies :: Map Ident OptPos,
                                    -- ^The other modules this module exports
    dependencies :: Set ModSpec      -- ^The other modules that must be linked
    }                               --  in by modules that depend on this one
    deriving (Eq, Generic)

emptyInterface :: ModuleInterface
emptyInterface =
    ModuleInterface Map.empty Map.empty Map.empty Map.empty Set.empty

-- These functions hack around Haskell's terrible setter syntax

-- |Update the public types of a module interface.
updatePubTypes :: (Map Ident (TypeSpec,Maybe TypeRepresentation)
                   -> Map Ident (TypeSpec,Maybe TypeRepresentation)) ->
                 ModuleInterface -> ModuleInterface
updatePubTypes fn modint = modint {pubTypes = fn $ pubTypes modint}

-- |Update the public resources of a module interface.
updatePubResources :: (Map Ident ResourceSpec -> Map Ident ResourceSpec) ->
                      ModuleInterface -> ModuleInterface
updatePubResources fn modint = modint {pubResources = fn $ pubResources modint}

-- |Update the public procs of a module interface.
updatePubProcs :: (Map Ident (Set ProcSpec) -> Map Ident (Set ProcSpec)) ->
                 ModuleInterface -> ModuleInterface
updatePubProcs fn modint = modint {pubProcs = fn $ pubProcs modint}

-- |Update the public dependencies of a module interface.
updatePubDependencies ::
    (Map Ident OptPos -> Map Ident OptPos) ->
    ModuleInterface -> ModuleInterface
updatePubDependencies fn modint =
    modint {pubDependencies = fn $ pubDependencies modint}

-- |Update the set of all dependencies of a module interface.
updateDependencies :: (Set ModSpec -> Set ModSpec) ->
                      ModuleInterface -> ModuleInterface
updateDependencies fn modint = modint {dependencies = fn $ dependencies modint}

-- |Holds everything needed to compile the module itself
data ModuleImplementation = ModuleImplementation {
    modPragmas   :: Set Pragma,               -- ^pragmas for this module
    modImports   :: Map ModSpec ImportSpec,   -- ^This module's imports
    modSubmods   :: Map Ident ModSpec,        -- ^This module's submodules
    modTypes     :: Map Ident TypeDef,        -- ^Types defined by this module
    modResources :: Map Ident ResourceDef,    -- ^Resources defined by this mod
    modProcs     :: Map Ident [ProcDef],      -- ^Procs defined by this module
    modKnownTypes:: Map Ident (Set TypeSpec), -- ^Type visible to this module
    modKnownResources :: Map Ident (Set ResourceSpec),
                                              -- ^Resources visible to this mod
    modKnownProcs:: Map Ident (Set ProcSpec), -- ^Procs visible to this module
    modForeignObjects:: Set FilePath,         -- ^Foreign object files used
    modForeignLibs:: Set String,              -- ^Foreign libraries used
    modLLVM :: Maybe LLVMAST.Module           -- ^Module's LLVM representation
    } deriving (Generic)

emptyImplementation :: ModuleImplementation
emptyImplementation =
    ModuleImplementation Set.empty Map.empty Map.empty Map.empty Map.empty
                         Map.empty Map.empty Map.empty Map.empty
                         Set.empty Set.empty Nothing


-- These functions hack around Haskell's terrible setter syntax

-- |Update the dependencies of a module implementation.
updateModImports :: (Map ModSpec ImportSpec -> Map ModSpec ImportSpec) ->
                   ModuleImplementation -> ModuleImplementation
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

-- | Update the LLVMAST.Module representation of the module
updateModLLVM :: (Maybe LLVMAST.Module -> Maybe LLVMAST.Module)
              -> ModuleImplementation
              -> Compiler ModuleImplementation
updateModLLVM fn modimp = do
  let llmod' = fn $ modLLVM modimp
  return $ modimp { modLLVM = llmod'}


-- | Given a type spec, find its internal representation (a string),
--   if possible.
lookupTypeRepresentation :: TypeSpec -> Compiler (Maybe TypeRepresentation)
lookupTypeRepresentation AnyType = return $ Just defaultTypeRepresentation
lookupTypeRepresentation InvalidType = return Nothing
lookupTypeRepresentation (TypeSpec modSpecs name _) = do
    -- logMsg Blocks $ "Looking for " ++ name ++ " in mod: " ++
    --      showModSpec modSpecs
    reenterModule modSpecs
    maybeImpln <- getModuleImplementation
    modInt <- getModuleInterface
    _ <- reexitModule
    -- Try find the TypeRepresentation in the interface
    let maybeIntMatch = Map.lookup name (pubTypes modInt) >>= snd
    -- Try find the TypeRepresentation in the implementation if not found
    -- in the interface
    let maybeMatch = case maybeIntMatch of
            Nothing ->
                maybeImpln >>=
                (Map.lookup name . modTypes) >>= typeDefRepresentation
            _ -> maybeIntMatch
    -- If still not found, search the direct descendant interface and
    -- implementation
    -- case maybeMatch of
    --     Nothing -> case parentModule modSpecs of
    --         Just des -> lookupTypeRepresentation (TypeSpec des name ps)
    --         Nothing -> return Nothing
    --     _ -> return maybeMatch
    return maybeMatch



-- |An identifier.
type Ident = String

-- |A variable name.
type VarName = Ident

-- |A proc name.
type ProcName = Ident

-- |A resource name.
type ResourceName = Ident

-- |A module specification, as a list of module names; module a.b.c would
--  be represented as ["a","b","c"].
type ModSpec = [Ident]


-- |The uses one module makes of another; first the public imports,
--  then the privates.  Each is either Nothing, meaning all exported
--  names are imported, or Just a set of the specific names to import.
data ImportSpec = ImportSpec {
    importPublic::(Maybe (Set Ident)),
    importPrivate::(Maybe (Set Ident))
    } deriving (Show, Generic)


-- |Create an import spec to import the identifiers specified by the
--  first argument (or everything public if it is Nothing), either
--  publicly or privately, as specified by the second argument.
importSpec :: Maybe [Ident] -> Visibility -> ImportSpec
importSpec Nothing Public =
    ImportSpec Nothing (Just Set.empty)
importSpec Nothing Private =
    ImportSpec (Just Set.empty) Nothing
importSpec (Just items) Public =
    ImportSpec (Just $ Set.fromList items) (Just Set.empty)
importSpec (Just items) Private =
    ImportSpec (Just Set.empty) (Just $ Set.fromList items)


-- |Merge two import specs to create a single one that imports
--  exactly what the two together specify.
combineImportSpecs :: ImportSpec -> ImportSpec -> ImportSpec
combineImportSpecs (ImportSpec pub1 priv1) (ImportSpec pub2 priv2) =
    ImportSpec (combineImportPart pub1 pub2) (combineImportPart priv1 priv2)


combineImportPart :: Maybe (Set Ident) -> Maybe (Set Ident) -> Maybe (Set Ident)
combineImportPart Nothing _ = Nothing
combineImportPart _ Nothing = Nothing
combineImportPart (Just set1) (Just set2) = Just (set1 `Set.union` set2)


-- |Actually import into the current module.  The ImportSpec says what
-- to import.
doImport :: ModSpec -> ImportSpec -> Compiler ()
doImport mod imports = do
    currMod <- getModuleSpec
    impl <- getModuleImplementationField id
    logAST $ "Handle importation from " ++ showModSpec mod ++
      " into " ++
      let modStr = showModSpec currMod
      in modStr ++ ":  " ++ showUse (27 + length modStr) mod imports
    fromIFace <- modInterface . trustFromJust "doImport" <$>
                 getLoadingModule mod
    let pubImports = importPublic imports
    let allImports = combineImportPart pubImports $ importPrivate imports
    let importedTypes = importsSelected allImports $ pubTypes fromIFace
    let importedResources = importsSelected allImports $ pubResources fromIFace
    let importedProcs = importsSelected allImports $ pubProcs fromIFace
    logAST $ "    importing types    : "
             ++ intercalate ", " (Map.keys importedTypes)
    logAST $ "    importing resources: "
             ++ intercalate ", " (Map.keys importedResources)
    logAST $ "    importing procs    : "
             ++ intercalate ", " (Map.keys importedProcs)
    -- XXX Must report error for imports of non-exported items
    let knownTypes = Map.unionWith Set.union (modKnownTypes impl) $
                     Map.map (Set.singleton . fst) importedTypes
    let knownResources =
            Map.unionWith Set.union (modKnownResources impl) $
            Map.map Set.singleton importedResources
    let knownProcs = Map.unionWith Set.union (modKnownProcs impl) importedProcs
    -- Update what's visible in the module
    updateModImplementation (\imp -> imp { modKnownTypes = knownTypes,
                                          modKnownResources = knownResources,
                                          modKnownProcs = knownProcs })
    let exportedTypes = importsSelected pubImports $ pubTypes fromIFace
    let exportedResources = importsSelected pubImports $ pubResources fromIFace
    let exportedProcs = importsSelected pubImports $ pubProcs fromIFace
    updateModInterface
      (\i -> i { pubTypes = Map.union (pubTypes i) exportedTypes,
                pubResources = Map.union (pubResources i) exportedResources,
                pubProcs = Map.unionWith Set.union (pubProcs i) exportedProcs })
    -- Update what's exported from the module
    return ()


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




importsSelected :: Maybe (Set Ident) -> Map Ident a -> Map Ident a
importsSelected Nothing items = items
importsSelected (Just these) items =
    Map.filterWithKey (\k _ -> Set.member k these) items


-- | Pragmas that can be specified for a module
data Pragma = NoStd        -- ^ Don't import that standard library for this mod
   deriving (Eq,Ord,Generic)

instance Show Pragma where
    show NoStd = "no_standard_library"


-- |Specify a pragma for the current module
addPragma :: Pragma -> Compiler ()
addPragma prag = do
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
    typeDefOptPos :: OptPos,                      -- source position of decl
    typeDefItems  :: [Item]                       -- other items in decl
    } deriving (Eq, Generic)


-- |A resource interface: everything a module needs to know to use
--  this resource.  Since a resource may be compound (composed of
--  other resources), this is basically a set of resource specs, each
--  with an associated type.
type ResourceIFace = Map ResourceSpec TypeSpec


resourceDefToIFace :: ResourceDef -> ResourceIFace
resourceDefToIFace def =
    Map.map (maybe AnyType resourceType) $ content def


-- |A resource definition.  Since a resource may be defined as a
--  collection of other resources, this is a set of resources (for
--  simple resources, this will be a singleton), each with type and
--  possibly an initial value.  There's also an optional source
-- position.
type ResourceDef = Placed (Map ResourceSpec (Maybe ResourceImpln))

data ResourceImpln =
    SimpleResource {
        resourceType::TypeSpec,
        resourceInit::Maybe (Placed Exp),
        resourcePos::OptPos
        } deriving (Generic)


-- |A proc definition, including the ID, prototype, the body,
--  normalised to a list of primitives, and an optional source
--  position.
data ProcDef = ProcDef {
    procName :: Ident,          -- the proc's name
    procProto :: ProcProto,     -- the proc's prototype
    procImpln :: ProcImpln,     -- the actual implementation
    procPos :: OptPos,          -- where this proc is defined
    procTmpCount :: Int,        -- the next temp variable number to use
    procCallers :: Map ProcSpec Int,
                                -- callers to this proc from this mod in the
                                -- source code (before inlining) and the
                                -- count of calls for each caller
    procVis :: Visibility,      -- what modules should be able to see this?
    procDetism :: Determinism,  -- how many results this proc returns
    procInline :: Bool,         -- should we inline calls to this proc?
    procSuperproc :: SuperprocSpec
                                -- the proc this should be part of, if any
}
             deriving (Eq, Generic)

procCallCount :: ProcDef -> Int
procCallCount proc = Map.foldr (+) 0 $ procCallers proc


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
    = NoSuperproc             -- Cannot be a subproc
    | AnySuperproc            -- Could be a subproc of any proc
    | SuperprocIs ProcSpec    -- May only be a subproc of specified proc
    deriving (Eq, Show, Generic)


-- |The appropriate initial SuperprocSpec given the proc's visibility
initSuperprocSpec :: Visibility -> SuperprocSpec
initSuperprocSpec vis = if isPublic vis then NoSuperproc else AnySuperproc


-- |How to dump a SuperprocSpec
showSuperProc :: SuperprocSpec -> String
showSuperProc NoSuperproc = ""
showSuperProc AnySuperproc = ""
showSuperProc (SuperprocIs super) =
  "(subproc of " ++ show super ++ ")"


-- |A procedure defintion body.  Initially, this is in a form similar
-- to what is read in from the source file.  As compilation procedes,
-- this is gradually refined and constrained, until it is converted
-- into a ProcBody, which is a clausal, logic programming form.
-- Finally it is turned into SSA form (LLVM).
data ProcImpln
    = ProcDefSrc [Placed Stmt]           -- ^defn in source-like form
    | ProcDefPrim PrimProto ProcBody ProcAnalysis SpeczProcBodies
                                         -- ^defn in LPVM (clausal) form
      -- defn in SSA (LLVM) form along with any needed extern definitions
    deriving (Eq,Generic)


-- | The identity of each specialized version. It needs to be a bijection
-- between this Id and the specialized condition. 
-- Currently, [Int] is enought. We can change it to [Tuple] when there 
-- are more things to consider. More detial can be found in [Transform.hs]
type SpeczVersionId = Int


-- Convert [SpeczVersionId] to [String] so it can be shorter in function
-- name.
speczIdToString :: SpeczVersionId -> String
speczIdToString speczId = 
    showHex speczId ""


-- | A map contains different specialization versions.
-- The key is the id of each version and the value is the 
-- actual implementation
type SpeczProcBodies = Map SpeczVersionId ProcBody

-- | Use UnionFind method to record the alias information
type AliasMap = DisjointSet PrimVarName


-- | a synonym function to hide the impletation of how unionfind is printed
showAliasMap :: AliasMap -> String
showAliasMap aliasMap = show $ aliasMapToAliasPairs aliasMap

-- | a synonym function to hide the impletation of how unionfind is converted to
-- alias pairs
aliasMapToAliasPairs :: AliasMap -> [(PrimVarName, PrimVarName)]
aliasMapToAliasPairs aliasMap = Set.toList $ dsToTransitivePairs aliasMap

-- | Multiple specialization info for global alias 
type AliasMultiSpeczInfo = [PrimVarName]


emptyAliasMultiSpeczInfo :: AliasMultiSpeczInfo
emptyAliasMultiSpeczInfo = []


-- | Stores whatever analysis results we infer about a proc definition.
data ProcAnalysis = ProcAnalysis {
    procArgAliasMap :: AliasMap,
    procArgAliasMultiSpeczInfo :: AliasMultiSpeczInfo
} deriving (Eq,Generic)

isCompiled :: ProcImpln -> Bool
isCompiled ProcDefPrim {} = True
isCompiled (ProcDefSrc _) = False

instance Show ProcImpln where
    show (ProcDefSrc stmts) = showBody 4 stmts
    -- TODO: show [SpeczProcBodies]
    show (ProcDefPrim proto body analysis _)
        = show proto ++ ":" ++ show analysis ++ showBlock 4 body

instance Show ProcAnalysis where
    show (ProcAnalysis procArgAliasMap procArgAliasMultiSpeczInfo) =
       "\n AliasPairs: " ++ showAliasMap procArgAliasMap 
       ++ "\n AliasMultiSpeczInfo: "  
       ++ show procArgAliasMultiSpeczInfo


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
      forkBodies::[ProcBody]    -- ^one branch for each value of forkVar
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
mkTempName ctr = "tmp$" ++ show ctr

-- |Make a default LLBlock
defaultBlock :: LLBlock
defaultBlock =  LLBlock { llInstrs = [], llTerm = TermNop }


-- |Fold over a list of Placed Stmts applying the fn to each ProcCall, and
-- applying comb, which must be associative, to combine results.  Results
-- are combined in a right-associative way, with the initial val on the right.
foldProcCalls :: (ModSpec -> Ident -> Maybe Int -> Determinism -> Bool
                  -> [Placed Exp] -> a) ->
                 (a -> a -> a) -> a -> [Placed Stmt] -> a
foldProcCalls _fn _comb val [] = val
foldProcCalls fn comb val (s:ss) = foldProcCalls' fn comb val (content s) ss

foldProcCalls' :: (ModSpec -> Ident -> Maybe Int -> Determinism -> Bool
                   -> [Placed Exp] -> a) ->
                 (a -> a -> a) -> a -> Stmt -> [Placed Stmt] -> a
foldProcCalls' fn comb val (ProcCall m name procID detism res args) ss =
    foldProcCalls fn comb (comb val $ fn m name procID detism res args) ss
foldProcCalls' fn comb val ForeignCall{} ss =
    foldProcCalls fn comb val ss
foldProcCalls' fn comb val (Cond tst thn els) ss =
    foldProcCalls' fn comb
      (foldProcCalls fn comb
        (foldProcCalls fn comb val els)
          thn)
      (content tst)
      ss
foldProcCalls' fn comb val (And stmts) ss =
    foldProcCalls fn comb
      (foldProcCalls fn comb val stmts)
      ss
foldProcCalls' fn comb val (Or stmts) ss =
    foldProcCalls fn comb
      (foldProcCalls fn comb val stmts)
      ss
foldProcCalls' fn comb val (Not stmt) ss =
    foldProcCalls' fn comb val
      (content stmt)
      ss
foldProcCalls' fn comb val TestBool{} ss =
    foldProcCalls fn comb val ss
foldProcCalls' fn comb val Nop ss =
    foldProcCalls fn comb val ss
foldProcCalls' fn comb val (Loop body) ss =
    foldProcCalls fn comb (foldProcCalls fn comb val body) ss
foldProcCalls' fn comb val (UseResources _ body) ss =
    foldProcCalls fn comb (foldProcCalls fn comb val body) ss
-- foldProcCalls' fn comb val For{} ss =
--     foldProcCalls fn comb val ss
foldProcCalls' fn comb val Break ss =
    foldProcCalls fn comb val ss
foldProcCalls' fn comb val Next ss =
    foldProcCalls fn comb val ss


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
      PrimFork _ _ _ [] -> shouldnt "empty clause list in a PrimFork"
      PrimFork _ _ _ (body:bodies) ->
          List.foldl
          (\a b -> abDisj a $ foldBodyPrims primFn common abDisj b)
          (foldBodyPrims primFn common abDisj body)
          bodies


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
      PrimFork _ _ _ [] -> shouldnt "empty clause list in a PrimFork"
      PrimFork _ _ _ (body:bodies) ->
        abConj common $
        List.foldl
        (\a b -> abDisj a $ foldBodyDistrib primFn common abDisj abConj b)
        (foldBodyPrims primFn common abDisj body)
        bodies


-- |Info about a proc call, including the ID, prototype, and an
--  optional source position.
data ProcSpec = ProcSpec {
      procSpecMod :: ModSpec,
      procSpecName :: ProcName,
      procSpecID :: ProcID,
      procSpeczVersionID :: Maybe SpeczVersionId}
                deriving (Eq,Ord,Generic)

instance Show ProcSpec where
    show (ProcSpec mod name pid speczId) =
        showModSpec mod ++ "." ++ name ++ "<" ++ show pid ++ ">"
                ++ case speczId of 
                    Nothing -> ""
                    Just id -> "[" ++ speczIdToString id ++ "]"

-- |An ID for a proc.
type ProcID = Int

-- |A type specification:  the type name and type parameters.  Also
--  could be AnyType or InvalidType, the top and bottom of the type lattice,
--  respectively.
data TypeSpec = TypeSpec {
    typeMod::ModSpec,
    typeName::Ident,
    typeParams::[TypeSpec]
    } | AnyType | InvalidType
              deriving (Eq,Ord,Generic)

-- |This specifies a type, but permits a type to be specified indirectly,
--  as simply identical to the type of another variable, or directly.
data TypeRef = DirectType {typeRefType :: TypeSpec}
             | IndirectType {typeRefVar :: VarName}
             deriving (Eq,Ord)

instance Show TypeRef where
    show (DirectType tspec) = show tspec
    show (IndirectType var) = "@" ++ show var

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
    procProtoParams::[Param],
    procProtoResources::Set.Set ResourceFlowSpec
    } deriving (Eq, Generic)


-- |A proc prototype, including name and formal parameters.
data PrimProto = PrimProto {
    primProtoName::ProcName,
    primProtoParams::[PrimParam]
    } deriving (Eq, Generic)


instance Show PrimProto where
  show (PrimProto name params) =
    name ++ "(" ++ intercalate ", " (List.map show params) ++ ")"


-- |A formal parameter, including name, type, and flow direction.
data Param = Param {
    paramName::VarName,
    paramType::TypeSpec,
    paramFlow::FlowDirection,
    paramFlowType::ArgFlowType
    } deriving (Eq, Generic)


-- |The type and mode (flow) of a single argument or parameter
data TypeFlow = TypeFlow {
  typeFlowType :: TypeSpec,
  typeFlowMode :: FlowDirection
  } deriving (Eq)

instance Show TypeFlow where
    show (TypeFlow ty fl) = flowPrefix fl ++ show ty


-- |Return the TypeSpec and FlowDirection of a Param
paramTypeFlow :: Param -> TypeFlow
paramTypeFlow (Param{paramType=ty, paramFlow=fl}) = TypeFlow ty fl

-- |A formal parameter, including name, type, and flow direction.
data PrimParam = PrimParam {
    primParamName::PrimVarName,
    primParamType::TypeSpec,
    primParamFlow::PrimFlow,
    primParamFlowType::ArgFlowType, -- XXX Not sure this is still needed
    primParamInfo::ParamInfo        -- ^What we've inferred about this param
    } deriving (Eq, Generic)


-- |Info inferred about a single proc parameter
data ParamInfo = ParamInfo {
        paramInfoUnneeded::Bool       -- ^Can this parameter be eliminated?
    } deriving (Eq,Generic)

-- |A dataflow direction:  in, out, both, or neither.
data FlowDirection = ParamIn | ParamOut | ParamInOut | FlowUnknown
                   deriving (Show,Eq,Ord,Generic)

-- |A primitive dataflow direction:  in or out
data PrimFlow = FlowIn | FlowOut
                   deriving (Show,Eq,Ord,Generic)


-- |Does the specified flow direction flow in?
flowsIn :: FlowDirection -> Bool
flowsIn ParamIn    = True
flowsIn ParamOut   = False
flowsIn ParamInOut = True
flowsIn FlowUnknown = shouldnt "checking if unknown flow direction flows in"

-- |Does the specified flow direction flow out?
flowsOut :: FlowDirection -> Bool
flowsOut ParamIn = False
flowsOut ParamOut = True
flowsOut ParamInOut = True
flowsOut FlowUnknown = shouldnt "checking if unknown flow direction flows out"


-- |Source program statements.  These will be normalised into Prims.
data Stmt
     -- |A Wybe procedure call, with module, proc name, proc ID, determinism,
     --   and args.  We assume every call is Det until type checking.
     --   The Bool flag indicates that the proc is allowed to use resources.
     = ProcCall ModSpec Ident (Maybe Int) Determinism Bool [Placed Exp]
     -- |A foreign call, with language, foreign name, tags, and args
     | ForeignCall Ident Ident [Ident] [Placed Exp]
     -- |Do nothing (and succeed)
     | Nop

     -- After unbranching, this con only appear as the last Stmt in a body.

     -- |A conditional; execute the first (SemiDet) Stmts; if they succeed
     --  execute the second Stmts, else execute the third.
     | Cond (Placed Stmt) [Placed Stmt] [Placed Stmt]

     -- | A scoped construct for resources.  This is eliminated during resource
     --   processing.
     | UseResources [ResourceSpec] [Placed Stmt]

     -- All the following are eliminated during unbranching.

     -- |A test that succeeds iff the expression is true
     | TestBool Exp
     -- |A test that fails iff all the enclosed tests fail; enclosed
     | And [Placed Stmt]
     -- |A test that fails iff all the enclosed tests fail; enclosed
     | Or [Placed Stmt]
     -- |A test that fails iff the enclosed test succeeds
     | Not (Placed Stmt)

     -- |A loop body; the loop is controlled by Breaks and Nexts
     | Loop [Placed Stmt]
     -- XXX to handle for loops, need to hoist generator expr out of the loop
     -- -- |An enumerator; only valid in a loop
     -- | For (Placed Exp) (Placed Exp)
     -- |Immediately exit the enclosing loop; only valid in a loop
     | Break  -- holds the variable versions before the break
     -- |Immediately jump to the top of the enclosing loop; only valid in a loop
     | Next  -- holds the variable versions before the next
     deriving (Eq,Ord,Generic)


instance Show Stmt where
  show s = "{" ++ showStmt 4 s ++ "}"

-- |Returns whether the statement is Det
detStmt :: Stmt -> Bool
detStmt (ProcCall _ _ _ SemiDet _ _) = False
detStmt (TestBool _) = False
detStmt (Cond _ thn els) = all detStmt $ List.map content $ thn++els
detStmt (And list) = all detStmt $ List.map content list
detStmt (Or list) = all detStmt $ List.map content list
detStmt (Not _) = False
detStmt _ = True


-- |Produce a single statement comprising the conjunctions of the statements
--  in the supplied list.
seqToStmt :: [Placed Stmt] -> Placed Stmt
seqToStmt [] = Unplaced $ TestBool $ Typed (IntValue 1)
                                           (TypeSpec ["wybe"] "bool" [])
                                           True
seqToStmt [stmt] = stmt
seqToStmt stmts = Unplaced $ And stmts


-- |An expression.  These are all normalised into statements.
data Exp
      = IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Var VarName FlowDirection ArgFlowType
      | Typed Exp TypeSpec Bool       -- ^explicitly typed expr giving type
                                      -- and whether type is a cast
      -- The following are eliminated during flattening
      | Where [Placed Stmt] (Placed Exp)
      | CondExp (Placed Stmt) (Placed Exp) (Placed Exp)
      | Fncall ModSpec Ident [Placed Exp]
      | ForeignFn Ident Ident [Ident] [Placed Exp]
     deriving (Eq,Ord,Generic)


-- | If the input is a constant value, return it (with any Typed wrapper
-- removed).  Return Nothing if it's not a constant.
expIsConstant :: Exp -> Maybe Exp
expIsConstant exp@IntValue{}    = Just exp
expIsConstant exp@FloatValue{}  = Just exp
expIsConstant exp@StringValue{} = Just exp
expIsConstant exp@CharValue{}   = Just exp
expIsConstant (Typed exp _ _)   = expIsConstant exp
expIsConstant _                 = Nothing


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
    ((not $ paramInfoUnneeded $ primParamInfo param) &&) . not
      <$> paramIsPhantom param


-- |Get names of proto input params
protoInputParamNames :: PrimProto -> Compiler [PrimVarName]
protoInputParamNames proto = (primParamName <$>) <$> protoRealParams proto


-- |Is the supplied argument a parameter of the proc proto
isProcProtoArg :: [PrimVarName] -> PrimArg -> Bool
isProcProtoArg paramNames arg@ArgVar {} = argVarName arg `elem` paramNames
isProcProtoArg _ _ = False


-- |A loop generator (ie, an iterator).  These need to be
--  generalised, allowing them to be user-defined.
data Generator
      = In VarName (Placed Exp)

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
     = PrimCall ProcSpec [PrimArg]
     | PrimForeign String ProcName [Ident] [PrimArg]
     | PrimTest PrimArg
     deriving (Eq,Ord,Generic)

instance Show Prim where
    show = showPrim 0

-- |The allowed arguments in primitive proc or foreign proc calls,
--  just variables and constants.
data PrimArg
     = ArgVar {argVarName     :: PrimVarName, -- ^Name of argument variable
               argVarType     :: TypeSpec,    -- ^Its type
               argVarCoerce   :: Bool,        -- ^Whether it must be converted
               argVarFlow     :: PrimFlow,    -- ^Its flow direction
               argVarFlowType :: ArgFlowType, -- ^Its flow type
               argVarFinal    :: Bool         -- ^Is this a definite last use
                                              -- (one use in the last statement
                                              -- to use the variable)
              }
     | ArgInt Integer TypeSpec                -- ^Constant integer arg
     | ArgFloat Double TypeSpec               -- ^Constant floating point arg
     | ArgString String TypeSpec              -- ^Constant string arg
     | ArgChar Char TypeSpec                  -- ^Constant character arg
     | ArgUnneeded PrimFlow TypeSpec          -- ^Unneeded input or output
     deriving (Eq,Ord,Generic)


-- |Returns a list of all arguments to a prim
primArgs :: Prim -> [PrimArg]
primArgs (PrimCall _ args) = args
primArgs (PrimForeign _ _ _ args) = args
primArgs (PrimTest arg) = [arg]


-- |Returns a list of all arguments to a prim
replacePrimArgs :: Prim -> [PrimArg] -> Prim
replacePrimArgs (PrimCall pspec _) args = PrimCall pspec args
replacePrimArgs (PrimForeign lang nm flags _) args =
    PrimForeign lang nm flags args
replacePrimArgs (PrimTest _) [arg] = PrimTest arg
replacePrimArgs instr args =
    shouldnt $ "Attempting to replace arguments of " ++ show instr
               ++ " with " ++ show args


argIsVar :: PrimArg -> Bool
argIsVar ArgVar{} = True
argIsVar _ = False


-- |Relates a primitive argument to the corresponding source argument
data ArgFlowType = Ordinary        -- ^An argument/parameter as written by user
                 | HalfUpdate      -- ^One half of a variable update (!var)
                 | Implicit OptPos -- ^Temp var for expression at that position
                 | Resource ResourceSpec -- ^An argument to pass a resource
     deriving (Eq,Ord,Generic)

instance Show ArgFlowType where
    show Ordinary = ""
    show HalfUpdate = "%"
    show (Implicit _) = ""
    show (Resource _) = "#"


-- |The dataflow direction of an actual argument.
argFlowDirection :: PrimArg -> PrimFlow
argFlowDirection ArgVar{argVarFlow=flow} = flow
argFlowDirection ArgInt{} = FlowIn
argFlowDirection ArgFloat{} = FlowIn
argFlowDirection ArgString{} = FlowIn
argFlowDirection ArgChar{} = FlowIn
argFlowDirection (ArgUnneeded flow _) = flow


-- |Extract the Wybe type of a PrimArg.
argType :: PrimArg -> TypeSpec
argType ArgVar{argVarType=typ} = typ
argType (ArgInt _ typ) = typ
argType (ArgFloat _ typ) = typ
argType (ArgString _ typ) = typ
argType (ArgChar _ typ) = typ
argType (ArgUnneeded _ typ) = typ


argDescription :: PrimArg -> String
argDescription (ArgVar var _ _ flow ftype _) =
    (case flow of
          FlowIn -> "input "
          FlowOut -> "output ") ++
    argFlowDescription flow
    ++ (case ftype of
          Ordinary       -> " variable " ++ primVarName var
          HalfUpdate     -> " update of variable " ++ primVarName var
          Implicit pos   -> " expression" ++ showMaybeSourcePos pos
          Resource rspec -> " resource " ++ show rspec)
argDescription (ArgInt val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgFloat val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgString val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgChar val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgUnneeded flow _) = "unneeded " ++ argFlowDescription flow


-- |A printable description of a primitive flow direction
argFlowDescription :: PrimFlow -> String
argFlowDescription FlowIn  = "input"
argFlowDescription FlowOut = "output"


-- |Convert a statement read as an expression to a Stmt.
expToStmt :: Exp -> Stmt
expToStmt (Fncall [] "&&" args) = And $ List.map (fmap expToStmt) args
expToStmt (Fncall [] "||"  args) = Or  $ List.map (fmap expToStmt) args
expToStmt (Fncall [] "~" [arg]) = Not $ fmap expToStmt arg
expToStmt (Fncall [] "~" args) = shouldnt $ "non-unary 'not' " ++ show args
expToStmt (Fncall maybeMod name args) =
    ProcCall maybeMod name Nothing Det False args
expToStmt (ForeignFn lang name flags args) =
    ForeignCall lang name flags args
expToStmt (Var name ParamIn _) = ProcCall [] name Nothing Det False []
expToStmt (Var name ParamInOut _) = ProcCall [] name Nothing Det True []
expToStmt expr = shouldnt $ "non-Fncall expr " ++ show expr


procCallToExp :: Stmt -> Exp
procCallToExp (ProcCall maybeMod name Nothing _ _ args) =
    Fncall maybeMod name args
procCallToExp stmt =
    shouldnt $ "converting non-proccall to expr " ++ showStmt 4 stmt


-- |Return the set of variables that will definitely be freshly assigned by
-- the specified expr.  Treats FlowUnknown exprs as *not* assigning anything,
-- and ParamInOut exprs as not assigning anything, because it does not
-- *freshly* assign a variable (ie, it's already assigned).
expOutputs :: Exp -> Set VarName
expOutputs (Typed expr _ _) = expOutputs expr
expOutputs (Var name flow _) =
    if flow == ParamOut then Set.singleton name else Set.empty
expOutputs (Fncall _ _ args) = pexpListOutputs args
expOutputs (Where _ pexp) = expOutputs $ content pexp
expOutputs (CondExp _ pexp1 pexp2) = pexpListOutputs [pexp1,pexp2]
expOutputs _ = Set.empty


pexpListOutputs :: [Placed Exp] -> Set VarName
pexpListOutputs = List.foldr (Set.union . expOutputs . content) Set.empty


setExpTypeFlow :: TypeFlow -> Exp -> Exp
setExpTypeFlow typeflow (Typed expr _ cast)
    = Typed expr' ty cast
    where Typed expr' ty _ = setExpTypeFlow typeflow expr
setExpTypeFlow (TypeFlow ty fl) (Var name _ ftype)
    = Typed (Var name fl ftype) ty False
setExpTypeFlow (TypeFlow ty ParamIn) expr
    = Typed expr ty False
setExpTypeFlow (TypeFlow ty fl) expr =
    shouldnt $ "Cannot set type/flow of " ++ show expr


setPExpTypeFlow :: TypeFlow -> Placed Exp -> Placed Exp
setPExpTypeFlow typeflow pexpr = (setExpTypeFlow typeflow) <$> pexpr


isHalfUpdate :: FlowDirection -> Exp -> Bool
isHalfUpdate flow (Typed expr _ _) = isHalfUpdate flow expr
isHalfUpdate flow (Var _ flow' HalfUpdate) = flow == flow'
isHalfUpdate _ _ = False

----------------------------------------------------------------
--                      Variables (Uses and Defs)
--
-- Finding uses and defines of primitive bodies is made a lot easier
-- by single assignment form:  we just need to find all variable uses
-- or definitions.
----------------------------------------------------------------

-- varsInPrims :: PrimFlow -> [Prim] -> Set PrimVarName
-- varsInPrims dir prims =
--     List.foldr Set.union Set.empty $ List.map (varsInPrim dir) prims

-- varsInPrim :: PrimFlow -> Prim     -> Set PrimVarName
-- varsInPrim dir (PrimCall _ args)      = varsInPrimArgs dir args
-- varsInPrim dir (PrimForeign _ _ _ args) = varsInPrimArgs dir args
-- varsInPrim dir (PrimTest arg)         = varsInPrimArgs dir [arg]

-- varsInPrimArgs :: PrimFlow -> [PrimArg] -> Set PrimVarName
-- varsInPrimArgs dir args =
--     List.foldr Set.union Set.empty $ List.map (varsInPrimArg dir) args

varsInPrimArg :: PrimFlow -> PrimArg -> Set PrimVarName
varsInPrimArg dir ArgVar{argVarName=var,argVarFlow=dir'} =
  if dir == dir' then Set.singleton var else Set.empty
varsInPrimArg _ (ArgInt _ _)            = Set.empty
varsInPrimArg _ (ArgFloat _ _)          = Set.empty
varsInPrimArg _ (ArgString _ _)         = Set.empty
varsInPrimArg _ (ArgChar _ _)           = Set.empty
varsInPrimArg _ (ArgUnneeded _ _)       = Set.empty


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

-- |How to show an Item.
instance Show Item where
  show (TypeDecl vis name (TypeRepresentation repn) items pos) =
    visibilityPrefix vis ++ "type " ++ show name
    ++ " is" ++ show repn
    ++ showMaybeSourcePos pos ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\n}\n"
  show (TypeDecl vis name (TypeCtors ctorvis ctors) items pos) =
    visibilityPrefix vis ++ "type " ++ show name
    ++ " " ++ visibilityPrefix ctorvis
    ++ showMaybeSourcePos pos ++ "\n    "
    ++ intercalate "\n  | " (List.map show ctors) ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\n}\n"
  show (ImportMods vis mods pos) =
      visibilityPrefix vis ++ "use " ++
      showModSpecs mods ++ showMaybeSourcePos pos ++ "\n  "
  show (ImportItems vis mod specs pos) =
      visibilityPrefix vis ++ "from " ++ showModSpec mod ++
      " use " ++ intercalate ", " specs
      ++ showMaybeSourcePos pos ++ "\n  "
  show (ImportForeign files pos) =
      "use foreign " ++ intercalate ", " files
      ++ showMaybeSourcePos pos ++ "\n  "
  show (ImportForeignLib names pos) =
      "use foreign library " ++ intercalate ", " names
      ++ showMaybeSourcePos pos ++ "\n  "
  show (ModuleDecl vis name items pos) =
    visibilityPrefix vis ++ "module " ++ show name ++ " is"
    ++ showMaybeSourcePos pos ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\n}\n"
  show (ResourceDecl vis name typ init pos) =
    visibilityPrefix vis ++ "resource " ++ name ++ ":" ++ show typ
    ++ maybeShow " = " init " "
    ++ showMaybeSourcePos pos
  show (FuncDecl vis detism inline proto typ exp pos) =
    visibilityPrefix vis
    ++ determinismPrefix detism
    ++ (if inline then "inline " else "")
    ++ "func " ++ show proto ++ ":" ++ show typ
    ++ showMaybeSourcePos pos
    ++ " = " ++ show exp
  show (ProcDecl vis detism inline proto stmts pos) =
    visibilityPrefix vis
    ++ determinismPrefix detism
    ++ (if inline then "inline " else "")
    ++ "proc " ++ show proto
    ++ showMaybeSourcePos pos
    ++ " {"
    ++ showBody 4 stmts
    ++ "\n  }"
  show (StmtDecl stmt pos) =
    showStmt 4 stmt ++ showMaybeSourcePos pos
  show (PragmaDecl prag) =
    "pragma " ++ show prag


-- |How to show a type representation
instance Show TypeRepresentation where
  show Address = "address"
  show (Bits bits) = show bits ++ " bit unsigned"
  show (Signed bits) = show bits ++ " bit signed"
  show (Floating bits) = show bits ++ " bit float"


-- |How to show a type family
instance Show TypeFamily where
  show IntFamily   = "integer/address type"
  show FloatFamily = "floating point type"


-- |How to show a ModSpec.
showModSpec :: ModSpec -> String
showModSpec spec = intercalate "." spec


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


-- |How to show a determinism.
determinismPrefix :: Determinism -> String
determinismPrefix SemiDet = "test "
determinismPrefix Det = ""


-- |How to show an import or use declaration.
showUse :: Int -> ModSpec -> ImportSpec -> String
showUse tab mod (ImportSpec pubs privs) =
    let pubstr = showImports "public " mod pubs
        privstr = showImports "" mod privs
    in  if List.null pubstr || List.null privstr
        then pubstr ++ privstr
        else pubstr ++ "\n" ++ replicate tab ' ' ++ privstr
  where showImports prefix mod Nothing = prefix ++ "use " ++ showModSpec mod
        showImports prefix mod (Just set) =
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
    show (Placed t pos) = show t ++ showMaybeSourcePos (Just pos)
    show (Unplaced t) =   show t


-- |How to show an optional source position
showMaybeSourcePos :: OptPos -> String
-- uncomment turn off annoying source positions
-- showMaybeSourcePos _ = ""
-- comment to turn off annoying source positions
showMaybeSourcePos (Just pos) =
  " @" ++ takeBaseName (sourceName pos) ++ ":"
  ++ show (sourceLine pos) ++ ":" ++ show (sourceColumn pos)
showMaybeSourcePos Nothing = ""


--showTypeMap :: Map Ident TypeDef -> String

-- |How to show a set of identifiers as a comma-separated list
showIdSet :: Set Ident -> String
showIdSet set = intercalate ", " $ Set.elems set

-- |How to show a type definition.
instance Show TypeDef where
  show (TypeDef vis params rep members _ pos items) =
    visibilityPrefix vis
    ++ (if List.null params then "" else "(" ++ intercalate "," params ++ ")")
    ++ maybe "" (" is " ++) (show <$> rep)
    ++ " { "
    ++ intercalate " | " (show <$> members)
    ++ " "
    ++ intercalate "\n  " (show <$> items)
    ++ " } "
    ++ showMaybeSourcePos pos


-- |How to show a resource definition.
instance Show ResourceImpln where
  show (SimpleResource typ init pos) =
    show typ ++ maybeShow " = " init "" ++ showMaybeSourcePos pos


-- |How to show a list of proc definitions.
showProcDefs :: Int -> [ProcDef] -> String
showProcDefs _ [] = ""
showProcDefs firstID (def:defs) =
    showProcDef firstID def ++ showProcDefs (1+firstID) defs


-- |How to show a proc definition.
showProcDef :: Int -> ProcDef -> String
showProcDef thisID procdef@(ProcDef n proto def pos _ _ vis detism inline sub) =
    "\n"
    ++ (if n == "" then "*main*" else n) ++ " > "
    ++ visibilityPrefix vis
    ++ (if inline then "inline " else "")
    ++ determinismPrefix detism
    ++ "(" ++ show (procCallCount procdef) ++ " calls)"
    ++ showSuperProc sub
    ++ "\n"
    ++ show thisID ++ ": "
    ++ (if isCompiled def then "" else show proto ++ ":")
    ++ show def


-- |How to show a type specification.
instance Show TypeSpec where
  show AnyType = "?"
  show InvalidType = "XXX"
  show (TypeSpec optmod ident args) =
      maybeModPrefix optmod ++ ident ++
      if List.null args then ""
      else "(" ++ (intercalate "," $ List.map show args) ++ ")"

-- |Show the use declaration for a set of resources, if it's non-empty.
showResources :: Set.Set ResourceFlowSpec -> String
showResources resources
  | Set.null resources = ""
  | otherwise          = " use " ++ intercalate ", "
                                    (List.map show $ Set.elems resources)


-- |How to show a proc prototype.
instance Show ProcProto where
  show (ProcProto name params resources) =
    name ++ "(" ++ (intercalate ", " $ List.map show params) ++ ")" ++
    showResources resources

-- |How to show a formal parameter.
instance Show Param where
  show (Param name typ dir flowType) =
    (show flowType) ++ flowPrefix dir ++ name ++ showTypeSuffix typ False

-- |How to show a formal parameter.
instance Show PrimParam where
  show (PrimParam name typ dir _ (ParamInfo unneeded)) =
      let (pre,post) = if unneeded then ("[","]") else ("","")
      in  pre ++ primFlowPrefix dir ++ show name ++ showTypeSuffix typ False
          ++ post


-- |Show the type of an expression, if it's known.
showTypeSuffix :: TypeSpec -> Bool -> String
showTypeSuffix AnyType _ = ""
showTypeSuffix typ True  = ":!" ++ show typ
showTypeSuffix typ False = ":" ++ show typ


-- |How to show a dataflow direction.
flowPrefix :: FlowDirection -> String
flowPrefix ParamIn    = ""
flowPrefix ParamOut   = "?"
flowPrefix ParamInOut = "!"
flowPrefix FlowUnknown = "???"

-- |How to show a *primitive* dataflow direction.
primFlowPrefix :: PrimFlow -> String
primFlowPrefix FlowIn    = ""
primFlowPrefix FlowOut   = "?"

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
showFork ind (PrimFork var ty last bodies) =
    startLine ind ++ "case " ++ (if last then "~" else "") ++ show var ++
                  ":" ++ show ty ++ " of" ++
    List.concatMap (\(val,body) ->
                        startLine ind ++ show val ++ ":" ++
                        showBlock (ind+4) body ++ "\n")
    (zip [0..] bodies)


-- |Show a list of placed prims.
showPlacedPrims :: Int -> [Placed Prim] -> String
showPlacedPrims ind stmts = List.concatMap (showPlacedPrim ind) stmts


-- |Show a single primitive statement with the specified indent.
showPlacedPrim :: Int -> Placed Prim -> String
showPlacedPrim ind stmt = showPlacedPrim' ind (content stmt) (place stmt)


-- |Show a single primitive statement with the specified indent and
--  optional source position.
showPlacedPrim' :: Int -> Prim -> OptPos -> String
showPlacedPrim' ind prim pos =
  startLine ind ++ showPrim ind prim ++ showMaybeSourcePos pos


-- |Show a single primitive statement.
showPrim :: Int -> Prim -> String
showPrim _ (PrimCall pspec args) =
        show pspec ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
showPrim _ (PrimForeign lang name flags args) =
        "foreign " ++ lang ++ " " ++
        name ++ (if List.null flags then "" else " " ++ unwords flags) ++
        "(" ++ intercalate ", " (List.map show args) ++ ")"
showPrim _ (PrimTest arg) =
        "test " ++ show arg


-- |Show a variable, with its suffix.
instance Show PrimVarName where
    show (PrimVarName var suffix) = var ++ "#" ++ show suffix


-- |Show a single statement.
showStmt :: Int -> Stmt -> String
showStmt _ (ProcCall maybeMod name procID detism resourceful args) =
    determinismPrefix detism
    ++ (if resourceful then "!" else "")
    ++ maybeModPrefix maybeMod
    ++ maybe "" (\n -> "<" ++ show n ++ ">") procID ++
    name ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
showStmt _ (ForeignCall lang name flags args) =
    "foreign " ++ lang ++ " " ++ name ++
    (if List.null flags then "" else " " ++ unwords flags) ++
    "(" ++ intercalate ", " (List.map show args) ++ ")"
showStmt _ (TestBool test) =
    "testbool " ++ show test
showStmt indent (And stmts) =
    intercalate (" and\n" ++ replicate indent' ' ')
    (List.map (showStmt indent' . content) stmts) ++
    ")"
    where indent' = indent + 4
showStmt indent (Or stmts) =
    "(   " ++
    intercalate (" or\n" ++ replicate indent' ' ')
        (List.map (showStmt indent' . content) stmts) ++
    ")"
    where indent' = indent + 4
showStmt indent (Not stmt) =
    "not(" ++ showStmt indent' (content stmt) ++ ")"
    where indent' = indent + 4
showStmt indent (Cond condstmt thn els) =
    let leadIn = List.replicate indent ' '
    in "if {" ++ showStmt (indent+4) (content condstmt) ++ "}::\n"
       ++ showBody (indent+4) thn ++ "\n"
       ++ leadIn ++ "else::"
       ++ showBody (indent+4) els ++ "\n"
       ++ leadIn ++ "}"
showStmt indent (Loop lstmts) =
    "do" ++  showBody (indent + 4) lstmts
    ++ List.replicate indent ' ' ++ "}"
showStmt indent (UseResources resources stmts) =
    "use " ++ intercalate ", " (List.map show resources) ++ " in"
    ++ showBody (indent + 4) stmts
    ++ List.replicate indent ' ' ++ "}"
showStmt _ (Nop) = "nop"
-- showStmt _ (For itr gen) =
--     "for " ++ show itr ++ " in " ++ show gen
showStmt _ (Break) = "break"
showStmt _ (Next) = "next"


-- |Show a proc body, with the specified indent.
showBody :: Int -> [Placed Stmt] -> String
showBody indent stmts =
  List.concatMap (\s -> "\n" ++ List.replicate indent ' '
                        ++ showStmt indent (content s)) stmts


-- |Show a primitive argument.
instance Show PrimArg where
  show (ArgVar name typ coerce dir ftype final) =
      (if final then "~" else "") ++
      primFlowPrefix dir ++
      show ftype ++
      show name ++ showTypeSuffix typ coerce
  show (ArgInt i typ)    = show i ++ showTypeSuffix typ False
  show (ArgFloat f typ)  = show f ++ showTypeSuffix typ False
  show (ArgString s typ) = show s ++ showTypeSuffix typ False
  show (ArgChar c typ)   = show c ++ showTypeSuffix typ False
  show (ArgUnneeded dir typ) =
      primFlowPrefix dir ++ "_" ++ showTypeSuffix typ False


-- |Show a single typed expression.
instance Show Exp where
  show (IntValue i) = show i
  show (FloatValue f) = show f
  show (StringValue s) = show s
  show (CharValue c) = show c
  show (Var name dir flowtype) = (show flowtype) ++ (flowPrefix dir) ++ name
  show (Where stmts exp) = show exp ++ " where" ++ showBody 8 stmts
  show (CondExp cond thn els) =
    "if\n" ++ show cond ++ " then " ++ show thn ++ " else " ++ show els
  show (Fncall maybeMod fn args) =
    maybeModPrefix maybeMod ++
    fn ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  show (ForeignFn lang fn flags args) =
    "foreign " ++ lang ++ " " ++ fn
    ++ (if List.null flags then "" else " " ++ unwords flags)
    ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  show (Typed exp typ cast) =
      show exp ++ showTypeSuffix typ cast


-- |maybeShow pre maybe post
--  if maybe has something, show pre, the maybe payload, and post
--  if the maybe is Nothing, don't show anything
maybeShow :: Show t => String -> Maybe t -> String -> String
maybeShow pre Nothing post = ""
maybeShow pre (Just something) post =
  pre ++ show something ++ post


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
trustFromJust :: String -> (Maybe t) -> t
trustFromJust msg Nothing = shouldnt $ "trustFromJust in " ++ msg
trustFromJust _ (Just val) = val


-- |Monadic version of trustFromJust.
trustFromJustM :: Monad m => String -> (m (Maybe t)) -> m t
trustFromJustM msg computation = do
    maybe <- computation
    return $ trustFromJust msg maybe


-- |Prettify and show compiler messages. Only Error messages are shown always,
-- the other message levels are shown only when the 'verbose' option is set.
showMessages :: Compiler ()
showMessages = do
    verbose <- optVerbose <$> gets options
    messages <- reverse <$> gets msgs
    let filtered =
            if verbose
            then messages
            else List.filter (\(a,_) -> a == Error) messages
    liftIO $ mapM_ showMessage filtered


-- |Prettify and show one compiler message.
showMessage :: (MessageLevel, String) -> IO ()
showMessage (lvl, msg) =
  case lvl of
      Informational ->
          putStrLn msg
      Warning -> do
          setSGR [SetColor Foreground Vivid Yellow]
          putStrLn msg
          setSGR [Reset]
      Error -> do
          setSGR [SetColor Foreground Vivid Red]
          putStrLn msg
          setSGR [Reset]


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
logAST s = logMsg AST s


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
    let prefix = (makeBold $ show selector) ++ ": "
    whenLogging selector $
      liftIO $ hPutStrLn stderr (prefix ++ List.intercalate ('\n':prefix) (lines msg))

-- | Appends a ISO/IEC 6429 code to the given string to print it bold
-- in a terminal output.
makeBold :: String -> String
makeBold s = "\x1b[1m" ++ s ++ "\x1b[0m"


------------------------------ Module Encoding Types -----------------------

data EncodedLPVM = EncodedLPVM ModuleIndex [Module]
                   deriving (Generic)


type ModuleIndex = [(ModSpec, FilePath)]

makeEncodedLPVM :: [Module] -> EncodedLPVM
makeEncodedLPVM ms =
    let makeIndex m = (modSpec m, takeDirectory $ modOrigin m)
        index = List.map makeIndex ms
    in  EncodedLPVM index ms
