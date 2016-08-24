--  File     : AST.hs
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Wybe language
--  Copyright:  2010-2015 Peter Schachte.  All rights reserved.

{-# LANGUAGE DeriveGeneric #-}

-- |The abstract syntax tree, and supporting types and functions.
--  This includes the parse tree, as well as the AST types, which
--  are normalised versions of the parse tree types.
--
--  This also includes the Compiler monad and the Module types.
module AST (
  -- *Types just for parsing
  Item(..), Visibility(..), maxVisibility, minVisibility, isPublic,
  Determinism(..), TypeProto(..), TypeSpec(..), TypeRef(..), TypeImpln(..),
  FnProto(..), ProcProto(..), Param(..), TypeFlow(..), paramTypeFlow,
  PrimProto(..), PrimParam(..), ParamInfo(..),
  Exp(..), Generator(..), Stmt(..), 
  TypeRepresentation(..), defaultTypeRepresentation, lookupTypeRepresentation,
  phantomParam, phantomArg, phantomType,
  -- *Source Position Types
  OptPos, Placed(..), place, betterPlace, content, maybePlace, rePlace,
  placedApply, makeMessage, updatePlacedM,
  -- *AST types
  Module(..), ModuleInterface(..), ModuleImplementation(..), 
  ImportSpec(..), importSpec,
  collectSubModules,
  enterModule, reenterModule, exitModule, finishModule, 
  emptyInterface, emptyImplementation, 
  getParams, getProcDef, mkTempName, updateProcDef, updateProcDefM,
  ModSpec, ProcImpln(..), ProcDef(..), procCallCount,
  ProcBody(..), PrimFork(..), Ident, VarName,
  ProcName, TypeDef(..), ResourceDef(..), ResourceIFace(..), FlowDirection(..), 
  argFlowDirection, argType, outArgVar, argDescription, flowsIn, flowsOut,
  foldBodyPrims, foldBodyDistrib, foldProcCalls,
  expToStmt, procCallToExp, expFlow,
  setExpTypeFlow, setPExpTypeFlow, isHalfUpdate,
  Prim(..), ProcSpec(..),
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
  getModule, getModuleInterface, updateModule, getSpecModule, updateSpecModule,
  updateModImplementation, updateModImplementationM, updateModLLVM,
  updateModInterface, updateAllProcs, updateModSubmods,
  getDirectory, getModuleSpec, getModuleParams, option, 
  optionallyPutStr, message, (<!>), genProcName,
  addImport, doImport, addType, lookupType, publicType,
  ResourceName(..), ResourceSpec(..), ResourceFlowSpec(..), ResourceImpln(..),
  addSimpleResource, lookupResource, publicResource, 
  addProc, lookupProc, publicProc,
  refersTo, callTargets, logDump,
  showBody, showPlacedPrims, showStmt, showBlock, showProcDef, showModSpec, 
  showModSpecs, showResources, showMaybeSourcePos, showProcDefs,
  shouldnt, nyi, checkError, checkValue, trustFromJust, trustFromJustM,
  showMessages, stopOnError, logMsg, whenLogging2, whenLogging,
  -- *Helper functions
  defaultBlock                           
  ) where

import           Config
import           Control.Monad
import           Control.Monad.Trans (lift,liftIO)
import           Control.Monad.Trans.State
import           Data.List as List
import           Data.Map as Map
import           Data.Maybe
import           Data.Set as Set
import           Options
import           System.Exit
import           System.FilePath
import           System.IO
import           Text.ParserCombinators.Parsec.Pos
import           Util
import System.Console.ANSI

import GHC.Generics (Generic)

import qualified LLVM.General.AST as LLVMAST

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

-- |An item appearing at the top level of a source file.
data Item
     -- = TypeDecl Visibility TypeProto TypeRepresentation [Item] OptPos
     = TypeDecl Visibility TypeProto TypeImpln [Item] OptPos
     | ModuleDecl Visibility Ident [Item] OptPos
     | ImportMods Visibility [ModSpec] OptPos
     | ImportItems Visibility ModSpec [Ident] OptPos
     | ResourceDecl Visibility ResourceName TypeSpec (Maybe (Placed Exp)) OptPos
       -- The Bool in the next two indicates whether inlining is forced
     | FuncDecl Visibility Determinism Bool 
       FnProto TypeSpec (Placed Exp) OptPos
     | ProcDecl Visibility Determinism Bool ProcProto [Placed Stmt] OptPos
     -- | CtorDecl Visibility FnProto OptPos
     | StmtDecl Stmt OptPos
     deriving Generic

-- |The visibility of a file item.  We only support public and private.
data Visibility = Public | Private
                  deriving (Eq, Show, Generic)

data Determinism = Det | SemiDet
                  deriving (Eq, Show, Generic)

type TypeRepresentation = String

defaultTypeRepresentation :: TypeRepresentation
defaultTypeRepresentation = "pointer"

data TypeImpln = TypeRepresentation TypeRepresentation 
               | TypeCtors Visibility [Placed FnProto]
               deriving Generic


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
                 deriving Generic

-- |A function prototype consists of a function name and zero or more formal 
--  parameters.
data FnProto = FnProto {
    fnProtoName::Ident,
    fnProtoParams::[Param],
    fnProtoResourceFlows::[ResourceFlowSpec]
    } deriving (Generic, Eq)


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


-- |Apply a function that takes a thing and an optional place to a 
--  placed thing.
placedApply :: (a -> OptPos -> b) -> (Placed a) -> b
placedApply f placed = f (content placed) (place placed)


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
                        (Compiler opts [] False Map.empty 0 [] [] Map.empty)


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
          updateCompilerM (\st -> do
                             let mods = modules st
                             let maybeMod = Map.lookup modspec mods
                             case maybeMod of
                               Nothing -> return st
                               Just mod -> do
                                 mod' <- updater mod
                                 return $ st { modules = Map.insert
                                                         modspec mod' mods})


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
updateLoadedModuleImplnM :: 
    (ModuleImplementation -> Compiler ModuleImplementation) ->
    ModSpec -> Compiler ()
updateLoadedModuleImplnM updater modspec =
    updateLoadedModuleM (\m -> do
                           let maybeImpln = modImplementation m
                           case maybeImpln of
                             Nothing -> return m
                             Just imp -> do
                               updated <- updater imp
                               return $ m { modImplementation = Just updated })
    modspec




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

-- |Return some function of the module currently being compiled.
getModule :: (Module -> t) -> Compiler t
getModule getter = gets (getter . List.head . underCompilation)


-- |Transform the module currently being compiled.
updateModule :: (Module -> Module) -> Compiler ()
updateModule updater = do
    modify (\comp -> let mods = underCompilation comp
                     in  if List.null mods
                         then shouldnt "updateModule with no current module"
                         else comp { underCompilation =
                                          updater (List.head mods):List.tail mods })

-- |Transform the module currently being compiled.
updateModuleM :: (Module -> Compiler Module) -> Compiler ()
updateModuleM updater = do
    updateCompilerM (\comp -> do
                          let mods = underCompilation comp
                          when (List.null mods) $
                            shouldnt "updateModuleM with no current module"
                          mod' <- updater $ List.head mods
                          return comp { underCompilation = mod':List.tail mods })


-- |Return some function of the specified module.  Error if it's not a module.
getSpecModule :: String -> ModSpec -> (Module -> t) -> Compiler t
getSpecModule context spec getter = do
    let msg = context ++ " looking up missing module " ++ show spec
    curr <- gets (List.filter ((==spec) . modSpec) . underCompilation)
    logAST $ "found " ++ (show $ length curr) ++
      " matching modules under compilation"
    case curr of
        []    -> gets (maybe (error msg) getter . Map.lookup spec . modules)
        [mod] -> return $ getter mod
        _     -> shouldnt "getSpecModule: multiple modules with same spec"

-- |Return some function of the specified module; returns a Maybe
findSpecModule :: ModSpec -> (Module -> t) -> Compiler (Maybe t)
findSpecModule spec getter = 
    gets (fmap getter . Map.lookup spec . modules)

-- |Transform the specified module.  Does nothing if it does not exist.
updateSpecModule :: ModSpec -> (Module -> Module) -> Compiler ()
updateSpecModule spec updater = do
    modify 
      (\comp -> comp { modules = Map.adjust updater spec (modules comp) })

-- |Transform the specified module.  An error if it does not exist.
updateSpecModuleM :: (Module -> Compiler Module) -> ModSpec -> Compiler ()
updateSpecModuleM updater spec = do
    updateCompilerM
      (\comp -> do
            let mods = modules comp
            let mod = Map.lookup spec mods
            case mod of
                Nothing -> shouldnt $ "nonexistent module " ++ show spec
                Just m -> do
                    m' <- updater m
                    return $ comp {modules = Map.insert spec m' mods})

-- |Prepare to compile a module by setting up a new Module on the 
--  front of the list of modules underCompilation. 
enterModule :: FilePath -> ModSpec -> Maybe [Ident] -> Compiler ()
enterModule dir modspec params = do
    count <- gets ((1+) . loadCount)
    modify (\comp -> comp { loadCount = count })
    logAST $ "Entering module " ++ showModSpec modspec
    modify (\comp -> let mods = Module dir modspec params 0 0
                                       emptyInterface (Just emptyImplementation)
                                       count count 0 [] Nothing
                                       : underCompilation comp
                     in  comp { underCompilation = mods })

-- |Go back to compiling a module we have previously finished with.
-- Trusts that the modspec really does specify a module.
reenterModule :: ModSpec -> Compiler ()
reenterModule modspec = do
    logAST $ "finding module " ++ showModSpec modspec
    mod <- getSpecModule "reenterModule" modspec id
    logAST $ "found it"
    modify (\comp -> comp { underCompilation = mod : underCompilation comp })


exitModule :: Compiler [ModSpec]
exitModule = do
    mod <- finishModule
    let num = thisLoadNum mod
    logAST $ "Finishing module " ++ showModSpec (modSpec mod)
    logAST $ "    loadNum = " ++ show num ++
           ", minDependencyNum = " ++ show (minDependencyNum mod)
    if (minDependencyNum mod < num) 
      then do
        modify (\comp -> comp { deferred = mod:deferred comp })
        return []
      else do
        deferred <- gets deferred
        let (bonus,rest) = span ((==num) . minDependencyNum) deferred
        modify (\comp -> comp { deferred = rest })
        return $ List.map modSpec $ mod:bonus

finishModule :: Compiler Module
finishModule = do
    mod <- getModule id
    modify 
      (\comp -> comp { underCompilation = List.tail (underCompilation comp) })
    updateModules $ Map.insert (modSpec mod) mod
    return mod


-- |Return the directory of the current module.
getDirectory :: Compiler FilePath
getDirectory = getModule modDirectory

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
addType :: Ident -> TypeDef -> Visibility -> Compiler (TypeSpec)
addType name def@(TypeDef arity rep _) vis = do
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
lookupType (TypeSpec _ "phantom" []) _ =
    return $ Just $ TypeSpec ["wybe"] "phantom" []
lookupType ty@(TypeSpec ["wybe"] "int" []) _ = return $ Just ty
lookupType ty@(TypeSpec mod name args) pos = do
    logAST $ "Looking up type " ++ show ty
    tspecs <- refersTo mod name modKnownTypes typeMod
    logAST $ "Candidates: " ++ show tspecs
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
            if typeDefArity def == length args
              then do
                args' <- fmap catMaybes $ mapM (flip lookupType pos) args
                let matchingMod = maybe (shouldnt "lookupType") modSpec maybeMod
                let matchingType = TypeSpec matchingMod name args'
                logAST $ "Matching type = " ++ show matchingType
                return $ Just $ matchingType
              else do
                message Error
                  ("Type '" ++ name ++ "' expects " ++ (show $ typeDefArity def) ++
                   " arguments, but " ++ (show $ length args) ++ " were given")
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
lookupResource :: ResourceSpec -> OptPos -> Compiler (Maybe ResourceIFace)
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
            return $ Just iface
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
    updateImplementation
      (updateModImports
       (\moddeps -> 
         let imports' =
                 case Map.lookup modspec moddeps of
                     Nothing -> imports
                     Just imports'' -> combineImportSpecs imports'' imports
         in Map.insert modspec imports' moddeps))
    when (isNothing $ importPublic imports) $
      updateInterface Public (updateDependencies (Set.insert modspec))
    maybeMod <- gets (List.find ((==modspec) . modSpec) . underCompilation)
    logAST $ "Noting import of " ++ showModSpec modspec ++
           ", which is " ++ (if isNothing maybeMod then "NOT " else "") ++
           "currently being loaded"
    case maybeMod of
        Nothing -> return ()  -- not currently loading dependency
        Just mod -> do
            logAST $ "Limiting minDependencyNum to " ++
                    show (thisLoadNum mod)
            updateModule (\m -> m { minDependencyNum =
                                        min (thisLoadNum mod)
                                            (minDependencyNum m) })



-- |Add the specified proc definition to the current module.
addProc :: Int -> Item -> Compiler ()
addProc tmpCtr (ProcDecl vis detism inline proto stmts pos) = do
    let ProcProto name params resources = proto
    let procDef = ProcDef name proto (ProcDefSrc stmts) pos tmpCtr 
                  Map.empty vis detism inline $ initSuperprocSpec vis
    currMod <- getModuleSpec
    procs <- getModuleImplementationField (findWithDefault [] name . modProcs)
    let procs' = procs ++ [procDef]
    let spec = ProcSpec currMod name (length procs)
    updateImplementation
      (\imp ->
        let known = findWithDefault Set.empty name $ modKnownProcs imp
            known' = Set.insert spec known
        in imp { modProcs = Map.insert name procs' $ modProcs imp,
                 modKnownProcs = Map.insert name known' $ modKnownProcs imp })
    updateInterface vis (updatePubProcs (mapSetInsert name spec))
    logAST $ "Adding defnintion for " ++ show spec ++ ":" ++
      showProcDef 4 procDef
    return ()
addProc _ item =
    shouldnt $ "addProc given non-Proc item " ++ show item


getParams :: ProcSpec -> Compiler [Param]
getParams pspec = do
    -- XXX shouldn't have to grovel in implementation to find prototype
    fmap (procProtoParams . procProto) $ getProcDef pspec


getProcDef :: ProcSpec -> Compiler ProcDef
getProcDef (ProcSpec modSpec procName procID) = do
    mod <- trustFromJustM ("no such module " ++ showModSpec modSpec) $ 
           getLoadingModule modSpec
    let impl = trustFromJust ("unimplemented module " ++ showModSpec modSpec) $ 
               modImplementation mod
    return $ (modProcs impl ! procName) !! procID


updateProcDef :: (ProcDef -> ProcDef) -> ProcSpec -> Compiler ()
updateProcDef updater pspec@(ProcSpec modspec procName procID) =
    updateLoadedModuleImpln
    (\imp -> imp { modProcs =
                       Map.adjust
                       (\l -> let (front,back) = List.splitAt procID l
                                  updated = 
                                      if List.null back
                                      then shouldnt $ "invalid proc spec " ++
                                           show pspec
                                      else updater $ List.head back
                              in  front ++ updated:List.tail back)
                       procName (modProcs imp) })
    modspec
    

updateProcDefM :: (ProcDef -> Compiler ProcDef) -> ProcSpec -> Compiler ()
updateProcDefM updater pspec@(ProcSpec modspec procName procID) =
    updateLoadedModuleImplnM
    (\imp -> do
       let procs = modProcs imp
       case Map.lookup procName procs of
         Nothing -> return imp
         Just defs -> do
           let (front,back) = List.splitAt procID defs
           updated <- 
               if List.null back
               then shouldnt $ "invalid proc spec " ++
                    show pspec
               else updater $ List.head back
           let defs' = front ++ updated:List.tail back
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
  modDirectory :: FilePath,      -- ^The directory the module is in
  modSpec :: ModSpec,            -- ^The module path name 
  modParams :: Maybe [Ident],    -- ^The type parameters, if a type
  modConstants :: Int,           -- ^Num constant constructors, if a type
  modNonConstants :: Int,        -- ^Num non-constant constructors, if a type
  modInterface :: ModuleInterface, -- ^The public face of this module
  modImplementation :: Maybe ModuleImplementation, 
                                 -- ^the module's implementation
  thisLoadNum :: Int,            -- ^the loadCount when loading this module
  minDependencyNum :: Int,       -- ^the smallest loadNum of all dependencies
  procCount :: Int,              -- ^a counter for gensym-ed proc names
  stmtDecls :: [Placed Stmt],     -- ^top-level statements in this module
  itemsHash :: Maybe String -- ^map of proc name to it's hash 
  } deriving (Generic)


descendantModuleOf :: ModSpec -> ModSpec -> Bool
descendantModuleOf sub [] = True
descendantModuleOf (a:as) (b:bs)
  | a == b = descendantModuleOf as bs
descendantModuleOf _ _ = False

getDescendant :: ModSpec -> Maybe ModSpec
getDescendant [] = Nothing
getDescendant (m:[]) = Nothing
getDescendant modspec = Just $ init modspec

-- | Collect all the subModules of the given modspec.
collectSubModules :: ModSpec -> Compiler [ModSpec]
collectSubModules mspec = do
    subMods <- fmap (Map.elems . modSubmods) $ getLoadedModuleImpln mspec
    desc <- fmap concat $ mapM collectSubModules subMods
    return $ subMods ++ desc



-- |The list of defining modules that the given (possibly
--  module-qualified) name could possibly refer to from the current
--  module.  This may include the current module, or any module it may
--  be imported from.  The implMapFn is a Module selector function that
--  produces a map that tells whether that module exports that name,
--  and implMapFn tells whether a module implementation defines that
--  name.  The reference to this name occurs in the current module.
refersTo :: ModSpec -> Ident -> (ModuleImplementation -> Map Ident (Set b)) ->
            (b -> ModSpec) -> Compiler (Set b)
refersTo modspec name implMapFn specModFn = do
    currMod <- getModuleSpec
    logAST $ "Finding visible symbol " ++ maybeModPrefix modspec ++
      name ++ " from module " ++ showModSpec currMod
    visible <- getModule (Map.findWithDefault Set.empty name . implMapFn . 
                          fromJust . modImplementation)
    logAST $ "*** ALL visible from: " ++ showModSpec modspec ++ ": "
        ++ showModSpecs (Set.toList (Set.map specModFn visible)) 
    let matched = Set.filter ((modspec `isSuffixOf`) . specModFn) visible
    case Set.null matched of
        False -> return matched
        -- Try and look into the super mod.
        True -> case getDescendant currMod of
            Just des -> do
                reenterModule des
                desMatched <- refersTo modspec name implMapFn specModFn
                finishModule
                return desMatched
            Nothing -> return matched
    


-- |Returns a list of the potential targets of a proc call.
callTargets :: ModSpec -> ProcName -> Compiler [ProcSpec]
callTargets modspec name = do
    pspecs <- fmap Set.toList $ refersTo modspec name modKnownProcs procSpecMod
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
    pubTypes :: Map Ident (TypeSpec,TypeRepresentation),   
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
updatePubTypes :: (Map Ident (TypeSpec,TypeRepresentation) 
                   -> Map Ident (TypeSpec,TypeRepresentation)) -> 
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
    modImports   :: Map ModSpec ImportSpec,   -- ^This module's imports
    modSubmods   :: Map Ident ModSpec,        -- ^This module's submodules
    modTypes     :: Map Ident TypeDef,        -- ^Types defined by this module
    modResources :: Map Ident ResourceDef,    -- ^Resources defined by this mod
    modProcs     :: Map Ident [ProcDef],      -- ^Procs defined by this module
    modKnownTypes:: Map Ident (Set TypeSpec), -- ^Type visible to this module
    modConstCtorCount :: Int,                 -- ^Number of consts constructors
    modNonConstCtorCount :: Int,              -- ^Num of arity >=1 constructors
    modKnownResources :: Map Ident (Set ResourceSpec),
                                              -- ^Resources visible to this mod
    modKnownProcs:: Map Ident (Set ProcSpec),  -- ^Procs visible to this module
    modLLVM :: Maybe LLVMAST.Module  -- ^ Module's LLVM.General.AST.Module representation
    } deriving (Generic)

emptyImplementation :: ModuleImplementation
emptyImplementation =
    ModuleImplementation Map.empty Map.empty Map.empty Map.empty Map.empty
                         Map.empty 0 0 Map.empty Map.empty Nothing


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
lookupTypeRepresentation AnyType = return $ Just "pointer"
lookupTypeRepresentation InvalidType = return Nothing
lookupTypeRepresentation (TypeSpec ["wybe"] "bool" _) = return $ Just "bool"
lookupTypeRepresentation (TypeSpec ["wybe"] "int" _) = return $ Just "int"
lookupTypeRepresentation (TypeSpec ["wybe"] "float" _) = return $ Just "float"
lookupTypeRepresentation (TypeSpec ["wybe"] "double" _) = return $ Just "double"
lookupTypeRepresentation (TypeSpec _ "phantom" _) = return $ Just "phantom"
lookupTypeRepresentation (TypeSpec modSpecs name _) = do
    -- logMsg Blocks $ "Looking for " ++ name ++ " in mod: " ++
    --      showModSpec modSpecs
    reenterModule modSpecs
    maybeImpln <- getModuleImplementation
    modInt <- getModuleInterface
    _ <- finishModule
    -- Try find the TypeRepresentation in the interface
    let maybeIntMatch = fmap snd $ Map.lookup name $ pubTypes modInt
    -- Try find the TypeRepresentation in the implementation if not found
    -- in the interface
    let maybeMatch = case maybeIntMatch of
            Nothing ->
                maybeImpln >>=
                (fmap typeDefRepresentation . Map.lookup name . modTypes)
            _ -> maybeIntMatch
    -- If still not found, search the direct descendant interface and
    -- implementation
    -- case maybeMatch of
    --     Nothing -> case getDescendant modSpecs of
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
    fromIFace <- fmap (modInterface . trustFromJust "doImport") $ 
                 getLoadingModule mod
    let pubImports = importPublic imports
    let allImports = combineImportPart pubImports $ importPrivate imports
    let importedTypes = importsSelected allImports $ pubTypes fromIFace
    let importedResources = importsSelected allImports $ pubResources fromIFace
    let importedProcs = importsSelected allImports $ pubProcs fromIFace
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


importsSelected :: Maybe (Set Ident) -> Map Ident a -> Map Ident a
importsSelected Nothing items = items
importsSelected (Just these) items =
    Map.filterWithKey (\k _ -> Set.member k these) items


-- |A type definition, including the number of type parameters and an 
--  optional source position.
data TypeDef = TypeDef {
    typeDefArity :: Int,
    typeDefRepresentation :: TypeRepresentation,
    typeDefOptPos :: OptPos
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
        resourceInit::(Maybe (Placed Exp)), 
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
    = ProcDefSrc [Placed Stmt]           -- defn in source-like form
    | ProcDefPrim PrimProto ProcBody     -- defn in LPVM (clausal) form
      -- defn in SSA (LLVM) form along with any needed extern definitions 
    deriving (Eq,Generic)


isCompiled :: ProcImpln -> Bool
isCompiled (ProcDefPrim _ _) = True
isCompiled (ProcDefSrc _) = False

instance Show ProcImpln where
    show (ProcDefSrc stmts) = showBody 4 stmts
    show (ProcDefPrim proto body) = show proto ++ ":" ++ showBlock 4 body

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

-- | A primitive switch.  This only appears at tne end of a ProcBody.
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
-- applying comb, which must be associative, to combine results.
foldProcCalls :: (ModSpec -> Ident -> (Maybe Int) -> [Placed Exp] -> a) ->
                 (a -> a -> a) -> a -> [Placed Stmt] -> a
foldProcCalls fn comb val [] = val
foldProcCalls fn comb val (s:ss) = foldProcCalls' fn comb val (content s) ss

foldProcCalls' :: (ModSpec -> Ident -> (Maybe Int) -> [Placed Exp] -> a) ->
                 (a -> a -> a) -> a -> Stmt -> [Placed Stmt] -> a
foldProcCalls' fn comb val (ProcCall m name procID args) ss =
    foldProcCalls fn comb (comb val $ fn m name procID args) ss
foldProcCalls' fn comb val (Cond tst _ thn els) ss =
    foldProcCalls fn comb
    (foldProcCalls fn comb
     (foldProcCalls fn comb
      (foldProcCalls fn comb val els)
      thn)
     tst)
    ss
foldProcCalls' fn comb val (Loop body) ss =
    foldProcCalls fn comb (foldProcCalls fn comb val body) ss
foldProcCalls' fn comb val (_) ss =
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
      procSpecMod::ModSpec,
      procSpecName::ProcName,
      procSpecID::ProcID}
                deriving (Eq,Ord,Generic)

instance Show ProcSpec where
    show (ProcSpec mod name pid) =
        showModSpec mod ++ "." ++ name ++ "<" ++ show pid ++ ">"

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

-- |A proc prototype, including name and formal parameters.
data ProcProto = ProcProto {
    procProtoName::ProcName,
    procProtoParams::[Param],
    procProtoResources::[ResourceFlowSpec]
    } deriving (Eq, Generic)


-- |A proc prototype, including name and formal parameters.
data PrimProto = PrimProto {
    primProtoName::ProcName,
    primProtoParams::[PrimParam]
    } deriving (Eq, Generic)


instance Show PrimProto where
  show (PrimProto name params) = 
    name ++ "(" ++ (intercalate ", " $ List.map show params) ++ ")"


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
    primParamInfo::ParamInfo  -- ^What we've inferred about this param
    } deriving (Eq, Generic)


-- |Info inferred about a single proc parameter
data ParamInfo = ParamInfo {
        paramInfoUnneeded::Bool       -- ^Can this parameter be eliminated?
    } deriving (Eq,Generic)

-- |A dataflow direction:  in, out, both, or neither.
data FlowDirection = ParamIn | ParamOut | ParamInOut | NoFlow | FlowUnknown
                   deriving (Show,Eq,Ord,Generic)

-- |A primitive dataflow direction:  in or out
data PrimFlow = FlowIn | FlowOut
                   deriving (Show,Eq,Ord,Generic)


-- |Does the specified flow direction flow in?
flowsIn :: FlowDirection -> Bool
flowsIn NoFlow     = False
flowsIn ParamIn    = True
flowsIn ParamOut   = False
flowsIn ParamInOut = True
flowsIn FlowUnknown = shouldnt "checking if unknown flow direction flows in"

-- |Does the specified flow direction flow out?
flowsOut :: FlowDirection -> Bool
flowsOut NoFlow     = False
flowsOut ParamIn = False
flowsOut ParamOut = True
flowsOut ParamInOut = True
flowsOut FlowUnknown = shouldnt "checking if unknown flow direction flows out"


-- |Source program statements.  These will be normalised into Prims.
data Stmt
     = ProcCall ModSpec Ident (Maybe Int) [Placed Exp]
     | ForeignCall Ident Ident [Ident] [Placed Exp]
     | Test [Placed Stmt] (Placed Exp)
     | Nop
     -- All the following are eliminated during unbranching.
     -- The first stmt list is empty and the Exp is anything until
     -- flattening.  After that, the stmt list contains the body of
     -- the test, and the Exp is primitive.
     | Cond [Placed Stmt] (Placed Exp) [Placed Stmt] [Placed Stmt]
     | Loop [Placed Stmt]
     -- These are only valid in a loop
     | For (Placed Exp) (Placed Exp)
     | Break  -- holds the variable versions before the break
     | Next  -- holds the variable versions before the next
     deriving (Eq,Ord,Generic)

instance Show Stmt where
  show s = "{" ++ showStmt 4 s ++ "}"

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
      | CondExp (Placed Exp) (Placed Exp) (Placed Exp)
      | Fncall ModSpec Ident [Placed Exp]
      | ForeignFn Ident Ident [Ident] [Placed Exp]
     deriving (Eq,Ord,Generic)


-- |Is the supplied parameter a phantom?
phantomParam :: PrimParam -> Bool
phantomParam = phantomType . primParamType

-- |Is the supplied argument a phantom?
phantomArg :: PrimArg -> Bool
phantomArg (ArgVar _ ty _ _ _) = phantomType ty
phantomArg _ = False -- Nothing but a var can be a phantom

-- |Does the supplied type indicate a phantom?
phantomType :: TypeSpec -> Bool
phantomType TypeSpec{typeName="phantom"} = True
phantomType _ = False


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
     | PrimNop
     deriving (Eq,Ord,Generic)

instance Show Prim where
    show prim = showPrim 0 prim

-- |The allowed arguments in primitive proc or foreign proc calls, 
--  just variables and constants.
data PrimArg 
     = ArgVar PrimVarName TypeSpec PrimFlow ArgFlowType Bool 
       -- ^Bool indicates definite last use (one use in the last 
       --  statement to use the variable) 
     | ArgInt Integer TypeSpec
     | ArgFloat Double TypeSpec
     | ArgString String TypeSpec
     | ArgChar Char TypeSpec
     deriving (Eq,Ord,Generic)


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
    show (Resource res) = "#"


-- |The dataflow direction of an actual argument.
argFlowDirection :: PrimArg -> PrimFlow
argFlowDirection (ArgVar _ _ flow _ _) = flow
argFlowDirection (ArgInt _ _) = FlowIn
argFlowDirection (ArgFloat _ _) = FlowIn
argFlowDirection (ArgString _ _) = FlowIn
argFlowDirection (ArgChar _ _) = FlowIn


argType :: PrimArg -> TypeSpec
argType (ArgVar _ typ _ _ _) = typ
argType (ArgInt _ typ) = typ
argType (ArgFloat _ typ) = typ
argType (ArgString _ typ) = typ
argType (ArgChar _ typ) = typ


outArgVar:: PrimArg -> PrimVarName
outArgVar (ArgVar var _ flow _ _) | flow == FlowOut = var
outArgVar _ = shouldnt "outArgVar of input argument"


argDescription :: PrimArg -> String
argDescription (ArgVar var _ flow ftype _) =
    (case flow of
          FlowIn -> "input "
          FlowOut -> "output ") ++
    (case ftype of
        Ordinary -> "variable " ++ primVarName var
        HalfUpdate -> "update of variable " ++ primVarName var
        Implicit pos -> "expression" ++ showMaybeSourcePos pos
        Resource rspec -> "resource " ++ show rspec)
argDescription (ArgInt val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgFloat val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgString val _) = "constant argument '" ++ show val ++ "'"
argDescription (ArgChar val _) = "constant argument '" ++ show val ++ "'"



-- |Convert a statement read as an expression to a Stmt.
expToStmt :: Exp -> Stmt
expToStmt (Fncall maybeMod name args) = ProcCall maybeMod name Nothing args
expToStmt (ForeignFn lang name flags args) = 
  ForeignCall lang name flags args
expToStmt (Var name ParamIn _) = ProcCall [] name Nothing []
expToStmt exp = shouldnt $ "non-Fncall expr " ++ show exp


procCallToExp :: Stmt -> Exp
procCallToExp (ProcCall maybeMod name Nothing args) =
    Fncall maybeMod name args
procCallToExp stmt =
    shouldnt $ "converting non-proccall to expr " ++ showStmt 4 stmt


expFlow :: Exp -> FlowDirection
expFlow (Typed expr _ _) = expFlow expr
expFlow (Var _ flow _) = flow
expFlow _ = ParamIn


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

varsInPrims :: PrimFlow -> [Prim] -> Set PrimVarName
varsInPrims dir prims =
    List.foldr Set.union Set.empty $ List.map (varsInPrim dir) prims

varsInPrim :: PrimFlow -> Prim     -> Set PrimVarName
varsInPrim dir (PrimCall _ args)      = varsInPrimArgs dir args
varsInPrim dir (PrimForeign _ _ _ args) = varsInPrimArgs dir args
varsInPrim dir (PrimNop)                = Set.empty

varsInPrimArgs :: PrimFlow -> [PrimArg] -> Set PrimVarName
varsInPrimArgs dir args = 
    List.foldr Set.union Set.empty $ List.map (varsInPrimArg dir) args

varsInPrimArg :: PrimFlow -> PrimArg -> Set PrimVarName
varsInPrimArg dir (ArgVar var _ dir' _ _) = 
  if dir == dir' then Set.singleton var else Set.empty
varsInPrimArg _ (ArgInt _ _)            = Set.empty
varsInPrimArg _ (ArgFloat _ _)          = Set.empty
varsInPrimArg _ (ArgString _ _)         = Set.empty
varsInPrimArg _ (ArgChar _ _)           = Set.empty


----------------------------------------------------------------
--                      Showing Compiler State
--
-- Each module is shown listing submodules, types, resources and procs
-- it exports, then listing the module imports, and the types,
-- resources and procs it defines, including definitions.  Functions
-- are converted to procs.
--
-- Each proc is show including whether it is public, how many calls to
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

logDump :: LogSelection -> LogSelection -> String -> Compiler ()
logDump selector1 selector2 pass = do
    whenLogging2 selector1 selector2 $ do
      modList <- gets (Map.elems . modules)
      liftIO $ putStrLn $ replicate 70 '=' ++ "\nAFTER " ++ pass ++ ":\n" ++
        intercalate ("\n" ++ replicate 50 '-' ++ "\n") 
        (List.map show $ List.filter ((/="wybe"). List.head . modSpec) modList)


-- |How to show an Item.
instance Show Item where
  show (TypeDecl vis name (TypeRepresentation repn) items pos) =
    visibilityPrefix vis ++ "type " ++ show name 
    ++ " is" ++ repn
    ++ showMaybeSourcePos pos ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\nend\n"
  show (TypeDecl vis name (TypeCtors ctorvis ctors) items pos) =
    visibilityPrefix vis ++ "type " ++ show name 
    ++ " " ++ visibilityPrefix ctorvis
    ++ showMaybeSourcePos pos ++ "\n    "
    ++ intercalate "\n  | " (List.map show ctors) ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\nend\n"
  show (ImportMods vis mods pos) =
      visibilityPrefix vis ++ "use " ++ 
      showModSpecs mods ++ showMaybeSourcePos pos ++ "\n  "
  show (ImportItems vis mod specs pos) =
      visibilityPrefix vis ++ "from " ++ showModSpec mod ++
      " use " ++ intercalate ", " specs
      ++ showMaybeSourcePos pos ++ "\n  "
  show (ModuleDecl vis name items pos) =
    visibilityPrefix vis ++ "module " ++ show name ++ " is" 
    ++ showMaybeSourcePos pos ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\nend\n"
  show (ResourceDecl vis name typ init pos) =
    visibilityPrefix vis ++ "resource " ++ show name ++ ":" ++ show typ
    ++ maybeShow " = " init " "
    ++ showMaybeSourcePos pos
  show (FuncDecl vis detism inline proto typ exp pos) =
    visibilityPrefix vis
    ++ determinismPrefix detism
    ++ if inline then "inline " else ""
    ++ "func " ++ show proto ++ ":" ++ show typ
    ++ showMaybeSourcePos pos
    ++ " = " ++ show exp
  show (ProcDecl vis detism inline proto stmts pos) =
    visibilityPrefix vis
    ++ determinismPrefix detism
    ++ if inline then "inline " else ""
    ++ "proc " ++ show proto
    ++ showMaybeSourcePos pos
    ++ showBody 4 stmts
  -- show (CtorDecl vis proto pos) =
  --   visibilityPrefix vis ++ "ctor " ++ show proto
  --   ++ showMaybeSourcePos pos
  show (StmtDecl stmt pos) =
    showStmt 4 stmt ++ showMaybeSourcePos pos

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

-- |How to show a function prototype.
instance Show FnProto where
  show (FnProto name [] resources) = name ++ showResources resources
  show (FnProto name params resources) = 
    name ++ "(" ++ intercalate "," (List.map show params) ++ ")" ++
    showResources resources

-- |How to show something that may have a source position
instance Show t => Show (Placed t) where
    show (Placed t pos) = show t ++ showMaybeSourcePos (Just pos)
    show (Unplaced t) =   show t

    
-- |How to show an optional source position
showMaybeSourcePos :: OptPos -> String
-- turn off annoying source positions
-- showMaybeSourcePos _ = ""
showMaybeSourcePos (Just pos) = 
  " @" ++ takeBaseName (sourceName pos) ++ ":" 
  ++ show (sourceLine pos) ++ ":" ++ show (sourceColumn pos)
showMaybeSourcePos Nothing = ""

-- |How to show a module.
instance Show Module where
    show mod =
        let int  = modInterface mod
            maybeimpl = modImplementation mod
        in " Module " ++ showModSpec (modSpec mod) ++ 
           maybeShow "(" (modParams mod) ")" ++
           "\n  public submods  : " ++ showMapPoses (pubDependencies int) ++
           "\n  public types    : " ++ showMapLines (pubTypes int) ++
           "\n  public resources: " ++ showMapLines (pubResources int) ++
           "\n  public procs    : " ++ 
           intercalate "\n                    " 
           (List.map show $ Set.toList $ Set.unions $ 
            Map.elems $ pubProcs int) ++
           if isNothing maybeimpl then "\n  implementation not available"
           else let impl = fromJust maybeimpl
                    indent = replicate 20 ' '
                in
                 "\n  imports         : " ++
                 intercalate "\n                    " 
                 [showUse 20 mod dep | 
                  (mod,dep) <- Map.assocs $ modImports impl] ++
                 -- "\n  vis types       : " ++ 
                 -- (fillLines indent 20 80 $ 
                 --  showSetMapItems $ modKnownTypes impl) ++
                 -- "\n  vis resources   : " ++
                 -- (fillLines indent 20 80 $ 
                 --  showSetMapItems $ modKnownResources impl) ++
                 -- "\n  vis procs       : " ++
                 -- (fillLines indent 20 80 $ 
                 --  showSetMapItems $ modKnownProcs impl) ++
                 "\n  types           : " ++ showMapTypes (modTypes impl) ++
                 "\n  resources       : " ++ showMapLines (modResources impl) ++
                 "\n  procs           : " ++ "\n" ++
                 (showMap "\n\n" (const "") (showProcDefs 0)
                  (modProcs impl)) ++
                 (if Map.null (modSubmods impl)
                  then ""
                  else "\n  submodules      : " ++ 
                       showMap ", " (const "") showModSpec (modSubmods impl))

--showTypeMap :: Map Ident TypeDef -> String

-- |How to show a set of identifiers as a comma-separated list
showIdSet :: Set Ident -> String
showIdSet set = intercalate ", " $ Set.elems set

-- |How to show a map, one line per item.
showMapLines :: Show v => Map Ident v -> String
showMapLines = showMap "\n                    " (++": ") show

showSetMapItems :: (Show b, Ord b) => (Map a (Set b)) -> String
showSetMapItems setMap =
    intercalate ", " $
    List.map show $ Set.toList $ 
    List.foldr Set.union Set.empty $ Map.elems setMap


-- |How to show a map, items separated by commas.
showMapTypes :: Map Ident TypeDef -> String
showMapTypes = showMap ", " (++ "/") show

-- |How to show a map to source positions, one line per item.
showMapPoses :: Map Ident OptPos -> String
showMapPoses = showMap ", " id showMaybeSourcePos

-- |How to show a map from identifiers to values, given a separator 
--  for items, and a separator for keys from values, and a function 
--  to show the values.
showMap :: String -> (k -> String) -> (v -> String) -> Map k v -> String
showMap outersep keyFn valFn m =
    intercalate outersep $ List.map (\(k,v) -> keyFn k ++ valFn v) $
    Map.assocs m


-- |How to show a type definition.
instance Show TypeDef where
  show (TypeDef arity rep pos) = 
    show arity ++ " (" ++ rep ++ ") " ++ showMaybeSourcePos pos


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

showResources :: [ResourceFlowSpec] -> String
showResources [] = ""
showResources resources = 
    " use " ++ intercalate ", " (List.map show resources)


-- |How to show a proc prototype.
instance Show ProcProto where
  show (ProcProto name params resources) = 
    name ++ "(" ++ (intercalate ", " $ List.map show params) ++ ")" ++
    showResources resources

-- |How to show a formal parameter.
instance Show Param where
  show (Param name typ dir flowType) =
    (show flowType) ++ flowPrefix dir ++ name ++ showTypeSuffix typ

-- |How to show a formal parameter.
instance Show PrimParam where
  show (PrimParam name typ dir _ (ParamInfo unneeded)) =
      let (pre,post) = if unneeded then ("[","]") else ("","")
      in  pre ++ primFlowPrefix dir ++ show name ++ showTypeSuffix typ ++ post

showTypeSuffix :: TypeSpec -> String
showTypeSuffix AnyType = ""
showTypeSuffix typ = ":" ++ show typ


-- |How to show a dataflow direction.
flowPrefix :: FlowDirection -> String
flowPrefix NoFlow     = ""
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

showFork :: Int -> PrimFork -> String
showFork ind NoFork = ""
showFork ind (PrimFork var ty last bodies) =
    startLine ind ++ "case " ++ (if last then "~" else "") ++ show var ++
                  ":" ++ show ty ++ " of" ++
    List.concatMap (\(val,body) ->
                        startLine ind ++ show val ++ ":" ++
                        showBlock (ind+4) body ++ "\n")
    (zip [0..] bodies)


-- |Show a list of placed prims
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

showPrim :: Int -> Prim -> String
showPrim _ (PrimCall pspec args) =
        show pspec ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
showPrim _ (PrimForeign lang name flags args) =
        "foreign " ++ lang ++ " " ++ 
        name ++ (if List.null flags then "" else " " ++ unwords flags) ++
        "(" ++ intercalate ", " (List.map show args) ++ ")"
showPrim _ (PrimNop) =
        "NOP"

-- |Show a variable, with its suffix
instance Show PrimVarName where
    show (PrimVarName var suffix) = var ++ "#" ++ show suffix


showStmt :: Int -> Stmt -> String
showStmt _ (ProcCall maybeMod name procID args) =
    maybeModPrefix maybeMod ++ maybe "" (\n -> "<" ++ show n ++ ">") procID ++
    name ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
showStmt _ (ForeignCall lang name flags args) =
    "foreign " ++ lang ++ " " ++ name ++ 
    (if List.null flags then "" else " " ++ unwords flags) ++
    "(" ++ intercalate ", " (List.map show args) ++ ")"
showStmt indent (Test stmts exp) =
    "test {" ++ showBody (indent+6) stmts ++ "}\n"
    ++ List.replicate (indent+5) ' '
    ++ "} " ++ show exp
showStmt indent (Cond condstmts cond thn els) =
    let leadIn = List.replicate indent ' '
    in "if {" ++ showBody (indent+4) condstmts ++ "}\n"
       ++ leadIn ++ show cond ++ "::\n"
       ++ showBody (indent+4) thn ++ "\n"
       ++ leadIn ++ "else::"
       ++ showBody (indent+4) els ++ "\n"
       ++ leadIn ++ "end"
showStmt indent (Loop lstmts) =
    "do" ++  showBody (indent + 4) lstmts
    ++ List.replicate indent ' ' ++ " end"
showStmt _ (Nop) = "nop"
showStmt _ (For itr gen) =
    "for " ++ show itr ++ " in " ++ show gen
showStmt _ (Break) = "break"
showStmt _ (Next) = "next"


showBody :: Int -> [Placed Stmt] -> String
showBody indent stmts =
  List.concatMap (\s -> "\n" ++ List.replicate indent ' ' 
                        ++ showStmt indent (content s)) stmts


-- |Show a primitive argument.
instance Show PrimArg where
  show (ArgVar name typ dir ftype final) = 
      (if final then "~" else "") ++
      primFlowPrefix dir ++ 
      show ftype ++
      show name ++ showTypeSuffix typ
  show (ArgInt i typ)    = show i ++ showTypeSuffix typ
  show (ArgFloat f typ)  = show f ++ showTypeSuffix typ
  show (ArgString s typ) = show s ++ showTypeSuffix typ
  show (ArgChar c typ)   = show c ++ showTypeSuffix typ


-- |Show a single typed expression.
-- |Show a single expression.
instance Show Exp where
  show (IntValue i) = show i
  show (FloatValue f) = show f
  show (StringValue s) = show s
  show (CharValue c) = show c
  show (Var name dir flowtype) = (show flowtype) ++ (flowPrefix dir) ++ name
  show (Where stmts exp) = show exp ++ " where" ++ showBody 8 stmts
  show (CondExp cond thn els) = 
    "if\n" ++ show cond ++ "then " ++ show thn ++ " else " ++ show els
  show (Fncall maybeMod fn args) = 
    maybeModPrefix maybeMod ++
    fn ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  show (ForeignFn lang fn flags args) = 
    "foreign " ++ lang ++ " " ++ fn 
    ++ (if List.null flags then "" else " " ++ unwords flags)
    ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  show (Typed exp typ cast) =
      show exp ++ (if cast then "!" else "") ++ showTypeSuffix typ

-- |maybeShow pre maybe pos
--  if maybe has something, show pre, the maybe payload, and post
--  if the maybe is Nothing, don't show anything
maybeShow :: Show t => String -> Maybe t -> String -> String
maybeShow pre Nothing post = ""
maybeShow pre (Just something) post =
  pre ++ show something ++ post


-- |Report an internal error and abort
shouldnt :: String -> a
shouldnt what = error $ "Internal error: " ++ what


nyi :: String -> a
nyi what = error $ "Not yet implemented: " ++ what

-- |Check that all is well, else abort
checkError :: Monad m => String -> Bool -> m ()
checkError msg bad = when bad $ shouldnt msg


-- |Check that a value is OK; if so, return it, else abort
checkValue :: (t -> Bool) -> String -> t -> t
checkValue tst msg val = if tst val then val else shouldnt msg


-- |Like fromJust, but with its own error message
trustFromJust :: String -> (Maybe t) -> t
trustFromJust msg Nothing = shouldnt $ "trustFromJust in " ++ msg
trustFromJust _ (Just val) = val


-- |Monadic version of trustFromJust
trustFromJustM :: Monad m => String -> (m (Maybe t)) -> m t
trustFromJustM msg computation = do
    maybe <- computation
    return $ trustFromJust msg maybe


showMessages :: Compiler ()
showMessages = do
    messages <- reverse <$> gets msgs
    liftIO $ mapM_ showMessage messages


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


whenLogging :: LogSelection -> Compiler () -> Compiler ()
whenLogging selector action = do
    loggingSet <- gets (optLogAspects . options)
    when (Set.member selector loggingSet)
      action


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
