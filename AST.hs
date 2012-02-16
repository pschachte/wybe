--  File     : AST.hs
--  Author   : Peter Schachte
--  Origin   : Thu Oct 14 23:30:58 2010
--  Purpose  : Abstract Syntax Tree for Frege language
--  Copyright: © 2010-2012 Peter Schachte.  All rights reserved.

module AST (-- Types just for parsing
  Item(..), Visibility(..), maxVisibility, minVisibility,
  TypeProto(..), TypeSpec(..), FnProto(..),
  ProcProto(..), Param(..), Stmt(..), 
  LoopStmt(..), Exp(..), Generator(..),
  -- Source Position Types
  Placed(..), place, content, maybePlace,
  -- AST types
  Module(..), ModuleInterface(..), ModSpec, ProcDef(..), Ident, VarName, 
  ProcName, TypeDef(..), ResourceDef(..), FlowDirection(..),  argFlowDirection,
  expToStmt, Prim(..), PrimArg(..), extractInterface,
  -- Stateful monad for the compilation process
  CompilerState(..), Compiler, runCompiler, compileSubmodule, compileImport,
  getState, getDirectory, getModuleName, getModuleParams, option, 
  optionallyPutStr, errMsg, addErrMsgs, initVars, freshVar, nextProcId, 
  addImport, addType, addSubmod, lookupType, publicType,
  addResource, lookupResource, publicResource,
  addProc, replaceProc, lookupProc, publicProc,
  reportErrors
  ) where

import Options
import Data.Maybe
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Text.ParserCombinators.Parsec.Pos
import System.FilePath
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans (liftIO)

----------------------------------------------------------------
--                      Types Just For Parsing
----------------------------------------------------------------

data Item
     = TypeDecl Visibility TypeProto [Item] (Maybe SourcePos)
     | ModuleDecl Visibility Ident [Item] (Maybe SourcePos)
     | ImportMods Visibility Bool [ModSpec] (Maybe SourcePos)
     | ImportItems Visibility Bool ModSpec [Ident] (Maybe SourcePos)
     | ResourceDecl Visibility Ident TypeSpec (Maybe SourcePos)
     | FuncDecl Visibility FnProto TypeSpec (Placed Exp) (Maybe SourcePos)
     | ProcDecl Visibility ProcProto [Placed Stmt] (Maybe SourcePos)
     | CtorDecl Visibility FnProto (Maybe SourcePos)
     | StmtDecl Stmt (Maybe SourcePos)

data Visibility = Public | Private
                  deriving (Eq, Show)

maxVisibility :: Visibility -> Visibility -> Visibility
maxVisibility Public _ = Public
maxVisibility _ Public = Public
maxVisibility _      _ = Private

minVisibility :: Visibility -> Visibility -> Visibility
minVisibility Private _ = Private
minVisibility _ Private = Private
minVisibility _       _ = Public

data TypeProto = TypeProto Ident [Ident]

data FnProto = FnProto Ident [Param]


----------------------------------------------------------------
--                    Handling Source Positions
----------------------------------------------------------------

data Placed t
    = Placed t SourcePos
    | Unplaced t

place :: Placed t -> Maybe SourcePos
place (Placed _ pos) = Just pos
place (Unplaced _) = Nothing

content :: Placed t -> t
content (Placed content _) = content
content (Unplaced content) = content

maybePlace :: t -> Maybe SourcePos -> Placed t
maybePlace t (Just pos) = Placed t pos
maybePlace t Nothing    = Unplaced t


----------------------------------------------------------------
--                    Compiler monad
----------------------------------------------------------------

data CompilerState = Compiler {
  options :: Options,   -- compiler options specified on the command line
  parseTree :: [Item],  -- the current module's parse tree
  varCount :: Int,      -- a counter for introduced variables (per proc)
  procCount :: Int,     -- a counter for gensym-ed proc names
  errs :: [String],     -- error messages
  modul :: Module       -- the module being produced
  } deriving Show

type Compiler = StateT CompilerState IO

runCompiler :: Options -> [Item] -> FilePath -> Ident -> Maybe [Ident] -> 
              Maybe SourcePos -> Compiler () -> IO (Module,[String])
runCompiler opts parse dir modname params pos comp = do
    final <- execStateT comp $ initCompiler opts parse dir modname 
            params pos
    return $ (modul final,errs final)

compileSubmodule :: [Item] -> FilePath -> Ident -> Maybe [Ident] -> 
                   Maybe SourcePos -> Visibility -> Compiler () -> Compiler ()
compileSubmodule items dir modname params pos vis comp = do
    submod <- compileImport items dir modname params pos vis comp
    addSubmod modname submod vis
    

compileImport :: [Item] -> FilePath -> Ident -> Maybe [Ident] -> 
                   Maybe SourcePos -> Visibility -> Compiler () -> Compiler Module
compileImport items dir modname params pos vis comp = do
    state <- get
    let opts = options state
    (submod,errs) <- liftIO . runCompiler opts items dir modname 
                    params pos $ comp
    addErrMsgs errs
    return submod
    

initCompiler :: Options -> [Item] -> FilePath -> Ident -> Maybe [Ident] -> 
               Maybe SourcePos -> CompilerState
initCompiler opts parse dir name params pos = 
    let (typs,pubtyps) =
            case params of
                Nothing -> (Map.empty, Map.empty)
                Just params' ->
                    (Map.insert name 
                     (TypeDef (List.length params') pos) Map.empty,
                     Map.insert name (List.length params') Map.empty)
    in Compiler opts parse 0 0 [] $
       Module dir name params 
       (ModuleInterface pubtyps Set.empty Map.empty Set.empty Set.empty) 
       (Just $ ModuleImplementation Map.empty Map.empty typs 
        Map.empty Map.empty)


getState :: (CompilerState -> t) -> Compiler t
getState selector = do
    state <- get
    return $ selector state

getModule :: Compiler Module
getModule = getState modul

setModule :: Module -> Compiler ()
setModule mod = do
    state <- get
    put state { modul = mod }

getDirectory :: Compiler FilePath
getDirectory = do
    modl <- getModule
    return $ modDirectory modl

getModuleName :: Compiler Ident
getModuleName = do
  modl <- getModule
  return $ modName modl

getModuleParams :: Compiler (Maybe [Ident])
getModuleParams = do
  modl <- getModule
  return $ modParams modl

getModuleInterface :: Compiler ModuleInterface
getModuleInterface = do
  modl <- getModule
  return $ modInterface modl

getModuleImplementation :: Compiler (Maybe ModuleImplementation)
getModuleImplementation = do
  modl <- getModule
  return $ modImplementation modl

getModuleImplementationField :: (ModuleImplementation -> t) ->
                               Compiler (Maybe t)
getModuleImplementationField fn = do
  imp <- getModuleImplementation
  case imp of
      Nothing -> return Nothing
      Just imp' -> return $ Just $ fn imp'

getModuleImplementationMaybe :: (ModuleImplementation -> Maybe t) ->
                               Compiler (Maybe t)
getModuleImplementationMaybe fn = do
  imp <- getModuleImplementation
  case imp of
      Nothing -> return Nothing
      Just imp' -> return $ fn imp'



errMsg :: String -> Maybe SourcePos -> Compiler ()
errMsg msg pos = addErrMsgs [makeMessage msg pos]

addErrMsgs :: [String] -> Compiler ()
addErrMsgs msgs = do
    state <- get
    put state { errs = (errs state) ++ msgs }

makeMessage :: String -> Maybe SourcePos -> String
makeMessage msg Nothing = msg
makeMessage msg (Just pos) =
  (sourceName pos) ++ ":" ++ 
  show (sourceLine pos) ++ ":" ++ 
  show (sourceColumn pos) ++ ": " ++ 
  msg

initVars :: Compiler ()
initVars = do
  state <- get
  put state { varCount = 0 }

freshVar :: Compiler String
freshVar = do
  state <- get
  let ctr = varCount state
  put state { varCount = ctr + 1 }
  return $ "$tmp" ++ (show ctr)

nextProcId :: Compiler Int
nextProcId = do
  state <- get
  let ctr = 1 + procCount state
  put state { procCount = ctr }
  return ctr


updateInterface :: Visibility -> (ModuleInterface -> ModuleInterface) -> 
                  Compiler ()
updateInterface Private interfaceOp = return ()  -- do nothing
updateInterface Public interfaceOp = do         -- update the interface
    oldmod <- getModule
    setModule oldmod { modInterface = interfaceOp $ modInterface oldmod }


updateImplementation :: (ModuleImplementation -> ModuleImplementation) -> 
                       Compiler ()
updateImplementation implOp = do
    oldmod <- getModule
    case modImplementation oldmod of
        Nothing -> return ()
        Just impl -> setModule oldmod { modImplementation = Just $ implOp impl }


addType :: Ident -> TypeDef -> Visibility -> Compiler ()
addType name def@(TypeDef arity _) vis = do
    updateImplementation (updateModTypes (Map.insert name def))
    updateInterface vis (updatePubTypes (Map.insert name arity))

addSubmod :: Ident -> Module -> Visibility -> Compiler ()
addSubmod name modl vis = do
    updateImplementation (updateModSubmods (Map.insert name modl))
    updateInterface vis (updatePubDependencies (Set.insert name))

lookupType :: Ident -> Compiler (Maybe TypeDef)
lookupType name = 
    getModuleImplementationMaybe (\imp -> Map.lookup name $ modTypes imp)


publicType :: Ident -> Compiler Bool
publicType name = do
  int <- getModuleInterface
  return $ Map.member name (pubTypes int)

addResource :: Ident -> ResourceDef -> Visibility -> Compiler ()
addResource name def vis = do
    updateImplementation (updateModResources (Map.insert name def))
    updateInterface vis (updatePubResources (Set.insert name))

lookupResource :: Ident -> Compiler (Maybe ResourceDef)
lookupResource name =
    getModuleImplementationMaybe (\imp -> Map.lookup name $ modResources imp)

publicResource :: Ident -> Compiler Bool
publicResource name = do
  mod <- getModule
  return $ Set.member name (pubResources $ modInterface mod)

addImport :: ModSpec -> Bool -> (Maybe [Ident]) -> Visibility -> Compiler ()
addImport modspec imp specific vis = do
    updateImplementation
      (updateModImports
       (\moddeps -> 
         let (ModDependency uses imps) = 
                 Map.findWithDefault 
                 (ModDependency ImportNothing ImportNothing) 
                 modspec moddeps
             uses' = if imp then uses else addImports specific vis uses
             imps' = if imp then addImports specific vis imps else imps
         in Map.insert modspec (ModDependency uses' imps') moddeps))
    updateInterface vis (updateDependencies (Set.insert $ last modspec))

addProc :: Ident -> ProcProto -> [Placed Prim] -> (Maybe SourcePos)
           -> Visibility -> Compiler ()
addProc name proto stmts pos vis = do
    newid <- nextProcId
    updateImplementation
      (updateModProcs
       (\procs ->
         let defs  = ProcDef newid proto stmts pos:findWithDefault [] name procs
         in  Map.insert name defs procs))
    updateInterface vis
      (updatePubProcs (mapListInsert name (ProcCallInfo newid proto)))

mapListInsert :: Ord a => a -> b -> Map a [b] -> Map a [b]
mapListInsert key elt =
    Map.alter (\maybe -> Just $ elt:fromMaybe [] maybe) key


replaceProc :: Ident -> Int -> ProcProto -> [Placed Prim] -> (Maybe SourcePos)
               -> Visibility -> Compiler ()
replaceProc name id proto stmts pos vis = do
    updateImplementation
      (updateModProcs
       (\procs -> 
         let olddefs = findWithDefault [] name procs
             (_,rest) = List.partition (\(ProcDef oldid _ _ _) -> id==oldid) 
                        olddefs
         in Map.insert name (ProcDef id proto stmts pos:rest) procs))


lookupProc :: Ident -> Compiler (Maybe [ProcDef])
lookupProc name = 
    getModuleImplementationMaybe (\imp -> Map.lookup name $ modProcs imp)


publicProc :: Ident -> Compiler Bool
publicProc name = do
  int <- getModuleInterface
  return $ Map.member name $ pubProcs int


option :: (Options -> t) -> Compiler t
option opt = do
    opts <- getState options
    return $ opt opts


optionallyPutStr :: (Options -> Bool) -> (CompilerState -> String) ->
                   Compiler ()
optionallyPutStr opt selector = do
    check <- option opt
    state <- get
    when check (liftIO . putStrLn $ selector state)


reportErrors :: Compiler ()
reportErrors = do
    errs <- getState errs
    unless (List.null errs) (liftIO . putStrLn $ intercalate "\n" errs)

----------------------------------------------------------------
--                            AST Types
----------------------------------------------------------------

-- Holds everything needed to compile a module
data Module = Module {
  modDirectory :: FilePath,              -- The directory the module is in
  modName :: Ident,                      -- The module name
  modParams :: Maybe [Ident],            -- The type parameters, if a type
  modInterface :: ModuleInterface,       -- The public face of this module
  modImplementation :: Maybe ModuleImplementation -- the module's implementation
  }

-- hack around Haskell's terrible setter syntax
updateModImplementation :: (ModuleImplementation -> ModuleImplementation) ->
                          Module -> Module
updateModImplementation fn mod =
    case modImplementation mod of
        Nothing -> mod
        Just impl -> 
            mod { modImplementation = Just $ fn impl }

updateModInterface :: (ModuleInterface -> ModuleInterface) ->
                     Module -> Module
updateModInterface fn mod =
    mod { modInterface = fn $ modInterface mod }


-- Holds everything needed to compile code that uses a module
data ModuleInterface = ModuleInterface {
    pubTypes :: Map Ident Int,       -- The types this module exports
    pubResources :: Set Ident,       -- XXX not handling resources properly
    pubProcs :: Map Ident [ProcCallInfo], -- The procs this module exports
    pubDependencies :: Set Ident,    -- The other modules this module exports
    dependencies :: Set Ident            -- The other modules that must be linked
    }                                   -- in by modules that depend on this one

-- hack around Haskell's terrible setter syntax
updatePubTypes :: (Map Ident Int -> Map Ident Int) -> 
                 ModuleInterface -> ModuleInterface
updatePubTypes fn modint = modint {pubTypes = fn $ pubTypes modint}

updatePubResources :: (Set Ident -> Set Ident) -> ModuleInterface -> ModuleInterface
updatePubResources fn modint = modint {pubResources = fn $ pubResources modint}

updatePubProcs :: (Map Ident [ProcCallInfo] -> Map Ident [ProcCallInfo]) -> 
                 ModuleInterface -> ModuleInterface
updatePubProcs fn modint = modint {pubProcs = fn $ pubProcs modint}

updatePubDependencies :: (Set Ident -> Set Ident) -> 
                        ModuleInterface -> ModuleInterface
updatePubDependencies fn modint = 
    modint {pubDependencies = fn $ pubDependencies modint}

updateDependencies :: (Set Ident -> Set Ident) -> ModuleInterface -> ModuleInterface
updateDependencies fn modint = modint {dependencies = fn $ dependencies modint}


-- Holds everything needed to compile the module itself
data ModuleImplementation = ModuleImplementation {
    modImports :: Map ModSpec ModDependency, -- All modules this module imports
    modSubmods :: Map Ident Module,        -- All submodules
    modTypes :: Map Ident TypeDef,         -- All types defined by this module
    modResources :: Map Ident ResourceDef, -- All resources defined by this module
    modProcs :: Map Ident [ProcDef]        -- All procs defined by this module
    }                                   -- in by modules that depend on this one


-- hack around Haskell's terrible setter syntax
updateModImports :: (Map ModSpec ModDependency -> Map ModSpec ModDependency) -> 
                   ModuleImplementation -> ModuleImplementation
updateModImports fn modimp = modimp {modImports = fn $ modImports modimp}

updateModSubmods :: (Map Ident Module -> Map Ident Module) -> 
                   ModuleImplementation -> ModuleImplementation
updateModSubmods fn modimp = modimp {modSubmods = fn $ modSubmods modimp}

updateModTypes :: (Map Ident TypeDef -> Map Ident TypeDef) -> 
                 ModuleImplementation -> ModuleImplementation
updateModTypes fn modimp = modimp {modTypes = fn $ modTypes modimp}

updateModResources :: (Map Ident ResourceDef -> Map Ident ResourceDef) -> 
                     ModuleImplementation -> ModuleImplementation
updateModResources fn modimp = modimp {modResources = fn $ modResources modimp}

updateModProcs :: (Map Ident [ProcDef] -> Map Ident [ProcDef]) -> 
                 ModuleImplementation -> ModuleImplementation
updateModProcs fn modimp = modimp {modProcs = fn $ modProcs modimp}


extractInterface :: Module -> ModuleInterface
extractInterface = modInterface
    

type Ident = String

type VarName = String

type ProcName = String

type ModSpec = [Ident]

data ModDependency = ModDependency ImportSpec ImportSpec -- (uses, imports)

data ImportSpec = ImportNothing
                | ImportSpec (Map Ident Visibility) (Maybe Visibility)

addImports :: (Maybe [Ident]) -> Visibility -> ImportSpec -> ImportSpec
addImports Nothing vis ImportNothing = ImportSpec Map.empty $ Just vis
addImports Nothing vis (ImportSpec map Nothing) = 
    ImportSpec map $ Just vis
addImports Nothing vis (ImportSpec map (Just vis')) = 
    ImportSpec map $ Just $ maxVisibility vis vis'
addImports (Just imps) vis (ImportSpec map vis') = 
    ImportSpec (List.foldr (\k -> Map.insert k vis) map imps) vis'
addImports (Just imps) vis ImportNothing = 
    ImportSpec (List.foldr (\k -> Map.insert k vis) Map.empty imps) Nothing

data TypeDef = TypeDef Int (Maybe SourcePos)

typeDefArity :: TypeDef -> Int
typeDefArity (TypeDef arity _) = arity


data ResourceDef = CompoundResource [Ident] (Maybe SourcePos)
                 | SimpleResource TypeSpec (Maybe SourcePos)

data ProcDef = ProcDef ProcID ProcProto [Placed Prim] (Maybe SourcePos)

data ProcCallInfo = ProcCallInfo ProcID ProcProto

procCallInfo :: ProcDef -> ProcCallInfo
procCallInfo (ProcDef id proto _ _) = ProcCallInfo id proto


type ProcID = Int

data TypeSpec = TypeSpec Ident [TypeSpec] | Unspecified

data Constant = Int Int
              | Float Double
              | Char Char
              | String String
                deriving Show

data ProcProto = ProcProto ProcName [Param]

data Param = Param VarName TypeSpec FlowDirection

data FlowDirection = ParamIn | ParamOut | ParamInOut | NoFlow
      deriving (Show,Eq)

data Stmt
     = ProcCall Ident [Placed Exp]
     | ForeignCall Ident Ident [Placed Exp]
     | Cond (Placed Exp) [Placed Stmt] [Placed Stmt]
     | Loop [Placed LoopStmt]
     | Nop

data LoopStmt
     = For Generator
     | BreakIf (Placed Exp)
     | NextIf (Placed Exp)
     | NormalStmt (Placed Stmt)

data Exp
      = IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Var VarName FlowDirection
      | Where [Placed Stmt] (Placed Exp)
      | CondExp (Placed Exp) (Placed Exp) (Placed Exp)
      | Fncall Ident [Placed Exp]
      | ForeignFn String String [Placed Exp]

data Generator 
      = In VarName (Placed Exp)
      | InRange VarName (Placed Exp) ProcName (Placed Exp) 
        (Maybe (ProcName,Placed Exp))

data Prim
     = PrimCall ProcName (Maybe ProcID) [PrimArg]
     | PrimForeign String ProcName (Maybe ProcID) [PrimArg]
     | PrimCond VarName [[Placed Prim]]
     | PrimLoop [Placed Prim]
     | PrimBreakIf VarName
     | PrimNextIf VarName

data PrimArg 
     = ArgVar VarName FlowDirection
     | ArgInt Integer
     | ArgFloat Double
     | ArgString String
     | ArgChar Char

argFlowDirection :: PrimArg -> FlowDirection
argFlowDirection (ArgVar _ flow) = flow
argFlowDirection (ArgInt _) = ParamIn
argFlowDirection (ArgFloat _) = ParamIn
argFlowDirection (ArgString _) = ParamIn
argFlowDirection (ArgChar _) = ParamIn


expToStmt :: Exp -> Stmt
expToStmt (Fncall name args) = ProcCall name args
expToStmt (ForeignFn lang name args) = ForeignCall lang name args


----------------------------------------------------------------
--                      Showing Compiler State
----------------------------------------------------------------

instance Show Item where
  show (TypeDecl vis name items pos) =
    show vis ++ " type " ++ show name ++ " is" 
    ++ showMaybeSourcePos pos ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\nend\n"
  show (ImportMods vis unqualified mods pos) =
      show vis ++ (if unqualified then " import " else " use ") ++ 
      showModSpecs mods ++ showMaybeSourcePos pos ++ "\n  "
  show (ImportItems vis unqualified mod specs pos) =
      show vis ++ " from " ++ showModSpec mod ++
      (if unqualified then " import " else " use ") ++ intercalate ", " specs
      ++ showMaybeSourcePos pos ++ "\n  "
  show (ModuleDecl vis name items pos) =
    show vis ++ " module " ++ show name ++ " is" 
    ++ showMaybeSourcePos pos ++ "\n  "
    ++ intercalate "\n  " (List.map show items)
    ++ "\nend\n"
  show (ResourceDecl vis name typ pos) =
    show vis ++ " resource " ++ show name ++ ":" ++ show typ
    ++ showMaybeSourcePos pos
  show (FuncDecl vis proto typ exp pos) =
    show vis ++ " func " ++ show proto ++ ":" ++ show typ
    ++ showMaybeSourcePos pos
    ++ " = " ++ show exp
  show (ProcDecl vis proto stmts pos) =
    show vis ++ " proc " ++ show proto
    ++ showMaybeSourcePos pos
    ++ show stmts
  show (CtorDecl vis proto pos) =
    show vis ++ " ctor " ++ show proto
    ++ showMaybeSourcePos pos
  show (StmtDecl stmt pos) =
    show stmt ++ showMaybeSourcePos pos

showModSpec :: ModSpec -> String
showModSpec spec = intercalate "." spec

showModSpecs :: [ModSpec] -> String
showModSpecs specs = intercalate ", " $ List.map showModSpec specs

showModDependency :: ModSpec -> ModDependency -> String
showModDependency mod (ModDependency uses imports) =
     showImportOrUse "import" mod imports
     ++ showImportOrUse "use" mod uses

visibilityPrefix :: Visibility -> String
visibilityPrefix Public = "public "
visibilityPrefix Private = ""

showImportOrUse :: String -> ModSpec -> ImportSpec -> String
showImportOrUse _ _ ImportNothing = ""
showImportOrUse directive mod (ImportSpec map vis) =
    (case vis of
        Just vis' -> visibilityPrefix vis' ++ directive ++ " " ++ 
                    showModSpec mod ++ " "
        Nothing -> "") ++
    (let mapKVs = assocs map
         pubs = [k | (k,v) <- mapKVs, v==Public]
         privs = [k | (k,v) <- mapKVs, v==Private]
     in (if List.null pubs then "" else 
             "public from " ++ showModSpec mod ++ " " ++ directive ++ " " ++
             intercalate ", " pubs) ++
        (if List.null privs then "" else 
             "from " ++ showModSpec mod ++ " " ++ directive ++ " " ++
             intercalate ", " privs))

instance Show TypeProto where
  show (TypeProto name []) = name
  show (TypeProto name args) = name ++ "(" ++ intercalate "," args ++ ")"

instance Show FnProto where
  show (FnProto name []) = name
  show (FnProto name params) = 
    name ++ "(" ++ intercalate "," (List.map show params) ++ ")"

instance Show t => Show (Placed t) where
  show pl = show (content pl) ++ showMaybeSourcePos (place pl)
    
showMaybeSourcePos :: Maybe SourcePos -> String
showMaybeSourcePos (Just pos) = 
  " {" ++ takeBaseName (sourceName pos) ++ ":" 
  ++ show (sourceLine pos) ++ ":" ++ show (sourceColumn pos) ++ "}"
showMaybeSourcePos Nothing = " {?}"

instance Show Module where
    show mod =
        let int  = modInterface mod
            maybeimpl = modImplementation mod
        in "\n Module " ++ modName mod ++ maybeShow "(" (modParams mod) ")" ++
           "\n  public submods  : " ++ showIdSet (pubDependencies int) ++
           "\n  public types    : " ++ 
           intercalate ", " 
           [n ++ "/" ++ show a | (n,a) <- Map.assocs $ pubTypes int] ++
           "\n  public resources: " ++ showIdSet (pubResources int) ++
           "\n  public procs    : " ++ 
           intercalate "\n                    " 
           [show proto ++ " <" ++ show id ++ ">" | 
            (ProcCallInfo id proto) <- 
                List.concat $ Map.elems $ pubProcs int] ++
           if isNothing maybeimpl then "\n  implementation not available"
           else let impl = fromJust maybeimpl
                in
                 "\n  imports         : " ++
                 intercalate "\n                    " 
                 [showModDependency mod dep | 
                  (mod,dep) <- Map.assocs $ modImports impl] ++
                 "\n  types           : " ++ showMap (modTypes impl) ++
                 "\n  resources       : " ++ showMap (modResources impl) ++
                 "\n  procs           : " ++ showMap (modProcs impl) ++ "\n" ++
                 "\nSubmodules of " ++ modName mod ++ ":\n" ++ 
                 showMap (modSubmods impl)

showIdSet :: Set Ident -> String
showIdSet set = intercalate ", " $ Set.elems set

showMap :: Show v => Map Ident v -> String
showMap m = intercalate "\n                    " 
            $ List.map (\(k,v) -> k ++ ": " ++ show v) $ Map.assocs m

instance Show TypeDef where
  show (TypeDef arity pos) = 
    "arity " ++ show arity ++ " " ++ showMaybeSourcePos pos

instance Show ResourceDef where
  show (CompoundResource ids pos) =
    intercalate ", " ids ++ showMaybeSourcePos pos
  show (SimpleResource typ pos) =
    show typ ++ showMaybeSourcePos pos

instance Show ProcDef where
  show (ProcDef i proto def pos) =
    "\nproc " ++ show proto ++ " (id " ++ show i ++ "): " 
    ++ showMaybeSourcePos pos 
    ++ showBlock 4 def

instance Show TypeSpec where
  show Unspecified = "?"
  show (TypeSpec ident []) = ident
  show (TypeSpec ident args) = 
    ident ++ "(" ++ (intercalate "," $ List.map show args) ++ ")"

instance Show ProcProto where
  show (ProcProto name params) = 
    name ++ "(" ++ (intercalate ", " $ List.map show params) ++ ")"

instance Show Param where
  show (Param name typ dir) =
    flowPrefix dir ++ name ++ ":" ++ show typ

flowPrefix :: FlowDirection -> String
flowPrefix NoFlow     = ""
flowPrefix ParamIn    = ""
flowPrefix ParamOut   = "?"
flowPrefix ParamInOut = "!"

startLine :: Int -> String
startLine ind = "\n" ++ replicate ind ' '

showBlock :: Int -> [Placed Prim] -> String
showBlock ind stmts = concat $ List.map (showPrim ind) stmts

showPrim :: Int -> Placed Prim -> String
showPrim ind stmt = showPrim' ind (content stmt) (place stmt)

showPrim' :: Int -> Prim -> Maybe SourcePos -> String
showPrim' ind (PrimCall name id args) pos =
  startLine ind ++ name ++ maybeShow "<" id ">"
  ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  ++ showMaybeSourcePos pos
showPrim' ind (PrimForeign lang name id args) pos =
  startLine ind ++ "foreign " ++ lang ++ " " ++ name ++ maybeShow "<" id ">"
  ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  ++ showMaybeSourcePos pos
showPrim' ind (PrimCond var blocks) pos =
  startLine ind ++ "case " ++ var ++ " of" 
  ++ showMaybeSourcePos pos
  ++ showCases 0 (ind+2) (ind+4) blocks
  ++ startLine ind ++ "end"
showPrim' ind (PrimLoop block) pos =
  startLine ind ++ "do " ++ showMaybeSourcePos pos
  ++ showBlock (ind+4) block
  ++ startLine ind ++ "end"
showPrim' ind (PrimBreakIf var) pos =
  startLine ind ++ "until " ++ var ++ showMaybeSourcePos pos
showPrim' ind (PrimNextIf var) pos =
  startLine ind ++ "unless " ++ var ++ showMaybeSourcePos pos

showCases :: Int -> Int -> Int -> [[Placed Prim]] -> String
showCases _ _ _ [] = ""
showCases num labelInd blockInd (block:blocks) =
  startLine labelInd ++ show num ++ ":"
  ++ showBlock blockInd block
  ++ showCases (num+1) labelInd blockInd blocks

instance Show Stmt where
  show (ProcCall name args) =
    name ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  show (Cond exp thn els) =
    "if" ++ show (content exp) ++ " then"
    ++ show thn
    ++ " else "
    ++ show els
    ++ " end"
  show (Loop lstmts) =
    "do " ++ concat (List.map show lstmts) ++ " end"

instance Show PrimArg where
  show (ArgVar name dir) = flowPrefix dir ++ name
  show (ArgInt i) = show i
  show (ArgFloat f) = show f
  show (ArgString s) = show s
  show (ArgChar c) = show c


instance Show LoopStmt where
  show (For gen) = "for " ++ show gen
  show (BreakIf cond) = "until " ++ show cond
  show (NextIf cond) = "unless " ++ show cond
  show (NormalStmt stmt) = show stmt
  
instance Show Exp where
  show (IntValue i) = show i
  show (FloatValue f) = show f
  show (StringValue s) = show s
  show (CharValue c) = show c
  show (Var name dir) = (flowPrefix dir) ++ name
  show (Where stmts exp) = show exp ++ " where " ++ show stmts
  show (CondExp cond thn els) = 
    "if " ++ show cond ++ " then " ++ show thn ++ " else " ++ show els
  show (Fncall fn args) = 
    fn ++ "(" ++ intercalate ", " (List.map show args) ++ ")"
  show (ForeignFn lang fn args) = 
    "foreign " ++ lang ++ " " ++ fn 
    ++ "(" ++ intercalate ", " (List.map show args) ++ ")"

instance Show Generator where
  show (In var exp) = var ++ " in " ++ show exp
  show (InRange var start updateOp step Nothing) =
    var ++ " from " ++ show start ++ " by " ++ updateOp ++ show step
  show (InRange var start updateOp step (Just end)) =
    show (InRange var start updateOp step Nothing) ++ " to " ++ show end

-- maybeShow pre maybe pos
-- if maybe has something, show pre, the maybe payload, and post
-- if the maybe is Nothing, don't show anything

maybeShow :: Show t => String -> Maybe t -> String -> String
maybeShow pre Nothing pos = ""
maybeShow pre (Just something) post =
  pre ++ show something ++ post
