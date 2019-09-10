--  File     : Builder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Jan 31 16:37:48 2012
--  Purpose  : Handles compilation at the module level.
--  Copyright: (c) 2012-2015 Peter Schachte.  All rights reserved.
--
--  BEGIN MAJOR DOC
--  The wybe compiler handles module dependencies, and builds
--  executables by itself, without the need for build tools like
--  make.  The function buildTarget is responsible for determining
--  what source files need to be compiled, and for building the
--  final outputs (whether executable, object file, archive, etc.).
--
--  To keep compile times manageable while supporting optimisation,
--  we compile modules bottom-up, ensuring that all a module's
--  imports are compiled before compling the module itself. In the
--  case of circular module dependencies, each strongly-connected
--  component in the module dependency graph is compiled as a unit.
--  This is handled by the compileModule function, which includes
--  the functionality for finding the SCCs in the module dependency
--  graph. The monadic functions enterModule and exitModule,
--  imported from the AST module, implement the SCC functionality,
--  with exitModule returning a list of modules that form an SCC.
--  Between enterModule and exitModule, the Normalise.normalise
--  function is called to record the code of the module and to
--  record all its dependencies. Each SCC is compiled by the
--  compileModSCC function.
--
--  One shortcoming of the bottom-up approach is that some analyses
--  are best performed top-down.  For example, we can only eliminate
--  unneeded procedures when we've seen all the calls to all
--  procedures in the module.  By compiling bottom-up, we do not have
--  access to this information.  Our solution to this problem is to
--  perform the top-down analysis after the bottom-up compilation,
--  generating results that we can use for the next compilation.  If
--  the top-down analysis produces results that conflict with the
--  previous top-down analysis, so that the compilation produced
--  invalid results, then we must re-compile enough of the program to
--  fix the problem.  It is hoped that this will happen infrequently
--  enough that the time saved by not usually having to make separate
--  traversals for analysis and compilation will more than make up
--  for the few times we need to recompile.
--
--  Ensuring that all compiler phases happen in the right order is
--  subtle, particularly in the face of mutual module dependencies.
--  Following are the ordering dependencies.
--
--  * Types: the types a type depends on need to have been processed
--  before the type itself, so that sizes are known. In the case of
--  recursive or mutually recursive type dependencies, all types in
--  the recursion must be pointers. Types are transformed into
--  submodules, and constructors, deconstructors, accessors,
--  mutators, and auxiliary type procedures (equality tests, plus
--  eventually comparisons, printers, pretty printers, etc.) are all
--  generated as procedures within those submodules.  Therefore,
--  these must be handled as submodules are.
--
--  * Resources:  the resources a resource depends on must have been
--  processed before the resource itself.  (We currently don't
--  support defining resources in terms of others, but the plan is
--  to support that.)  The types in the module that defines a
--  resource, and all module dependencies, must have been processed
--  at least enough to know they have been defined to process the
--  resource declaration.
--
--  * Top-level statements in a module: these are transformed to
--  statements in a special procedure whose name is the empty string
--  as the statements are processed, so their dependencies are the
--  same as for statements in ordinary procedure bodies.
--
--  * Functions: functions and function calls are transformed to
--  procedures and procedure calls without reference to anything
--  external to the functions themselves, so function dependencies
--  behave exactly like procedure dependencies.
--
--  * Procedures: the procedures a procedure calls must have been
--  type and mode checked before they can themselves be type/mode
--  checked, and must be analysed and optimised before they can
--  themselves be analysed/optimised. All the procedures in the
--  (sub)modules that define each type a procedure uses, as either a
--  parameter or local variable type, must have been processed the
--  same way before processing the procedure itself.
--
--  * Submodules: the submodules of a module, including the types,
--  must be processed as mutual dependencies of that module, which
--  they are. The nested submodules of a module (including types)
--  have access to all public and private members of the parent
--  module, and the parent has access to all public members of the
--  parent, so they are mutual dependencies.
--
--  This means only minimal processing can be done before module
--  dependencies are noted and read in.  So we handle all these
--  dependencies by initially reading a module to be compiled and
--  handling contents as follows:
--
--  * Types:  create and enter the submodule, note that parent
--  imports it, and process its constructors and other contents.
--
--  * Submodules:  create and enter the submodule, note that parent
--  imports it, and process its contents.
--
--  * Resources:  Record for later processing.
--
--  * Pragmas:  Record for later processing.
--
--  * Constructors: record for later type layout, code generation,
--  etc.
--
--  * Top level statements:  add statements to the special "" proc
--  in the module, creating it if necessary.
--
--  * Procs and functions:  record them for later normalisation,
--  analysis, optimisation, etc.
--
--  Once we reach the end of a module or submodule, we call
--  exitModule, which returns a list of modules that form an SCC in
--  the module dependency graph.  That list is passed to
--  compileModSCC, which does the following:
--
--    1. Traverse all recorded type submodules in the module list
--       finding all type dependencies; topologically sort them and
--       identify SCCs. For each SCC:
--
--         1. Determine the type representation for all
--            constructors.
--
--         2. Record the primitive representation of the type.
--
--         3. Generate and record all constructor, accessor,
--            mutator, and utility procs.
--
--       This is handled in the Normalise module.
--
--    2. Check all resource imports and exports. (Resources)
--
--    3. Normalise all recorded procs in their modules, including
--       generated constructors, etc. (Normalise)
--
--    4. Validate the types of exported procs. (Types)
--
--    5. Check proc argument types and modes are checked, and
--       resolve called procs. (Types)
--
--    6. Check proc resources and transform them to args.
--      (Resources)
--
--    7. Transform away branches, loops, and nondeterminism.
--       (Unbranch)
--
--    8. Topologically sort proc call graph and identify SCCs.  For
--       each SCC, bottom-up, do the following:
--
--         1. Compile procs to clausal form (Clause)
--
--         2. Optimise procs (Optimise)
--
--  END MAJOR DOC

-- |Code to oversee the compilation process.
module Builder (buildTargets, compileModule) where

import           Analysis
import           AST
import           ASTShow                   (logDump)
import           Blocks                    (blockTransformModule,
                                            concatLLVMASTModules)
import           Callers                   (collectCallers)
import           Clause                    (compileProc)
import           Config
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import qualified Data.ByteString.Char8     as BS
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Set                  as Set
import           Data.Maybe
import           Emit
import           Normalise                 (normalise, completeNormalisation)
import           ObjectInterface

import           Optimise                  (optimiseMod)
import           Options                   (LogSelection (..), Options,
                                            optForce, optForceAll, optLibDirs)
import           NewParser                 (parseWybe)
import           Resources                 (resourceCheckMod,
                                            transformProcResources,
                                            canonicaliseProcResources)
import           Scanner                   (fileTokens)
import           System.Directory
import           System.FilePath
import           System.Exit
import           Transform                 (transformProc)
import           Types                     (typeCheckMod,
                                            validateModExportTypes)
import           Unbranch                  (unbranchProc)
import           Snippets
import           BinaryFactory
import qualified Data.ByteString.Char8 as BS
import qualified LLVM.AST              as LLVMAST

------------------------ Handling dependencies ------------------------

-- |Build the specified targets with the specified options.
buildTargets :: Options -> [FilePath] -> Compiler ()
buildTargets opts targets = do
    possDirs <- gets (optLibDirs . options)
    -- load library first
    mapM_ (buildTarget $ optForce opts || optForceAll opts) targets
    showMessages
    stopOnError "building outputs"
    logDump FinalDump FinalDump "EVERYTHING"


-- |Build a single target; flag specifies to re-compile even if the
--  target is up-to-date.
buildTarget :: Bool -> FilePath -> Compiler ()
buildTarget force target = do
    Informational <!> "Building target: " ++ target
    let tType = targetType target
    case tType of
        UnknownFile ->
            Error <!> "Unknown target file type: " ++ target
        _ -> do
            let modname = takeBaseName target
            let dir = takeDirectory target
            built <- buildModuleIfNeeded force [modname] [dir]
            targetExists <- (liftIO . doesFileExist) target
            -- XXX not quite right:  we shouldn't build executable or archive
            -- if it already exists and none of the dependencies have changed
            if not built && targetExists && tType /= ExecutableFile
              then logBuild $ "Nothing to be done for target: " ++ target
              else do
                  logBuild $ "Emitting Target: " ++ target
                  case tType of
                     ObjectFile     -> emitObjectFile [modname] target
                     BitcodeFile    -> emitBitcodeFile [modname] target
                     AssemblyFile   -> emitAssemblyFile [modname] target
                     ArchiveFile    -> buildArchive target
                     ExecutableFile -> buildExecutable [modname] target
                     other          -> nyi $ "output file type " ++ show other
                  whenLogging Emit $ logLLVMString [modname]


-- |Compile or load a module dependency.
buildDependency :: ModSpec -> Compiler Bool
buildDependency modspec = do
    logBuild $ "Load dependency: " ++ showModSpec modspec
    force <- option optForceAll
    possDirs <- gets (optLibDirs . options)
    localDir <- getDirectory
    buildModuleIfNeeded force modspec (localDir:possDirs)


-- | Run compilation passes on a single module specified by [modspec] resulting
-- in the LPVM and LLVM forms of the module to be placed in the Compiler State
-- monad. The [force] flag determines whether the module is built from source
-- or its previous compilation is extracted from its corresponding object file.
buildModuleIfNeeded :: Bool    -- ^Force compilation of this module
              -> ModSpec       -- ^Module name
              -> [FilePath]    -- ^Directories to look in
              -> Compiler Bool -- ^Returns whether or not file
                              -- actually needed to be compiled
buildModuleIfNeeded force modspec possDirs = do
    loading <- gets (List.elem modspec . List.map modSpec . underCompilation)
    let clash kind1 f1 kind2 f2 = do
          Error <!> kind1 ++ " " ++ f1 ++ " and "
                    ++ kind2 ++ " " ++ f2 ++ " clash. There can only be one!"
    if loading
      then return False -- Already loading it; we'll handle it later
      else do
        maybemod <- getLoadedModule modspec
        logBuild $ "module " ++ showModSpec modspec ++ " is " ++
          (if isNothing maybemod then "not yet" else "already") ++
          " loaded"
        if isJust maybemod
          then return False -- already loaded:  nothing more to do
          else do
            srcOb <- moduleSources modspec possDirs
            logBuild $ show srcOb
            case srcOb of
                NoSource -> do
                    Error <!> "Could not find source for module " ++
                              showModSpec modspec
                              ++ "\nin directories:\n    "
                              ++ intercalate "\n    " possDirs
                    return False

                -- only object file exists
                ModuleSource Nothing (Just objfile) Nothing Nothing -> do
                    loaded <- loadModuleFromObjFile modspec objfile
                    unless loaded $ do
                        -- if extraction failed, it is uncrecoverable now
                        let err = "Object file " ++ objfile ++
                                  " yielded no LPVM modules for " ++
                                  showModSpec modspec ++ "."
                        Error <!> "No other options to pursue."
                        Error <!> err
                    return False

                ModuleSource (Just srcfile) Nothing Nothing Nothing -> do
                    -- only source file exists
                    buildModule modspec srcfile
                    return True

                ModuleSource (Just srcfile) (Just objfile) Nothing Nothing -> do
                    -- both source and object exist:  rebuild if necessary
                    srcDate <- (liftIO . getModificationTime) srcfile
                    dstDate <- (liftIO . getModificationTime) objfile
                    if force || srcDate > dstDate
                      then do
                        unless force (extractModules objfile)
                        buildModule modspec srcfile
                        return True
                      else do
                        loaded <- loadModuleFromObjFile modspec objfile
                        unless loaded $ do
                            -- Loading failed, fallback on source building
                            logBuild $ "Falling back on building " ++
                                showModSpec modspec
                            buildModule modspec srcfile
                        return $ not loaded

                ModuleSource Nothing Nothing (Just dir) _ -> do
                    -- directory exists:  rebuild contents if necessary
                    logBuild $ "Modname for directory: " ++ showModSpec modspec
                    buildDirectory dir modspec

                -- Error cases:

                ModuleSource (Just srcfile) Nothing (Just dir) _ -> do
                    clash "Directory" dir "source file" srcfile
                    return False

                ModuleSource (Just srcfile) Nothing _ (Just archive) -> do
                    clash "Archive" archive "source file" srcfile
                    return False

                ModuleSource Nothing (Just objfile) (Just dir) _ -> do
                    clash "Directory" dir "object file" objfile
                    return False

                ModuleSource Nothing (Just objfile) _ (Just archive) -> do
                    clash "Archive" archive "object file" objfile
                    return False

                _ -> shouldnt "inconsistent file existence"






-- |Actually load and compile the module
buildModule :: ModSpec -> FilePath -> Compiler ()
buildModule mspec srcfile = do
    tokens <- (liftIO . fileTokens) srcfile
    -- let parseTree = parse tokens
    let parseTree = parseWybe tokens srcfile
    either (\er -> do
               liftIO $ putStrLn $ "Syntax Error: " ++ show er
               liftIO exitFailure)
           (compileModule srcfile mspec Nothing)
           parseTree
    -- XXX Rethink parse tree hashing
    -- let currHash = hashItems parseTree
    -- extractedHash <- extractedItemsHash mspec
    -- case extractedHash of
    --     Nothing -> compileModule srcfile mspec Nothing parseTree
    --     Just otherHash ->
    --         if currHash == otherHash
    --         then do
    --             logBuild $ "... Hash for module " ++ showModSpec mspec ++
    --                 " matches the old hash."
    --             _ <- loadModuleFromObjFile mspec objfile
    --             return ()
    --         else compileModule srcfile mspec Nothing parseTree



-- |Build a directory as the module `dirmod`.
buildDirectory :: FilePath -> ModSpec -> Compiler Bool
buildDirectory dir dirmod = do
    logBuild $ "Building DIR: " ++ dir ++ ", into MODULE: "
        ++ showModSpec dirmod
    -- Make the directory a Module package
    enterModule dir dirmod Nothing Nothing
    updateModule (\m -> m { isPackage = True })

    -- Get wybe modules (in the directory) to build
    let makeMod x = dirmod ++ [x]
    wybemods <- liftIO $ List.map (makeMod . dropExtension)
        <$> wybeSourcesInDir dir
    -- Build the above list of modules
    opts <- gets options
    let force = optForceAll opts || optForce opts
    -- quick shortcut to build a module
    let build m = buildModuleIfNeeded force m [takeDirectory dir]
    built <- or <$> mapM build wybemods

    -- Helper to add new import of `m` to current module
    let updateImport m = do
            addImport m (importSpec Nothing Public)
            updateImplementation $
                updateModSubmods $ Map.insert (last m) m
    -- The module package imports all wybe modules in its source dir
    mapM_ updateImport wybemods
    mods <- exitModule
    logBuild $ "Generated directory module containing" ++ showModSpecs mods
    -- Run the compilation passes on this module package to append the
    -- procs from the imports to the interface.
    -- XXX Maybe run only the import pass, as there is no module source!
    compileModSCC mods
    return built



-- |Compile a file module given the parsed source file contents.
compileModule :: FilePath -> ModSpec -> Maybe [Ident] -> [Item] -> Compiler ()
compileModule source modspec params items = do
    logBuild $ "===> Compiling module " ++ showModSpec modspec
    enterModule source modspec (Just modspec) params
    -- Hash the parse items and store it in the module
    let hashOfItems = hashItems items
    logBuild $ "HASH: " ++ hashOfItems
    updateModule (\m -> m { itemsHash = Just hashOfItems })
    -- verboseMsg 1 $ return (intercalate "\n" $ List.map show items)
    -- XXX This means we generate LPVM code for a module before
    -- considering dependencies.  This will need to change if we
    -- really need dependency info to do initial LPVM translation, or
    -- if it's too memory-intensive to load all code to be compiled
    -- into memory at once.  Note that this does not do a proper
    -- top-down traversal, because we may not visit *all* users of a
    -- module before handling the module.  If we decide we need to do
    -- that, then we'll need to handle the full dependency
    -- relationship explicitly before doing any compilation.
    Normalise.normalise items
    stopOnError $ "preliminary processing of module " ++ showModSpec modspec
    loadImports
    stopOnError $ "handling imports for module " ++ showModSpec modspec
    mods <- exitModule -- may be empty list if module is mutually dependent
    logBuild $ "<=== finished compling module " ++ showModSpec modspec
    compileModSCC mods


extractedItemsHash :: ModSpec -> Compiler (Maybe String)
extractedItemsHash modspec = do
    storedMods <- gets extractedMods
    -- Get the force options
    opts <- gets options
    if optForce opts || optForceAll opts
        then return Nothing
        else case Map.lookup modspec storedMods of
                 Nothing -> return Nothing
                 Just m  -> return $ itemsHash m


-- | Parse the stored module bytestring in the 'objfile' and record them in the
-- compiler state for later access.
extractModules :: FilePath -> Compiler ()
extractModules objfile = do
    logBuild $ "=== Preloading Wybe-LPVM modules from " ++ objfile
    extracted <- machoLPVMSection objfile []
    if List.null extracted

        then
        Warning <!> "Unable to preload serialised LPVM from " ++ objfile

        else do
        logBuild $ ">>> Extracted Module bytestring from " ++ show objfile
        let extractedSpecs = List.map modSpec extracted
        logBuild $ "+++ Recording modules: " ++ showModSpecs extractedSpecs
        -- Add the extracted modules in the 'objectModules' Map
        exMods <- gets extractedMods
        let addMod m = Map.insert (modSpec m) m
        let exMods' = List.foldr addMod exMods extracted
        modify (\s -> s { extractedMods = exMods' })



-- | Load all serialised modules present in the LPVM section of the object
-- file.  The returned boolean flag indicates whether this was successful. A
-- False flag is returned in the scenarios:
-- o Extraction failed
-- o Extracted modules didn't contain the `required` Module.
loadModuleFromObjFile :: ModSpec -> FilePath -> Compiler Bool
loadModuleFromObjFile required objfile = do
    logBuild $ "=== ??? Trying to load LPVM Module(s) from " ++ objfile
    extracted <- machoLPVMSection objfile [required]
    if List.null extracted
        then do
        logBuild $ "xxx Failed extraction of LPVM Modules from object file "
            ++ objfile
        return False
        -- Some module was extracted
        else do
        logBuild $ "=== >>> Extracted Module bytes from " ++ show objfile
        let extractedSpecs = List.map modSpec extracted
        logBuild $ "=== >>> Found modules: " ++ showModSpecs extractedSpecs
        -- Check if the `required` modspec is in the extracted ones.
        if required `elem` extractedSpecs
            then do
            -- Collect the imports
            imports <- concat <$> mapM placeExtractedModule extracted
            logBuild $ "=== >>> Building dependencies: "
                ++ showModSpecs imports
            -- Place the super mod under compilation while
            -- dependencies are built
            case extracted of
              (superMod:_) -> do
                modify (\comp -> let ms = superMod : underCompilation comp
                                 in comp { underCompilation = ms })
                built <- or <$> mapM buildDependency imports
                _ <- reexitModule
                logBuild $ "=== <<< Extracted Module put in its place from "
                           ++ show objfile
                return True
              [] -> shouldnt "no LPVM extracted from object file"
            else
            -- The required modspec was not part of the extracted
            -- Return false and try for building
            return False



placeExtractedModule :: Module -> Compiler [ModSpec]
placeExtractedModule thisMod = do
    let modspec = modSpec thisMod
    count <- gets ((1+) . loadCount)
    modify (\comp -> comp { loadCount = count })
    let loadMod = thisMod { thisLoadNum = count
                          , minDependencyNum = count }
    updateModules $ Map.insert modspec loadMod
    -- Load the dependencies
    let thisModImpln = trustFromJust
            "==== >>> Pulling Module implementation from loaded module"
            (modImplementation loadMod)
    let imports = (keys . modImports) thisModImpln
    return imports



-- | Compile and build modules inside a folder, compacting everything into
-- one object file archive.
buildArchive :: FilePath -> Compiler ()
buildArchive arch = do
    let dir = dropExtension arch
    archiveMods <- liftIO $ List.map dropExtension <$> wybeSourcesInDir dir
    logBuild $ "Building modules to archive: " ++ show archiveMods
    build <- or <$> mapM (\m -> buildModuleIfNeeded False [m] [dir])
                    archiveMods
    let oFileOf m = joinPath [dir, m] ++ ".o"
    mapM_ (\m -> emitObjectFile [m] (oFileOf m))
          archiveMods
    makeArchive (List.map oFileOf archiveMods) arch

-------------------- Actually compiling some modules --------------------

-- |Actually compile a list of modules that form an SCC in the module
--  dependency graph.  This is called in a way that guarantees that
--  all modules on which these modules depend, other than one another,
--  will have been processed when this list of modules is reached.
--  This goes as far as producing LLVM code, but does not write it out.
compileModSCC :: [ModSpec] -> Compiler ()
compileModSCC mspecs = do
    logBuild $ "compileModSCC: [" ++ showModSpecs mspecs ++ "]"
    stopOnError $ "preliminary compilation of module(s) " ++ showModSpecs mspecs
    ----------------------------------
    -- FLATTENING
    logDump Flatten Types "FLATTENING"
    fixpointProcessSCC handleModImports mspecs
    mapM_ (completeNormalisation `inModule`) mspecs
    stopOnError $ "final normalisation of module(s) " ++ showModSpecs mspecs
    logBuild $ replicate 70 '='
    ----------------------------------
    -- TYPE CHECKING
    logBuild $ "resource and type checking module(s) "
               ++ showModSpecs mspecs ++ "..."
    mapM_ validateModExportTypes mspecs
    stopOnError $ "checking parameter type declarations in module(s) "
                  ++ showModSpecs mspecs
    -- Fixed point needed because eventually resources can bundle
    -- resources from other modules
    fixpointProcessSCC resourceCheckMod mspecs
    stopOnError $ "processing resources for module(s) " ++ showModSpecs mspecs
    -- No fixed point needed because public procs must have types declared
    mapM_ typeCheckMod mspecs
    stopOnError $ "type checking of module(s) "
                  ++ showModSpecs mspecs
    logDump Types Unbranch "TYPE CHECK"
    mapM_ (transformModuleProcs canonicaliseProcResources)  mspecs
    mapM_ (transformModuleProcs transformProcResources)  mspecs
    stopOnError $ "resource checking of module(s) "
                  ++ showModSpecs mspecs
    ----------------------------------
    -- UNBRANCHING
    mapM_ (transformModuleProcs unbranchProc)  mspecs
    stopOnError $ "handling loops and conditionals in module(s) "
                  ++ showModSpecs mspecs
    logDump Unbranch Clause "UNBRANCHING"
    -- AST manipulation before this line
    ----------------------------------
    -- CLAUSE GENERATION
    mapM_ (transformModuleProcs compileProc) mspecs
    -- LPVM from here
    stopOnError $ "generating low level code in " ++ showModSpecs mspecs
    mapM_ collectCallers mspecs
    logDump Clause Optimise "COMPILATION TO LPVM"
    ----------------------------------
    -- EXPANSION (INLINING)
    -- XXX Should optimise call graph sccs *across* each module scc
    -- to ensure inter-module dependencies are optimally optimised
    fixpointProcessSCC optimiseMod mspecs
    stopOnError $ "optimising " ++ showModSpecs mspecs
    logDump Optimise Optimise "OPTIMISATION"
    ----------------------------------
    -- ANALYSIS
    -- MODULE LEVEL ALIAS ANALYSIS - FIND FIXED POINT
    logMsg Analysis $ replicate 70 '='
    logMsg Analysis "Start ANALYSIS in Builder.hs"
    logMsg Analysis $ "mspecs: " ++ show mspecs
    logMsg Analysis $ replicate 70 '='
    fixpointProcessSCC analyseMod mspecs
    logDump Analysis Analysis "ANALYSIS"
    ----------------------------------
    -- TRANSFORM
    -- The extra pass to update prim mutate flag after performing alias analysis
    -- for all modules
    logMsg Transform $ replicate 70 '='
    logMsg Transform "Start TRANSFORM in Builder.hs"
    logMsg Transform $ "mspecs: " ++ show mspecs
    logMsg Transform $ replicate 70 '='
    mapM_ (transformModuleProcs transformProc)  mspecs
    logDump Transform Transform "TRANSFORM"

    ----------------------------------
    -- Create an LLVMAST.Module represtation
    -- mapM_ blockTransformModule (List.filter (not . isStdLib) mspecs)
    mapM_ blockTransformModule mspecs
    stopOnError $ "translating " ++ showModSpecs mspecs

    -- mods <- mapM getLoadedModule mods
    -- callgraph <- mapM (\m -> getSpecModule m
    --                        (Map.toAscList . modProcs .
    --                         fromJust . modImplementation))
    return ()

-- | Filter for avoiding the standard library modules
isStdLib :: ModSpec -> Bool
isStdLib []    = False
isStdLib (m:_) = m == "wybe"


-- |A Processor processes the specified module one iteration in a
--  context of mutual dependency among the list of modules.  It
--  produces a flag indicating that processing made some change (so a
--  fixed point has not been reached), and a list of error messages,
--  each with its associated optional source position.  The error
--  messages will only be printed after a fixed point is reached.
--  A processor is expected to find a fixed point within a single
--  module by itself.
type Processor = [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])


-- |Process a strongly connected component in the module dependency graph.
--  This code assumes that all lower sccs have already been checked.
fixpointProcessSCC :: Processor -> [ModSpec] -> Compiler ()
fixpointProcessSCC processor [modspec] = do
    (_,errors) <- processor [modspec] modspec
    -- immediate fixpoint if no mutual dependency
    mapM_ (uncurry (message Error)) errors
    return ()
fixpointProcessSCC processor scc = do        -- must find fixpoint
    (changed,errors) <-
        foldM (\(chg,errs) mod' -> do
                    (chg1,errs1) <- processor scc mod'
                    return (chg1||chg, errs1++errs))
        (False,[]) scc
    if changed
    then fixpointProcessSCC processor scc
    else mapM_ (uncurry (message Error)) errors



transformModuleProcs :: (ProcDef -> Compiler ProcDef) -> ModSpec ->
                        Compiler ()
transformModuleProcs trans thisMod = do
    logBuild $ "**** Reentering module " ++ showModSpec thisMod
    reenterModule thisMod
    -- (names, procs) <- :: StateT CompilerState IO ([Ident], [[ProcDef]])
    (names,procs) <- unzip <$>
                     getModuleImplementationField (Map.toList . modProcs)
    -- for each name we have a list of procdefs, so we must double map
    procs' <- mapM (mapM trans) procs
    updateImplementation
        (\imp -> imp { modProcs = Map.union
                                  (Map.fromList $ zip names procs')
                                  (modProcs imp) })
    _ <- reexitModule
    logBuild $ "**** Re-exiting module " ++ showModSpec thisMod
    return ()


------------------------ Loading Imports ------------------------

-- |Load all the imports of the current module.
loadImports :: Compiler ()
loadImports = do
    imports <- getModuleImplementationField (keys . modImports)
    logBuild $ "building dependencies: " ++ showModSpecs imports
    mapM_ buildDependency imports
    -- modspec <- getModuleSpec
    -- mod <- getModule id
    -- updateModules (Map.insert modspec mod)

------------------------ Handling Imports ------------------------

-- |Handle all the imports of the current module.  When called, all
-- modules imported by all the listed modules have been loaded, so we
-- can finally work out what is exported by, and what is visible in,
-- each of these modules.
handleModImports :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
handleModImports _ thisMod = do
    reenterModule thisMod
    imports <- getModuleImplementationField modImports
    kTypes <- getModuleImplementationField modKnownTypes
    kResources <- getModuleImplementationField modKnownResources
    kProcs <- getModuleImplementationField modKnownProcs
    iface <- getModuleInterface
    mapM_ (uncurry doImport) $ Map.toList imports
    kTypes' <- getModuleImplementationField modKnownTypes
    kResources' <- getModuleImplementationField modKnownResources
    kProcs' <- getModuleImplementationField modKnownProcs
    iface' <- getModuleInterface
    _ <- reexitModule
    return (kTypes/=kTypes' || kResources/=kResources' ||
            kProcs/=kProcs' || iface/=iface',[])



------------------------ Building Executable ---------------------

-- | Build the executable for the Target Module at the given
-- location.
-- All dependencies are collected as object files and linked
-- by the system 'cc' to create the target.
-- A new temporary main object file is created which has the main
-- function (LLVM) which calls the mains of the target module and the
-- imports in the correct order. The target module and imports have
-- mains defined as 'modName.main'.
buildExecutable :: ModSpec -> FilePath -> Compiler ()
buildExecutable targetMod fpath = do
    depends <- orderedDependencies targetMod
    if List.null depends || not (snd (last depends))
        then
            -- No main code in the selected module: don't build executable
            message Error
            ("No main (top-level) code in module '"
             ++ showModSpec targetMod ++ "'; not building executable")
            Nothing
        else do
            -- find dependencies (including module itself) that have a main
            logBuild $ "Dependencies: " ++ show depends
            let mainImports = fst <$> List.filter snd depends
            logBuild $ "o Modules with 'main': " ++ showModSpecs mainImports

            let mainProc = buildMain mainImports
            logBuild $ "Main proc:" ++ showProcDefs 0 [mainProc]

            enterModule fpath [] Nothing Nothing
            addImport ["wybe","command_line"] $ importSpec Nothing Private
            addImport ["wybe","io"] $ importSpec (Just ["io"]) Private
            mapM_ (\m -> addImport m $ importSpec (Just [""]) Private)
                  mainImports
            addProcDef mainProc
            mods <- exitModule
            compileModSCC mods
            logDump FinalDump FinalDump "BUILDING MAIN"
            let mainMod = case mods of
                  [m] -> m
                  _   -> shouldnt $ "non-singleton main module: "
                                    ++ showModSpecs mods

            logBuild $ "Finished building *main* module: " ++ showModSpecs mods

            -- mainMod <- newMainModule mainImports
            -- logBuild "o Built 'main' module for target: "
            -- mainModStr <- liftIO $ codeemit mainMod
            -- logEmit $ BS.unpack mainModStr
            ------------
            logBuild "o Creating temp Main module @ .../tmp/tmpMain.o"
            tempDir <- liftIO getTemporaryDirectory
            liftIO $ createDirectoryIfMissing False (tempDir ++ "wybetemp")
            let tmpMainOFile = tempDir ++ "wybetemp/" ++ "tmpMain.o"
            emitObjectFile mainMod tmpMainOFile

            ofiles <- mapM (loadObjectFile . fst) depends

            let allOFiles = tmpMainOFile:ofiles
            -----------
            logBuild "o Object Files to link: "
            logBuild $ "++ " ++ intercalate "\n++ " allOFiles
            logBuild $ "o Building Target (executable): " ++ fpath

            makeExec allOFiles fpath
            -- return allOFiles


buildMain mainImports =
    let cmdResource name = ResourceFlowSpec (ResourceSpec ["command_line"] name)
        -- Construct argumentless resourceful calls to all main procs
        bodyInner = [Unplaced $ ProcCall m "" Nothing Det True []
                    | m <- mainImports]
        -- XXX Shouldn't have to hard code assignment of phantom to io
        -- XXX Should insert assignments of initialised visible resources
        bodyCode = [lpvmCast (iVal 0) "io" phantomType,
                    move (iVal 0) (varSet "exit_code"),
                    Unplaced $ ForeignCall "C" "gc_init" [] []] ++ bodyInner
        mainBody = ProcDefSrc bodyCode
        -- Program main has argc, argv, exit_code, and io as resources
        proto = ProcProto "" []
                $ Set.fromList [cmdResource "argc" ParamIn,
                                 cmdResource "argv" ParamIn,
                                 cmdResource "exit_code" ParamOut,
                                 ResourceFlowSpec
                                     (ResourceSpec ["wybe","io"] "io")
                                     ParamOut]
    in ProcDef "" proto mainBody Nothing 0 Map.empty
       Private Det False NoSuperproc



-- | Traverse and collect a depth first dependency list from the given initial
-- Module, along with a boolean flag which indicates if that node has a defined
-- top level procedure (a main proc) i.e @[(a, True), (b, False), (c, True)]@
-- means that modules a & c have a main procedure.
-- Only those dependencies are followed which will have a corresponding object
-- file, that means no sub-mod dependencies and no standard library (for now).
orderedDependencies :: ModSpec -> Compiler [(ModSpec, Bool)]
orderedDependencies targetMod =
    List.nubBy (\(a,_) (b,_) -> a == b) <$> visit [targetMod] []
  where
    visit [] cs = return cs
    visit (m:ms) collected = do
        thisMod <- getLoadedModuleImpln m
        let procs = (keys . modProcs) thisMod
        packageFlag <- moduleIsPackage m
        let subMods = if packageFlag
                      then []
                      else (Map.elems . modSubmods) thisMod
        -- filter out std lib imports and sub-mod imports from imports
        -- since we are looking for imports which need a physical object file
        let imports =
                List.filter (\x -> notElem x subMods) $ --  && (not.isStdLib) x) $
                (keys . modImports) thisMod
        -- Check if this module 'm' has a main procedure.
        let mainExists = "" `elem` procs || "<0>" `elem` procs
        let collected' =
                case (packageFlag, mainExists) of
                    (True, _)     -> collected
                    (False, flag) -> (m, flag) : collected
        -- Don't visit any modspec already in `ms' (will be visited as it is)
        let remains = List.foldr (\x acc -> if x `elem` acc then acc else x:acc)
                ms imports
        visit remains collected'


-- | Load/Build object file for the module in the same directory
-- the module is in.
loadObjectFile :: ModSpec -> Compiler FilePath
loadObjectFile thisMod =
  do reenterModule thisMod
     dir <- getDirectory
     source <- getSource
     logBuild $ "SOURCE for " ++ showModSpec thisMod ++ " :: " ++ show source
     logBuild $ "DIR is: "  ++ show dir
     -- generating an name + extension for our object file
     let objFile = replaceExtension source $ "." ++ objectExtension
     -- Check if we need to re-emit object file
     rebuild <- objectReBuildNeeded thisMod dir
     when rebuild $ emitObjectFile thisMod objFile
     _ <- reexitModule
     return objFile


objectReBuildNeeded :: ModSpec -> FilePath -> Compiler Bool
objectReBuildNeeded thisMod dir = do
    srcOb <- moduleSources thisMod [dir]
    case srcOb of
        NoSource -> return True

        -- only object file exists, so we have loaded Module from object
        ModuleSource Nothing (Just _) _ _ -> return False

        -- only source file exists
        ModuleSource (Just _) Nothing _ _ -> return True

        ModuleSource (Just srcfile) (Just objfile) _ _ -> do
            srcDate <- (liftIO . getModificationTime) srcfile
            dstDate <- (liftIO . getModificationTime) objfile
            return $ srcDate > dstDate
        _ -> return True




-----------------------------------------------------------------------------
-- Module Source Handlers                                                  --
-----------------------------------------------------------------------------


-- | Search for different sources module `modspec` in the possible directory
-- list `possDirs`. This information is encapsulated as a ModuleSource. The
-- first found non-empty (not of constr NoSource) of ModuleSource is returned.
moduleSources :: ModSpec -> [FilePath] -> Compiler ModuleSource
moduleSources modspec possDirs = do
    let splits = List.map (`List.take` modspec) [1..length modspec]
    dirs <- mapM (\d -> mapM (sourceInDir d) splits) possDirs
    -- Return the last valid Source
    return $ (fromMaybe NoSource . List.find (/= NoSource) . reverse )
        $ concat dirs



-- | For a given module `ms`, check whether the name `ms` represents a source
-- file (.wybe), an object file (.o), an archive file (.a), or a sub-directory
-- in the given directory `d`. This information is returned as a `ModuleSource`
-- record.
sourceInDir :: FilePath -> ModSpec -> Compiler ModuleSource
sourceInDir d ms = do
    logBuild $ "Looking for source for module " ++ showModSpec ms
    let dirName = joinPath [d, showModSpec ms]
    -- Helper to convert a boolean to a Maybe [maybeFile True f == Just f]
    let maybeFile b f = if b then Just f else Nothing
    -- Different paths which can be a source for a module in the directory `d`
    let srcfile = moduleFilePath sourceExtension d ms
    let objfile = moduleFilePath objectExtension d ms
    let arfile = moduleFilePath archiveExtension d ms
    -- Flags checking
    dirExists <- liftIO $ doesDirectoryExist dirName
    srcExists <- liftIO $ doesFileExist srcfile
    objExists <- liftIO $ doesFileExist objfile
    arExists  <- liftIO $ doesFileExist arfile
    logBuild $ "Directory   " ++ dirName ++ " exists? " ++ show dirExists
    logBuild $ "Source file " ++ srcfile ++ " exists? " ++ show srcExists
    logBuild $ "Object file " ++ objfile ++ " exists? " ++ show objExists
    logBuild $ "Archive     " ++ arfile ++  " exists? " ++ show arExists
    if srcExists || objExists || arExists || dirExists
        then return
             ModuleSource
             { srcWybe = maybeFile srcExists srcfile
             , srcObj = maybeFile objExists objfile
             , srcDir = maybeFile dirExists dirName
             , srcArchive = maybeFile arExists arfile
             }
        else return NoSource


-- |The different sources that can provide implementation of a Module.
data ModuleSource = NoSource
                  | ModuleSource
                    { srcWybe    :: Maybe FilePath
                    , srcObj     :: Maybe FilePath
                    , srcDir     :: Maybe FilePath
                    , srcArchive :: Maybe FilePath
                    }
                  deriving (Eq)



-- |Pretty Printing
instance Show ModuleSource where
    show NoSource = "NO SOURCE"
    show m =
        let showPath (Just f) = f
            showPath Nothing  = "NIL"
        in "[ S: " ++ showPath (srcWybe m)
           ++ "\n| "
           ++ "O: " ++ showPath (srcObj m)
           ++ "\n| "
           ++ "D: " ++ showPath (srcDir m)
           ++ "\n| "
           ++ "A: " ++ showPath (srcArchive m)
           ++ "\n]\n"



-- |Return list of wybe module sources in the specified directory.
-- XXX This should also return subdirectory, which could also be modules.
wybeSourcesInDir :: FilePath -> IO [FilePath]
wybeSourcesInDir dir = do
    let isWybe = List.filter ((== ".wybe") . takeExtension)
    isWybe <$> listDirectory dir



------------------------ Filename Handling ------------------------

-- |The different sorts of files that could be specified on the
--  command line.
data TargetType = InterfaceFile | ObjectFile | ExecutableFile
                | UnknownFile | BitcodeFile | AssemblyFile
                | ArchiveFile
                deriving (Show,Eq)





-- |Given a file specification, return what sort of file it is.  The
--  file need not exist.
targetType :: FilePath -> TargetType
targetType filename
  | ext' == interfaceExtension  = InterfaceFile
  | ext' == objectExtension     = ObjectFile
  | ext' == executableExtension = ExecutableFile
  | ext' == bitcodeExtension    = BitcodeFile
  | ext' == assemblyExtension   = AssemblyFile
  | ext' == archiveExtension    = ArchiveFile
  | otherwise                  = UnknownFile
      where ext' = dropWhile (=='.') $ takeExtension filename


-- |Find the file path for the specified module spec relative to the
--  specified file path for the referencing module.
moduleFilePath :: String -> FilePath -> ModSpec -> FilePath
moduleFilePath extension dir spec =
    addExtension (joinPath $ splitDirectories dir ++ spec) extension




-- |Log a message, if we are logging builder activity (file-level compilation).
logBuild :: String -> Compiler ()
logBuild = logMsg Builder
