--  File     : Builder.hs
--  Author   : Peter Schachte, Zed(Zijun) Chen.
--  Purpose  : Handles compilation at the module level.
--  Copyright: (c) 2012-2015 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
--  BEGIN MAJOR DOC
--  The wybe compiler handles module dependencies, and builds
--  executables by itself, without the need for build tools like
--  make.  The function buildTarget is responsible for determining
--  what source files need to be compiled, and for building the
--  final outputs (whether executable, object file, archive, etc.).
--
--  Wybe allows a module to be defined by a single .wybe file, or
--  by a directory containing multiple submodules.  In the latter
--  case, the directory must contain a (possibly empty) file named
--  _.wybe, which should contain all of that module's source code
--  other than its submodules.
--
--  The compiler can generate all these output formats, using the file
--  extension to work out which type of file to build:  executable,
--  object code, LLVM bitcode, LLVM assembly code, or archive file.
--  In general, it can build any type of output from either type of
--  input, but note that on unix-style systems, both directories and
--  executables have empty file extensions, so it is not possible to
--  build an executable from a directory.  Asking to build an object,
--  LLVM bitcode, or LLVM assembler file for a directory module is
--  interpreted as asking to recursively build that type of file for
--  each wybe source file and module directory within that directory.
--
--  The compiler stores its internal data structures in object files it
--  generates, and extracts that information from the object file, rather
--  than loading and compiling the source file, if the object file is
--  younger than the source file.  In the case of a directory module, the
--  nested _.o, _.bc, or _.ll file holds all of the contents of that
--  module that come from the _.wybe file.  That is, the _.wybe file is
--  compiled much like other modules, except that its module name is that
--  of the parent directory, rather than the file itself.
--
--  To keep compile times manageable while supporting optimisation,
--  we compile modules bottom-up, ensuring that all a module's
--  imports are compiled before compling the module itself. In the
--  case of circular module dependencies, each strongly-connected
--  component in the module dependency graph is compiled as a unit.
--  This is handled by the compileModule function, which includes
--  the functionality for finding the SCCs in the module dependency
--  graph.  Then each SCC is compiled by the compileModSCC function.
--
--  One shortcoming of the bottom-up approach is that some optimisations
--  depend upon the way a procedure is used, which cannot be determined
--  from the code itself.  Such analyses are best performed top-down.
--  For example, if we can determine that a structure will not be
--  referenced after the call to a procedure, that procedure may be
--  compiled to destructively modify or reuse that structure.  Our
--  approach to this is to apply multiple specialisation:  we compile
--  different versions of this code for calls that may reference
--  that argument again and calls that cannot.  Our approach is to
--  to have the bottom-up analysis produce "requests", which indicate
--  what top-down analysis results would allow more efficient
--  specialisations of the code.  This information is produced bottom-
--  up.  Then, when generating the final executable, when all the code
--  is available, we determine how beneficial each specialisation would
--  be, and select the most useful specialisations to actually produce,
--  and generate code for any that have not already been generated.
--
--  Ensuring that all compiler phases happen in the right order is
--  subtle, particularly in the face of mutual module dependencies.
--  Following are the ordering dependencies.
--
--  * Types: the types a type depends on need to have been processed
--  before the type itself, so that sizes are known. In the case of
--  recursive or mutually recursive type dependencies, all types in
--  the recursion must be implemented as pointers. Types are transformed
--  into (sub)modules, and constructors, deconstructors, accessors,
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
--  at least enough to know they have been defined before processing
--  the resource declaration.
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
--  * Nested submodules: the submodules defined within a module file,
--  including the types, must be processed as mutual dependencies of
--  that module, which they are. The nested submodules of a module
--  (including types) have access to all public and private members
--  of the parent module, and the parent has access to all public
--  members of the parent, so they are mutual dependencies.
--
--  * Directory modules:  A directory containing a file named _.wybe
--  is also a module, with all the contained .wybe files as submodules.
--  However, these submodules do not automatically import all the other
--  modules in that directory, although they can explicitly import any
--  sibling modules they need.
--
--  This means only minimal processing can be done before module
--  dependencies are noted and read in.  So we handle all these
--  dependencies by initially reading a module to be compiled and
--  handling contents as follows:
--
--  * Types:  create and enter the submodule, note that the parent
--  imports it, and process its constructors and other contents.
--
--  * Submodules:  create and enter the submodule, note that parent
--  imports it, and process its contents.
--
--  * Resources:  Record for later processing.
--
--  * Pragmas:  Record for later processing.
--
--  * Constructors and low-level (representation) types: record for
--  later type layout, code generation, etc.
--
--  * Top level statements:  add statements to the special "" proc
--  in the module, creating it if necessary.
--
--  * Procs and functions:  record them for later normalisation,
--  analysis, optimisation, etc.
--
--  Once we have finished loading the sources for the specified
--  targets, and all their dependencies, we compute the SCCs in
--  the module dependency graph.  Then for each SCC, in topographic
--  order, we call compileModSCC, which does the following:
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
--    2. Check all resource imports and exports. (Resources.hs)
--
--    3. Normalise all recorded procs in their modules, including
--       generated constructors, etc. (Normalise.hs)
--
--    4. Validate the types of exported procs. (Types.hs)
--
--    5. Check proc argument types, resolve overloading, and
--       mode check all procs. (Types.hs)
--
--    6. Check proc resources and transform them to args.
--      (Resources.hs)
--
--    7. Transform away branches, loops, and nondeterminism.
--       (Unbranch.hs)
--
--    8. Topologically sort proc call graph and identify SCCs.  For
--       each SCC, bottom-up, do the following:
--
--         1. Compile procs to clausal form (Clause)
--
--         2. Optimise procs (Optimise)
--
--  END MAJOR DOC

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- |Code to oversee the compilation process.
module Builder (buildTargets) where

import           Analysis
import           AST
import           ASTShow                   (logDump, logDumpWith)
import           Blocks                    (blockTransformModule,
                                            concatLLVMASTModules)
import           Callers                   (collectCallers)
import           Clause                    (compileProc)
import           Config
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.Graph                as Graph
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Set                  as Set
import           Data.Maybe
import           Data.Foldable
import           Emit
import           Flow                      ((|>))
import           Normalise                 (normalise, completeNormalisation, normaliseItem)
import           ObjectInterface

import           Optimise                  (optimiseMod)
import           Options                   (LogSelection (..), Options (..),
                                            optForce, optForceAll, optLibDirs, optimisationEnabled, OptFlag (MultiSpecz))
import           Parser                    (parseWybe)
import           Resources                 (resourceCheckMod,
                                            transformProcResources,
                                            canonicaliseProcResources)
import           Unique                    ( uniquenessCheckProc )
import           Scanner                   (fileTokens)
import           System.Directory
import           System.FilePath
import           System.Exit
import           System.IO.Temp            (createTempDirectory)
import           Transform                 (transformProc,
                                            generateSpeczVersionInProc,
                                            expandRequiredSpeczVersionsByMod)
import           Types                     (typeCheckModSCC,
                                            validateModExportTypes)
import           Unbranch                  (unbranchProc)
import           Util                      (sccElts, useLocalCacheFileIfPossible, (&&&))
import           Snippets
import           Text.Parsec.Error
import           BinaryFactory
import qualified Data.ByteString.Char8 as BS
import qualified LLVM.AST              as LLVMAST

import           Debug.Trace
import LastCallAnalysis (lastCallAnalyseMod)

------------------------ Handling dependencies ------------------------

-- |Build the specified targets with the specified options.
buildTargets :: [FilePath] -> Compiler ()
buildTargets targets = do
    mapM_ buildTarget targets
    showMessages
    stopOnError "building outputs"
    dumpOpt <- option optDumpOptLLVM
    let dumper = if dumpOpt then logDumpWith ((Just <$>) . extractLLVM)
                            else logDump
    dumper FinalDump FinalDump "EVERYTHING"



-- |Build a single top-level target
buildTarget :: FilePath -> Compiler ()
buildTarget target = do
    logBuild $ "===> Building target " ++ target
    -- Create a clean temp directory for each build
    sysTmpDir <- liftIO getTemporaryDirectory
    tmpDir <- liftIO $ createTempDirectory sysTmpDir "wybe"
    logBuild $ "Temp Directory: " ++ tmpDir
    updateCompiler (\st -> st { tmpDir = tmpDir })

    target <- liftIO $ makeAbsolute target
    Informational <!> "Building target: " ++ target
    let tType = targetType target
    case tType of
        UnknownFile ->
            Error <!> "Unknown target file type: " ++ target
        _ -> do
            (modspec,dir) <- liftIO $ identifyRootModule target
            logBuild $ "Base directory: " ++ dir
                       ++ " Module: " ++ showModSpec modspec
            -- target should be in the working directory, lib dir will be added
            -- later
            depGraph <- loadAllNeededModules modspec True [(dir,False)]

            -- topological sort (bottom-up)
            let orderedSCCs = List.map (\(m, ms) -> (m, m, ms)) depGraph
                                |> Graph.stronglyConnComp
                                |> List.map sccElts

            compileModBottomUpPass orderedSCCs

            logBuild $ "Emitting Target: " ++ target
            if tType == ExecutableFile
            then
                buildExecutable orderedSCCs modspec target
            else do
                multiSpeczTopDownPass orderedSCCs
                unchanged <- gets unchangedMods
                logBuild $ "These modules are unchanged: "
                           ++ showModSpecs (Set.toList unchanged)
                toDump <- filterM isRootModule $ concat orderedSCCs
                let toDump' =
                        List.filter (not . (`Set.member` unchanged)) toDump
                targets <- zip toDump' <$> mapM
                    (((modOrigin . trustFromJust "buildTarget") <$>)
                     <$> getLoadedModule)
                    toDump'
                if List.null targets
                then do
                    logBuild "===> No files to write"
                    Informational <!> "Nothing to be done for target "
                                        ++ target
                else do
                    logBuild $ "===> writing files:"
                               ++ concat [ "\n     " ++ showModSpec m
                                           ++ " -> " ++ f
                                         | (m,f) <- targets]
                    let emitMod fn ext (m,f) = do
                            Informational
                                <!> "Writing module " ++ showModSpec m
                                    ++ " to file " ++ f -<.> ext
                            fn m f
                    case tType of
                        ObjectFile -> mapM_
                            (emitMod emitObjectFile objectExtension) targets
                        BitcodeFile -> mapM_
                            (emitMod emitBitcodeFile bitcodeExtension) targets
                        AssemblyFile -> mapM_
                            (emitMod emitAssemblyFile assemblyExtension) targets
                        -- ArchiveFile -> do
                        --     mapM_ (uncurry emitObjectFile) targets
                        --     buildArchive target
                        -- LibraryDirectory ->
                        --     mapM_ (uncurry emitObjectFile) targets
                        other ->
                            nyi $ "output file type " ++ show other
                    whenLogging Emit $ logLLVMString modspec
    liftIO $ removeDirectoryRecursive tmpDir
    logBuild $ "<=== Finished building target " ++ target


-- |Search and load all needed modules starting from the given modspec, defined
-- in one of the specified absolute directories. Return a directed graph
-- representing module dependencies.
loadAllNeededModules :: ModSpec -- ^Module name
              -> Bool           -- ^Whether the provided mod is the final target
              -> [(FilePath,Bool)] -- ^Directories to look in and whether libs
              -> Compiler [(ModSpec, [ModSpec])]
loadAllNeededModules modspec isTarget possDirs = do
    opts <- gets options
    let force = optForceAll opts || (isTarget && optForce opts)
    mods <- loadModuleIfNeeded force modspec possDirs
    stopOnError $ "loading module: " ++ showModSpec modspec
    logBuild $ "Loading module " ++ showModSpec modspec
               ++ " ... got " ++ showModSpecs mods

    if List.null mods
    then return []
    else do
        -- add lib dir to the possDirs when moving from target to dependencies
        let possDirs' = if isTarget
            then possDirs ++ ((,True) <$> optLibDirs opts)
            else possDirs

        -- handle dependencies of recently loaded modules
        concatMapM (\m -> do
            imports <- getModuleImplementationField (keys . modImports)
                        `inModule` m

            logBuild $ "handle imports: " ++ showModSpecs imports ++ " in "
                        ++ showModSpec m
            depGraph <- concatMapM (\importMod ->
                loadAllNeededModules importMod False possDirs') imports

            return $ (m, imports):depGraph
            ) mods


-- | Try to load the given "modspec" and try to use the compiled version from
-- object files if possible.
loadModuleIfNeeded :: Bool          -- ^Force compilation of this module
              -> ModSpec            -- ^Module name
              -> [(FilePath,Bool)]  -- ^Directories to look in and whether libs
              -> Compiler [ModSpec] -- ^Return newly loaded module
loadModuleIfNeeded force modspec possDirs = do
    logBuild $ "Loading " ++ showModSpec modspec
               ++ " with library directories "
               ++ intercalate ", " (fst <$> possDirs)
    let clash kind1 f1 kind2 f2 =
          Error <!> kind1 ++ " " ++ f1 ++ " and "
                    ++ kind2 ++ " " ++ f2 ++ " clash. There can only be one!"

    maybemod <- getLoadedModule modspec
    logBuild $ "module " ++ showModSpec modspec ++ " is " ++
        (if isNothing maybemod then "not yet" else "already") ++
        " loaded"
    if isJust maybemod
        then return [] -- already loaded:  nothing more to do
        else do
        modSrc <- moduleSources modspec possDirs
        logBuild $ show modSrc
        case modSrc of
            _ | isTypeVar (last modspec) -> do
                Error <!>
                    "Invalid module " ++ showModSpec modspec
                    ++ " (looks like a type variable)"
                return []
            NoSource -> do
                Error <!> "Could not find source for module " ++
                            showModSpec modspec
                            ++ "\nin directories:\n    "
                            ++ intercalate "\n    " (fst <$> possDirs)
                return []

            ModuleSource Nothing (Just objfile) Nothing Nothing _ -> do
                -- only object file exists
                loadModuleFromObjFile modspec objfile

            ModuleSource (Just srcfile) Nothing Nothing Nothing False -> do
                -- only source file exists, and not a library
                maybemod <- getLoadedModule modspec
                loadModuleFromSrcFile modspec srcfile Nothing

            ModuleSource (Just srcfile) Nothing Nothing Nothing True -> do
                -- only source file exists, but it's a library
                Error <!> "No compiled code for library file " ++ srcfile
                return []

            ModuleSource (Just srcfile) (Just objfile) Nothing Nothing isLib ->
                -- both source and object files exist:  rebuild if necessary
                loadModuleFromSrcOrObj force modspec srcfile objfile
                                       Nothing isLib

            ModuleSource Nothing Nothing (Just dir) _ isLib -> do
                -- directory and _.wybe exist:  rebuild contents if necessary
                loadDirectoryModule force dir modspec isLib

            -- Error cases:
            ModuleSource (Just srcfile) Nothing (Just dir) _ _ -> do
                clash "Directory" dir "source file" srcfile
                return []

            ModuleSource (Just srcfile) Nothing _ (Just archive) _ -> do
                clash "Archive" archive "source file" srcfile
                return []

            ModuleSource Nothing (Just objfile) (Just dir) _ _ -> do
                clash "Directory" dir "object file" objfile
                return []

            ModuleSource Nothing (Just objfile) _ (Just archive) _ -> do
                clash "Archive" archive "object file" objfile
                return []

            _ -> shouldnt "inconsistent file existence"


-- |Actually load the module from source code. Return a list of loaded modules.
loadModuleFromSrcFile :: ModSpec -> FilePath -> Maybe FilePath
                      -> Compiler [ModSpec]
loadModuleFromSrcFile mspec srcfile maybeDir = do
    logBuild $ "===> Compiling source file " ++ srcfile
    Informational <!> "Loading module " ++ showModSpec mspec
                      ++ " from " ++ srcfile
    tokens <- (liftIO . fileTokens) srcfile
    let parseTree = parseWybe tokens srcfile
    mods <- either
            (\er -> errmsg
                    (Just $ errorPos er)
                    ("Syntax error: " ++ tail (dropWhile (/='\n') $ show er))
                     >> return [])
            (compileParseTree srcfile mspec)
            parseTree
    -- If we just loaded a _.wybe file, now import sources in the directory
    case maybeDir of
      Nothing -> return ()
      Just dir -> do
        reenterModule mspec
        updateModule (\m -> m { isPackage = True })

        -- Get wybe modules (in the directory) to build
        let makeMod x = mspec ++ [x]
        wybemods <- liftIO $ List.map (makeMod . dropExtension)
                    <$> wybeSourcesInDir dir

        -- Helper to add new import of `m` to current module
        let updateImport m = do
                addImport m (importSpec Nothing Public)
                updateImplementation $
                    updateModSubmods $ Map.insert (last m) m
        -- The module package imports all wybe modules in its source dir
        mapM_ updateImport wybemods
        reexitModule
        logBuild $ "Imported sources in directory module containing "
                   ++ showModSpecs wybemods
    return mods

-- |Load a module from the newer of the specified source or object file; if a
-- directory is specified and we're loading from source, also import the modules
-- in that directory.
loadModuleFromSrcOrObj :: Bool -> ModSpec -> FilePath -> FilePath
                       -> Maybe FilePath -> Bool -> Compiler [ModSpec]
loadModuleFromSrcOrObj force modspec srcfile objfile maybeDir isLib = do
    srcDate <- (liftIO . getModificationTime) srcfile
    dstDate <- (liftIO . getModificationTime) objfile
    if srcDate <= dstDate && (not force || isLib)
    then do
        loaded <- loadModuleFromObjFile modspec objfile
        -- XXX Currently we don't support fall back to source code.
        -- i.e. "loadModuleFromObjFile" never returns an empty list.
        -- We should consider to rebuild it from source code if
        -- the "wybe object file version" is too old.
        when (List.null loaded)
            (Error <!> "Wybe object file " ++ objfile
                       ++ " contained no modules")
        return loaded
    else if isLib && srcDate > dstDate
    then do
        Error <!> "Library " ++ objfile ++ " needs to be rebuilt"
        return []
    else loadModuleFromSrcFile modspec srcfile maybeDir

-- |Build a directory as the module `dirmod`.
loadDirectoryModule :: Bool -> FilePath -> ModSpec -> Bool -> Compiler [ModSpec]
loadDirectoryModule force dir dirmod isLib = do
    logBuild $ "Loading directory " ++ dir ++ " into module "
        ++ showModSpec dirmod
    -- Make the directory a Module package
    let fileBase = dir </> moduleDirectoryBasename
    modSrc <- sourceInDir fileBase isLib
    case modSrc of
            ModuleSource Nothing (Just objfile) Nothing Nothing _ -> do
                -- only object file exists
                loadModuleFromObjFile dirmod objfile

            ModuleSource (Just srcfile) Nothing Nothing Nothing False ->
                -- only source file exists
                loadModuleFromSrcFile dirmod srcfile $ Just dir

            ModuleSource (Just srcfile) Nothing Nothing Nothing True -> do
                -- only source file for library exists
                Error <!> "No compiled version of library module "
                          ++ showModSpec dirmod ++ " exists"
                return []

            ModuleSource (Just srcfile) (Just objfile) Nothing Nothing isLib' ->
                -- both source and object files exist:  rebuild if necessary
                loadModuleFromSrcOrObj force dirmod srcfile objfile
                                       (Just dir) isLib'

            otherModSrc ->
                shouldnt $ "Unexpected ModuleSource for base file " ++ fileBase


-- |Compile a file module given the parsed source file contents.
-- Return a list of all the (sub)modules contained.
compileParseTree :: FilePath -> ModSpec -> [Item] -> Compiler [ModSpec]
compileParseTree source modspec items = do
    logBuild $ "===> Compiling module parse tree: " ++ showModSpec modspec
    logBuild $ "     From file: " ++ source
    enterModule source modspec (Just modspec)
    -- Hash the parse items and store it in the module
    let hashOfItems = hashItems items
    logBuild $ "HASH: " ++ hashOfItems
    updateModule (\m -> m { itemsHash = Just hashOfItems })
    -- verboseMsg 1 $ return (intercalate "\n" $ List.map show items)
    Normalise.normalise items
    stopOnError $ "preliminary processing of module " ++ showModSpec modspec
    descendents <- descendentModules modspec
    exitModule
    logBuild $ "<=== finished normalising parse tree: "
               ++ showModSpecs descendents
    return (modspec:descendents)


-- | Load all serialised modules present in the LPVM section of the object
-- file. The returned list contains modules loaded from the object file.
loadModuleFromObjFile :: ModSpec -> FilePath -> Compiler [ModSpec]
loadModuleFromObjFile required objfile = do
    logBuild $ "===> Trying to load LPVM Module(s) from " ++ objfile
    Informational <!> "Loading module " ++ showModSpec required
                      ++ " from " ++ objfile
    extracted <- loadLPVMFromObjFile objfile [required]
    case extracted of
        Left msg -> do
            Error <!> msg
            stopOnError $ "loading of object file " ++ objfile
            return [] -- unreachable
        Right mods -> do
            logBuild $ "===> Extracted Module bytes from " ++ objfile
            logBuild $ "===> Found modules: "
                    ++ showModSpecs (List.map modSpec mods)

            -- This object should contain the required mod (parent mod) and some
            -- sub mods.
            let (requiredMods, subMods) = List.partition (\m ->
                    modSpec m == required) mods

            -- Check if the `required` modspec is in the extracted ones.
            case requiredMods of
                [requiredMod] -> do
                    -- don't need to worried about root mod, it will be overridden
                    enterModule objfile required Nothing
                    updateModule (\m -> requiredMod {modOrigin = modOrigin m})
                    -- inserts sub modules
                    mapM_ (\mod -> do
                        let spec = modSpec mod
                        enterModule objfile spec Nothing
                        updateModule (\m -> mod {modOrigin = modOrigin m})
                        exitModule
                        ) subMods
                    exitModule
                    -- mark mods as unchanged
                    updateCompiler (\st ->
                        let unchanged = List.map modSpec mods
                                |> Set.fromList |> Set.union (unchangedMods st)
                        in st {unchangedMods = unchanged})
                    let loaded = List.map modSpec mods
                    when (List.null loaded) $ do
                        -- if extraction failed, it is uncrecoverable now
                        let err = "Object file " ++ objfile ++
                                    " yielded no LPVM modules for " ++
                                    showModSpec required ++ "."
                        Error <!> "No other options to pursue."
                        Error <!> err
                    return loaded
                _ ->
                    -- The required modspec was not part of the extracted, abort.
                    shouldnt $ "Invalid Wybe object file"
                            ++ "(can't find matching module)" ++ objfile


-- |Extract all the LPVM modules from the specified object file.
loadLPVMFromObjFile :: FilePath -> [ModSpec]
                    -> Compiler (Either String [Module])
loadLPVMFromObjFile objFile required = do
    tmpDir <- gets tmpDir
    objFile' <- liftIO $ useLocalCacheFileIfPossible objFile
    logBuild $ "Cache (or not) file to load: " ++ objFile'
    unless (objFile == objFile')
        (logBuild $ "find local cache file, use it instead: " ++ objFile')
    result <- liftIO $ extractLPVMData tmpDir objFile'
    case result of
        Left err -> return $ Left $ "Error decoding object file data: " ++ err
        Right modBS -> do
            logBuild "No error decoding object file data."
            logBuild $ "Extracted LPVM data"
            (List.map (\m -> m { modOrigin = objFile } ) <$>)
              <$> decodeModule required modBS


-- XXX This needs to be rewritten:
-- -- | Compile and build modules inside a folder, compacting everything into
-- -- one object file archive.
-- buildArchive :: FilePath -> Compiler ()
-- buildArchive arch = do
--     let dir = dropExtension arch
--     archiveMods <- liftIO $ List.map dropExtension <$> wybeSourcesInDir dir
--     logBuild $ "Building modules to archive: " ++ show archiveMods
--     let oFileOf m = joinPath [dir, m] <.> objectExtension
--     mapM_ (\m -> emitObjectFile [m] (oFileOf m)) archiveMods
--     makeArchive (List.map oFileOf archiveMods) arch

-------------------- Actually compiling some modules --------------------

-- |Compile each SCC in a bottom-up order.
compileModBottomUpPass :: [[ModSpec]] -> Compiler ()
compileModBottomUpPass orderedSCCs = do
    logBuild " ===> Start bottom-up pass"
    mapM_ (\scc -> do
        needed <- isCompileNeeded scc
        if needed
        then do
            logBuild $ " ---- Running on SCC: " ++ showModSpecs scc
            prepareToCompileModSCC scc
            stopOnError "reload outdated module"
            compileModSCC scc
        else
            logBuild $ " ---- Skip SCC: " ++ showModSpecs scc
        ) orderedSCCs
    logBuild " <=== Complete bottom-up pass"


-- |Return whether the given SCC is needed for compilation.
-- We consider a SCC can be skipped for compilation if and only if:
--   1. All mods in the SCC are already compiled, and
--   2. For all imports of mods in the SCC, the recorded interface hash matches
--      the current interface hash.
isCompileNeeded :: [ModSpec] -> Compiler Bool
isCompileNeeded modSCC = do
    unchanged <- gets unchangedMods
    if List.all (`Set.member` unchanged) modSCC
    then do
        upToDate <- andM $ List.map (\m -> do
            imports <- getModuleImplementationField modImports `inModule` m
            andM $ List.map (\(m', (_, hash)) ->
                if isNothing hash
                then do
                    logBuild $ "mod: " ++ showModSpec m ++ " imports: "
                        ++ showModSpec m' ++ " with empty hash"
                    return False
                else do
                    hash' <- getModule modInterfaceHash `inModule` m'
                    if hash' == hash
                    then
                        return True
                    else do
                        logBuild $ "mod: " ++ showModSpec m ++ " imports: "
                            ++ showModSpec m' ++ " with hash: " ++ show hash
                            ++ " but the current hash is: " ++ show hash'
                        return False
                ) (Map.toList imports)
            ) modSCC
        return $ not upToDate
    else do
        logBuild "SCC contains uncompiled module"
        return True -- has un-compiled module


-- |Make sure all mods in the given SCC are un-compiled. For compiled module,
-- reload it from source code.
prepareToCompileModSCC :: [ModSpec] -> Compiler ()
prepareToCompileModSCC modSCC = do
    unchanged <- gets unchangedMods
    let compiledMods = List.filter (`Set.member` unchanged) modSCC
    if List.null compiledMods
    then
        return ()
    else do
        logBuild $ "Mods that need reload: " ++ showModSpecs compiledMods
        -- Package (directory mod) can't be loaded from object file, don't need
        -- to worry about it.
        modsGroupByRoot <- foldM (\modsGroupByRoot m -> do
            reenterModule m
            obj <- getOrigin
            src <- getSource
            rootMod <- getModule modRootModSpec
            reexitModule
            case rootMod of
                Just rootMod -> modsGroupByRoot
                                |> Map.alter (\case
                                    Just ms -> Just (m:ms)
                                    Nothing -> Just [m]) (rootMod, obj, src)
                                |> return
                _            -> return modsGroupByRoot
            ) Map.empty compiledMods

        -- clean up compiled mods for reloading
        updateCompiler (\st ->
                let mods = modules st
                        |> Map.filterWithKey (\k _ -> k `notElem` compiledMods)
                in
                let unchanged = unchangedMods st
                        |> Set.filter (`notElem` compiledMods)
                in
                st { modules = mods, unchangedMods = unchanged }
            )

        logBuild $ "ModsGroupByRoot: " ++ show modsGroupByRoot

        -- reload
        mapM_ (\((rootM, obj, src), ms) -> do
            logBuild $ "Reload root mod: " ++ showModSpec rootM ++ " contains: "
                ++ showModSpecs ms ++ " from: " ++ show src
            exist <- liftIO $ doesFileExist src
            if exist
            then do
                srcDate <- (liftIO . getModificationTime) src
                dstDate <- (liftIO . getModificationTime) obj
                -- XXX we should consider checking "itemsHash" after checking
                -- the last modification time. Same in "loadModuleIfNeeded".
                if srcDate > dstDate
                then
                    Error <!> "Source: " ++ src ++ " has been changed during "
                              ++ "the compilation."
                else
                    loadModuleFromSrcFile rootM src Nothing >> return ()
            else Error <!>
                    "Unable to find corresponding source for object: " ++ obj
                    ++ ". Failed to reload modules:" ++ showModSpecs ms
            ) (Map.toList modsGroupByRoot)


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
    fixpointProcessSCC handleModImports mspecs
    completeNormalisation mspecs
    -- repeat this to handle imports of procs generated by completeNormalisation
    fixpointProcessSCC handleModImports mspecs
    stopOnError $ "final normalisation of module(s) " ++ showModSpecs mspecs
    logDump Flatten Types "FLATTENING"
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
    mapM_ (transformModuleProcs canonicaliseProcResources)  mspecs
    stopOnError $ "processing resources for module(s) " ++ showModSpecs mspecs
    typeCheckModSCC mspecs
    stopOnError $ "type checking of module(s) "
                  ++ showModSpecs mspecs
    logDump Types Unbranch "TYPE CHECK"
    mapM_ (transformModuleProcs uniquenessCheckProc)  mspecs
    stopOnError $ "uniqueness checking of module(s) "
                  ++ showModSpecs mspecs
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
    -- LAST CALL ANALYSIS
    -- Identifies situations in which we can turn a last-call into a tail-call
    logMsg LastCallAnalysis  $ replicate 70 '='
    logMsg LastCallAnalysis  "Start LAST CALL ANALYSIS in Builder.hs"
    logMsg LastCallAnalysis  $ "mspecs: " ++ show mspecs
    logMsg LastCallAnalysis  $ replicate 70 '='
    mapM_ lastCallAnalyseMod mspecs
    logDump LastCallAnalysis LastCallAnalysis  "LAST CALL ANALYSIS"

    -- mods <- mapM getLoadedModule mods
    -- callgraph <- mapM (\m -> getSpecModule m
    --                        (Map.toAscList . modProcs .
    --                         fromJust . modImplementation))
    mapM_ updateInterfaceHash mspecs
    mapM_ updateImportsInterfaceHash mspecs


-- Update the interface hash of the given module to match the current mod
-- implementation.
updateInterfaceHash :: ModSpec -> Compiler ()
updateInterfaceHash mspec = do
    reenterModule mspec
    -- update the mod interface based on the current implementation
    -- XXX For now, mod interface is not used during the "compileModSCC", so
    --     we can update it at the end. But that is not desired, plz find
    --     comments of "ModuleInterface" in AST.hs for more details.
    impl <- trustFromJustM ("unimplemented module " ++ showModSpec mspec)
            getModuleImplementation
    interface <- getModuleInterface
    let procs = Map.map (Map.mapWithKey (\(ProcSpec mod procName procID _) _ ->
            if mod == mspec
            then
                let p = (modProcs impl ! procName) !! procID in
                let proto = procImplnProto $ procImpln p in
                let body = procImplnBody $ procImpln p in
                let analysis = procImplnAnalysis $ procImpln p in
                if procInline p
                then InlineProc proto body
                else NormalProc proto analysis
            else
                ReexportedProc
            )) (pubProcs interface)
    updateModInterface (\i -> i {pubProcs = procs})
    -- re-compute the hash
    interface' <- getModuleInterface
    let hash = hashInterface interface'
    updateModule (\m -> m {modInterfaceHash = hash})
    reexitModule


-- Update the recorded interface hashes of all imports in the given module to
-- the current values.
updateImportsInterfaceHash :: ModSpec -> Compiler ()
updateImportsInterfaceHash mspec = do
    reenterModule mspec
    updateModImplementationM (\imp -> do
        let importsList = modImports imp |> Map.toAscList
        importsList' <- mapM (\(m, (spec, _)) -> do
            hash <- getModule modInterfaceHash `inModule` m
            return (m, (spec, hash))
            ) importsList
        let imports = Map.fromDistinctAscList importsList'
        return $ imp {modImports = imports})
    reexitModule


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
fixpointProcessSCC processor scc = do        -- must find fixpoint
    (changed,errors) <-
        foldM (\(chg,errs) mod' -> do
                    (chg1,errs1) <- processor scc mod'
                    return (chg1||chg, errs1++errs))
        (False,[]) scc
    if changed
    then fixpointProcessSCC processor scc
    else mapM_ (uncurry (message Error)) errors



------------------------ Handling Imports ------------------------

-- |Handle all the imports of the current module.  When called, all
-- modules imported by all the listed modules have been loaded, so we
-- can finally work out what is exported by, and what is visible in,
-- each of these modules.
handleModImports :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
handleModImports _ thisMod = do
    reenterModule thisMod
    imports     <- getModuleImplementationField modImports
    nestedIn    <- getModuleImplementationField modNestedIn
    kTypes      <- getModuleImplementationField modKnownTypes
    kResources  <- getModuleImplementationField modKnownResources
    kProcs      <- getModuleImplementationField modKnownProcs
    iface       <- getModuleInterface
    mapM_ (uncurry doImport) $ Map.toList imports
    maybe (return ()) importFromSupermodule nestedIn
    kTypes'     <- getModuleImplementationField modKnownTypes
    kResources' <- getModuleImplementationField modKnownResources
    kProcs'     <- getModuleImplementationField modKnownProcs
    iface'      <- getModuleInterface
    reexitModule
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
buildExecutable :: [[ModSpec]] -> ModSpec -> FilePath -> Compiler ()
buildExecutable orderedSCCs targetMod target = do
    possDirs <- gets $ ((,True) <$>) . optLibDirs . options
    loadModuleIfNeeded False cmdLineModSpec possDirs
    let privateImport = importSpec Nothing Private
    addImport cmdLineModSpec privateImport `inModule` targetMod
    dependsUnsorted <- orderedDependencies targetMod
    let topoMap = sccTopoMap orderedSCCs
        depends = sortOn (modTopoOrder topoMap . fst) dependsUnsorted
    if List.null depends || not (snd (last depends))
        then
            -- No main code in the selected module: don't build executable
            Error <!>
            ("No main (top-level) code in module '"
             ++ showModSpec targetMod ++ "'; not building executable")
        else do
            -- find dependencies (including module itself) that have a main
            logBuild $ "Dependencies: " ++ show depends
            let mainImports = fst <$> List.filter snd depends
            -- We need to insert
            logBuild $ "o Modules with 'main': " ++ showModSpecs mainImports

            let mainMod = []
            enterModule target mainMod Nothing
            addImport ["wybe"] privateImport
            addImport cmdLineModSpec privateImport
            -- Import all dependencies of the target mod
            mapM_ (\m -> addImport m $ importSpec Nothing Private)
                  (fst <$> depends)
            importFromSupermodule targetMod
            mainProc <- buildMain mainImports
            logBuild $ "Main proc:" ++ show mainProc
            normaliseItem mainProc
            exitModule
            compileModSCC [mainMod]
            logDump FinalDump FinalDump "BUILDING MAIN"

            logBuild $
                    "Finished building *main* module: " ++ showModSpec mainMod
            logBuild "o Creating temp Main module @ .../tmp/tmpMain.o"
            tmpDir <- gets tmpDir
            let tmpMainOFile = tmpDir </> "tmpMain.o"
            -- main module only contain a single proc that doesn't have a specz
            -- version, we build it first.
            blockTransformModule mainMod
            stopOnError $ "translating " ++ showModSpecs [mainMod]
            emitObjectFile mainMod tmpMainOFile

            multiSpeczTopDownPass (orderedSCCs ++ [mainMod])

            ofiles <- emitObjectFilesIfNeeded depends
            depMods <- mapMaybeM (getLoadedModule . fst) depends
            let foreigns = foreignDependencies depMods
            let allOFiles = tmpMainOFile:(ofiles ++ foreigns)

            logBuild "o Object Files to link: "
            logBuild $ "++ " ++ intercalate "\n++ " allOFiles
            logBuild $ "o Building Target (executable): " ++ target

            makeExec allOFiles target


-- |Visit all dependencies that have a corresponding object file, emit object
-- files that does not exist or are outdated.
emitObjectFilesIfNeeded :: [(ModSpec, Bool)] -> Compiler [FilePath]
emitObjectFilesIfNeeded depends = do
    unchangedSet <- gets unchangedMods
    logBuild $ "Unchanged Set: " ++ show unchangedSet
    mapM (\(m, _) -> do
        reenterModule m
        -- package (directory mod) won't be included in "depends", no need to
        -- handle it
        subMods <- Map.elems <$> getModuleImplementationField modSubmods
        source <- getSource
        let objFile = source -<.> objectExtension
        logBuild $ "Ready to emit module: " ++ showModSpec m ++
                    " with sub-modules: " ++ showModSpecs subMods
        let changed = List.any (`Set.notMember` unchangedSet) (m:subMods)
        if changed
        then do
            logBuild $ "emitting to: " ++ objFile
            emitObjectFile m objFile
        else
            logBuild $ "unchanged, skip it: " ++ objFile
        reexitModule

        -- we might use the local cache file instead of the actual file
        -- check and overwrite the file name
        liftIO $ useLocalCacheFileIfPossible objFile
        ) depends


-- | Return the list of foreign object file dependencies, each with the
-- appropriate directory attached, followed by the foreign library dependencies.
foreignDependencies :: [Module] -> [String]
foreignDependencies mods =
    let dirFns = (</>) . takeDirectory . modOrigin <$> mods
        implns = modImplementation <$> mods
        foreignOs = Set.toList $ Set.unions
                    $ zipWith Set.map dirFns
                    $ maybe Set.empty modForeignObjects <$> implns
        foreignLibs = Set.toList
                      $ Set.unions
                      $ maybe Set.empty modForeignLibs <$> implns
    in foreignOs ++ foreignLibs


-- |Generate a main function by piecing together calls to the main procs of all
-- the module dependencies that have them.
buildMain :: [ModSpec] -> Compiler Item
buildMain mainImports = do
    logBuild "Generating main executable code"
    let cmdResource name = ResourceFlowSpec (ResourceSpec cmdLineModSpec name)
    let mainRes = Set.fromList [cmdResource "argc" ParamIn,
                                cmdResource "argv" ParamIn,
                                cmdResource "exit_code" ParamOut]
    initRes <- Set.filter (`Set.notMember` Set.map resourceFlowRes mainRes)
             . Set.unions . (keysSet <$>)
            <$> mapM (initialisedResources `inModule`) mainImports
    let detism = setDetism Terminal
                 $ setImpurity Impure defaultProcModifiers
    -- Program main has argc, argv, and exit_code as resources
    let proto = ProcProto "" [] mainRes
    let mainBody =
          [ Unplaced $
            UseResources (Set.toList initRes) Nothing $
            -- Construct argumentless resourceful calls to all main procs
              [Unplaced $ ProcCall (First m "" Nothing) Det True []
              | m <- mainImports]
              ++ [Unplaced $ ForeignCall "c" "exit" ["semipure","terminal"]
                             [Unplaced $ intVarGet "exit_code"]]]
    -- return $ ProcDef "" proto mainBody Nothing 0 0 Map.empty
    --          Private Det MayInline Pure NoSuperproc
    return $ ProcDecl Private detism proto mainBody Nothing


-- | Traverse and collect a depth first dependency list from the given initial
-- Module, along with a boolean flag which indicates if that node has a defined
-- top level procedure (a main proc), e.g., @[(a, True), (b, False), (c, True)]@
-- means that modules a & c have a main procedure.
-- Only those dependencies are followed which will have a corresponding object
-- file, that means no sub-mod dependencies and no standard library (for now).
-- XXX re-implement this using "orderedSCCs"
orderedDependencies :: ModSpec -> Compiler [(ModSpec, Bool)]
orderedDependencies targetMod =
    List.nubBy (\(a,_) (b,_) -> a == b) <$> visit [targetMod] []
  where
    visit [] cs = return cs
    visit (m:ms) collected = do
        logBuild $ "Visiting: " ++ showModSpecs (m:ms)
        thisMod <- getLoadedModuleImpln m
        let procs = (keys . modProcs) thisMod
        packageFlag <- moduleIsPackage m
        let subMods = if packageFlag
                      then []
                      else (Map.elems . modSubmods) thisMod
        -- filter out std lib imports and sub-mod imports from imports
        -- since we are looking for imports which need a physical object file
        let imports =
                List.filter (`notElem` subMods) $ --  && (not.isStdLib) x) $
                (keys . modImports) thisMod
        -- Check if this module 'm' has a main procedure.
        let mainExists = "" `elem` procs || "<0>" `elem` procs
        let collected' =
                case (packageFlag, mainExists) of
                    (True, _)     -> collected
                    (False, flag) -> (m, flag) : collected
        -- Don't visit any modspec already in `ms' (will be visited as it is)
        -- Don't visit any modspec already in `collected''
        let remains =
                List.foldr (\x acc -> if x `elem` acc then acc else x:acc)
                        ms imports
                |> List.filter (\x -> x `notElem` List.map fst collected')
        visit remains collected'

-- | Maps the topological order of a non-std and non-cmdline modspec
type TopoMap = Map ModSpec Integer

-- | Generate a mapping from a non-std lib and non-cmdline modspec
--   to its topological order
sccTopoMap :: [[ModSpec]] -> TopoMap
sccTopoMap orderedSCCs =
    Map.fromList
        $ concat
        $ zipWith (\order scc -> (,order) <$> scc) [0..]
        $ List.filter
            (not . all isStdLib &&& not . all (==cmdLineModSpec))
            orderedSCCs

-- | Takes in a topomap (defined in sccTopoMap) and a modspec, then return the
--   modspec's topological order
modTopoOrder :: TopoMap -> ModSpec -> Integer
modTopoOrder topoMap modSpec =
    case Map.lookup modSpec topoMap of
        Just order -> order
        Nothing -> if isStdLib modSpec then -2 else -1

-----------------------------------------------------------------------------
-- Top-Down Pass for Multiple Specialization                               --
-----------------------------------------------------------------------------

-- | Run a top-down pass starting form the given module.
-- It will find all required specialized versions and generate them.
-- It also calls "blockTransformModule" to transform LPVM code to LLVM code.
-- XXX handle read-only object file such as stdlib "wybe". We can't fill in
-- specz versions like this. Currently it's ok because it does not have a specz
-- version. Tt's probably a good idea to only revise .o files in the current
-- directory, and handle any object files in a different directory the same way
-- we handle stdlib.
multiSpeczTopDownPass :: [[ModSpec]] -> Compiler ()
multiSpeczTopDownPass orderedSCCs = do
    logBuild " ===> Start top-down pass"
    mapM_ (\scc -> do
        doMultiSpecz <- gets (optimisationEnabled MultiSpecz . options)
        when doMultiSpecz $ do
            logBuild $ " ---- Running on: " ++ showModSpecs scc
            -- collecting all required spec versions
            fixpointProcessSCC expandRequiredSpeczVersionsByMod scc

            -- generating required specz versions
            mapM_ (transformModuleProcs generateSpeczVersionInProc) scc

        -- transform lpvm code to llvm code.
        unchanged <- gets unchangedMods
        -- XXX we can do a bit better by handling modules that has llvm code
        -- with some new specz versions.
        let scc' = List.filter (`Set.notMember` unchanged) scc
        mapM_ blockTransformModule scc'
        stopOnError $ "translating: " ++ showModSpecs scc'
        ) (List.reverse orderedSCCs)
    logBuild " <=== Complete top-down pass"


-----------------------------------------------------------------------------
-- Module Source Handlers                                                  --
-----------------------------------------------------------------------------


-- | Search for different sources module `modspec` in the possible directory
-- list `possDirs`. This information is encapsulated as a ModuleSource. The
-- first found non-empty (not of constr NoSource) of ModuleSource is returned.
moduleSources :: ModSpec -> [(FilePath,Bool)] -> Compiler ModuleSource
moduleSources modspec possDirs = do
    logBuild $ "Finding location of module " ++ showModSpec modspec
               ++ " in directories " ++ intercalate ", " (fst <$> possDirs)
    dirs <- mapM (\(d,l) -> sourceInDir (joinPath (d:modspec)) l) possDirs
    -- Return the last valid Source
    return $ (fromMaybe NoSource . List.find (/= NoSource)) dirs



-- | For a given module `ms`, check whether the name `ms` represents a source
-- file (.wybe), an object file (.o), an archive file (.a), or a sub-directory
-- in the given directory `d`. This information is returned as a `ModuleSource`
-- record.
sourceInDir :: FilePath -> Bool -> Compiler ModuleSource
sourceInDir baseName isLib = do
    logBuild $ "Looking for source of " ++ baseName
    -- Helper to convert a boolean to a Maybe [maybeFile True f == Just f]
    let maybeFile b f = if b then Just f else Nothing
    -- Different paths which can be a source for a module in the directory `d`
    let srcfile = baseName <.> sourceExtension
    let objfile = baseName <.> objectExtension
    let arfile  = baseName <.> archiveExtension
    -- Flags checking
    dirExists <- liftIO $ isModuleDirectory baseName
    srcExists <- liftIO $ doesFileExist srcfile
    objExists <- liftIO $ doesFileExist objfile
    arExists  <- liftIO $ doesFileExist arfile
    logBuild $ "Directory   " ++ baseName ++ " exists? " ++ show dirExists
    logBuild $ "Source file " ++ srcfile ++ " exists? " ++ show srcExists
    logBuild $ "Object file " ++ objfile ++ " exists? " ++ show objExists
    logBuild $ "Archive     " ++ arfile ++  " exists? " ++ show arExists
    return $ if srcExists || objExists || arExists || dirExists
        then ModuleSource
             { srcWybe = maybeFile srcExists srcfile
             , srcObj = maybeFile objExists objfile
             , srcDir = maybeFile dirExists baseName
             , srcArchive = maybeFile arExists arfile
             , srcIsLib = isLib
             }
        else NoSource


-- |The different sources that can provide implementation of a Module.
data ModuleSource = NoSource
                  | ModuleSource
                    { srcWybe    :: Maybe FilePath
                    , srcObj     :: Maybe FilePath
                    , srcDir     :: Maybe FilePath
                    , srcArchive :: Maybe FilePath
                    , srcIsLib   :: Bool
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
           ++ "\n| "
           ++ "L: " ++ show (srcIsLib m)
           ++ "\n]\n"


------------------------ Filename Handling ------------------------

-- |Given a filename, find its module and the parent directory of its root
-- module.
identifyRootModule :: FilePath -> IO (ModSpec,FilePath)
identifyRootModule target = do
    buildDirModSpec (takeDirectory target) [takeBaseName target]


-- |Given a directory, build up its module spec as a prefix to the specified
-- ModSpec.  This climbs the directory hierarchy looking for the root of the
-- Wybe module hierarchy.  A directory containing a file named `_.wybe` is
-- considered to be a Wybe module, with each `.wybe` file and each Wybe module
-- directory its submodules.
buildDirModSpec :: FilePath -> ModSpec -> IO (ModSpec,FilePath)
buildDirModSpec path modspec = do
    isMod <- doesFileExist $ path </> moduleDirectoryBasename <.> sourceExtension
    if isMod
        then buildDirModSpec (takeDirectory path) (takeFileName path:modspec)
        else return (modspec,path)


-- |Return list of wybe module sources in the specified directory.  This
-- includes .wybe files (other than the special _.wybe  file) plus and Wybe
-- module directories.
wybeSourcesInDir :: FilePath -> IO [FilePath]
wybeSourcesInDir dir =
    listDirectory dir >>=
    filterM (\f -> do
        isDirMod <- isModuleDirectory f
        let isSource = takeExtension f == ('.':sourceExtension)
        let notModFile = takeBaseName f /= moduleDirectoryBasename
        return $ isSource && notModFile || isDirMod)


-- |Is the specified file path a Wybe module directory?
isModuleDirectory :: FilePath -> IO Bool
isModuleDirectory path = do
    let dirFileBase = path </> moduleDirectoryBasename
    isDirModSrc <- doesFileExist $ dirFileBase <.> sourceExtension
    isDirModObj <- doesFileExist $ dirFileBase <.> objectExtension
    return $ isDirModSrc || isDirModObj


-- |The different sorts of files that could be specified on the
--  command line.
data TargetType = ObjectFile | BitcodeFile | AssemblyFile
                | ArchiveFile | ExecutableFile | UnknownFile
                deriving (Show,Eq)


-- |Given a file specification, return what sort of file it is.  The
--  file need not exist.
targetType :: FilePath -> TargetType
targetType filename
  | ext == objectExtension     = ObjectFile
  | ext == bitcodeExtension    = BitcodeFile
  | ext == assemblyExtension   = AssemblyFile
  | ext == archiveExtension    = ArchiveFile
  | ext == executableExtension = ExecutableFile
  | otherwise                   = UnknownFile
      where ext = dropWhile (=='.') $ takeExtension filename


------------------------ Logging ------------------------

-- |Log a message, if we are logging builder activity (file-level compilation).
logBuild :: String -> Compiler ()
logBuild = logMsg Builder
