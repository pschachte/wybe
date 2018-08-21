--  File     : Builder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Jan 31 16:37:48 2012
--  Purpose  : Handles compilation at the module level.
--  Copyright: (c) 2012-2015 Peter Schachte.  All rights reserved.
--
--  The wybe compiler handles module dependencies, and builds
--  executables by itself, without the need for build tools like
--  make.  To keep compile times manageable while supporting
--  optimisation, we build bottom-up, ensuring that all a module's
--  imports are compiled before compling the module itself.  In the
--  case of circular module dependencies, each strongly-connected
--  component in the module dependency graph is compiled as a unit.
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
--  The build process makes these steps for each SCC in the module
--  dependency graph (with responsible modules):
--    o  The code is read and flattened (happens before this module is invoked)
--    o  Imported modules are loaded, building if needed (this module)
--    o  The types of exported procs are validated (Types)
--    o  Resource imports and exports are checked (Resources)
--    o  Proc argument types and modes are checked (Types)
--    o  Proc resources are checked and transformed to args (Resources)
--    o  Branches, loops, and nondeterminism are transformed away (Unbranch)
--    o  Procs are compiled to clausal form (Clause)
--    o  Procs are optimised (Optimise)
--  This is the responsibility of the compileModSCC function.

-- |Code to oversee the compilation process.
module Builder (buildTargets, compileModule) where

import           AST
import           BinaryFactory
import           Blocks                    (blockTransformModule,
                                            concatLLVMASTModules, newMainModule)
import           Callers                   (collectCallers)
import           Clause                    (compileProc)
import           Config
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import qualified Data.ByteString.Char8     as BS
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Maybe
import           Emit
import           NewParser                 (parseWybe)
import           Normalise                 (normalise)
import           ObjectInterface
import           Optimise                  (optimiseMod)
import           Options                   (LogSelection (..), Options,
                                            optForce, optForceAll, optLibDirs,
                                            optUseStd)
import           Resources                 (canonicaliseProcResources,
                                            resourceCheckMod, resourceCheckProc)
import           Scanner                   (fileTokens)
import           System.Directory
import           System.FilePath
import           Types                     (typeCheckMod,
                                            validateModExportTypes)
import           Unbranch                  (unbranchProc)

------------------------ Handling dependencies ------------------------

-- |Build the specified targets with the specified options.
buildTargets :: Options -> [FilePath] -> Compiler ()
buildTargets opts targets = do
    possDirs <- gets (optLibDirs . options)
    let useStd = optUseStd opts
    -- load library first (if option useStd is True)
    when useStd $ void (buildModuleIfNeeded False ["wybe"] possDirs)
    mapM_ (buildTarget $ optForce opts || optForceAll opts) targets
    showMessages
    logDump FinalDump FinalDump "EVERYTHING"
    logLLVMDump FinalDump FinalDump "LLVM IR"


-- |Build a single target; flag specifies to re-compile even if the
--  target is up-to-date.
buildTarget :: Bool -> FilePath -> Compiler ()
buildTarget force target = do
    Informational <!> "Building target: " ++ target
    let tType = targetType target
    case tType of
        UnknownFile ->
            Error <!> "Unknown target file type: " ++ target
        ArchiveFile -> buildArchive target
        _ -> do
            let modname = takeBaseName target
            let dir = takeDirectory target
            built <- buildModuleIfNeeded force [modname] [dir]
            stopOnError "BUILDING TARGET"
            -- Check if the module contains sub modules
            _ <- concatSubMods [modname]

            when (tType == ExecutableFile) (buildExecutable [modname] target)
            if not built && tType /= ExecutableFile
              then logBuild $ "Nothing to be done for target: " ++ target
              else
                do logBuild $ "Emitting Target: " ++ target
                   when (tType == ObjectFile) $
                       emitObjectFile [modname] target
                   when (tType == BitcodeFile) $
                       emitBitcodeFile [modname] target
                   when (tType == AssemblyFile) $
                       emitAssemblyFile [modname] target
                   whenLogging Emit $ logLLVMString [modname]


-- |Compile or load a module dependency.
buildDependency :: ModSpec -> Compiler ()
buildDependency modspec = do
    logBuild $ "Load dependency: " ++ showModSpec modspec
    force <- option optForceAll
    possDirs <- gets (optLibDirs . options)
    localDir <- getDirectory
    _ <- buildModuleIfNeeded force modspec (localDir:possDirs)
    return ()


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
            srcOb <- liftIO $ moduleSources modspec possDirs
            logBuild $ show srcOb
            case srcOb of
                NoSource -> do
                    Error <!> "Could not find module " ++
                        showModSpec modspec
                    return False

                -- only object file exists
                ModuleSource Nothing (Just objfile) Nothing _ -> do
                    loaded <- loadModuleFromObjFile modspec objfile
                    if not loaded
                        -- if extraction failed, it is uncrecoverable now
                        then do
                        let err = "Object file " ++ objfile ++
                                  " yielded no LPVM modules for " ++
                                  showModSpec modspec ++ "."
                        Error <!> "No other options to pursue."
                        Error <!> err
                        stopOnError "Building only object file"
                        return False
                        -- extraction successful, no need to build
                        else return False


                ModuleSource (Just srcfile) Nothing _ _ -> do
                    -- only source file exists
                    buildModule modspec srcfile
                    return True

                ModuleSource Nothing _ (Just dir) _ -> do
                    logBuild $ "Modname for directory: " ++ showModSpec modspec
                    buildDirectory dir modspec

                ModuleSource (Just srcfile) (Just objfile) _ _ -> do
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

                _ -> shouldnt "inconsistent file existence"






-- |Actually load and compile the module
buildModule :: ModSpec -> FilePath -> Compiler ()
buildModule mspec srcfile = do
    tokens <- (liftIO . fileTokens) srcfile
    -- let parseTree = parse tokens
    let parseTree = either (error . ("Parser Error: " ++) . show) id $
            parseWybe tokens srcfile
    compileModule srcfile mspec Nothing parseTree
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
buildDirectory dir dirmod= do
    logBuild $ "Building DIR: " ++ dir ++ ", into MODULE: "
        ++ showModSpec dirmod
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

    -- Make the directory a Module package
    enterModule dir dirmod Nothing
    updateModule (\m -> m { isPackage = True })
    -- Helper to add new import of `m` to current module
    let updateImport m = do
            addImport m (importSpec Nothing Public)
            updateImplementation $
                updateModSubmods $ Map.insert (last m) m
    -- The module package imports all wybe modules in its source dir
    mapM_ updateImport wybemods
    done <- finishModule
    liftIO $ print done
    -- Run the compilation passes on this module package to append the
    -- procs from the imports to the interface.
    -- XXX Maybe run only the import pass, as there is no module source!
    compileModSCC [dirmod]
    return built



-- |Compile a module given the parsed source file contents.
compileModule :: FilePath -> ModSpec -> Maybe [Ident] -> [Item] -> Compiler ()
compileModule source modspec params items = do
    logBuild $ "===> Compiling module " ++ showModSpec modspec
    enterModule source modspec params
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
    Normalise.normalise compileModSCC items
    stopOnError $ "preliminary processing of module " ++ showModSpec modspec
    loadImports
    stopOnError $ "handling imports for module " ++ showModSpec modspec
    _ <- gets underCompilation
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
            let superMod = head extracted
            modify (\comp -> let ms = superMod : underCompilation comp
                       in comp { underCompilation = ms })
            mapM_ buildDependency imports
            _ <- finishModule
            logBuild $ "=== <<< Extracted Module put in it's place from "
                ++ show objfile
            return True

            -- The required modspec was not part of the extracted
            -- Return false and try for building
            else
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



-- | Concatenate the LLVMAST.Module implementations of the submodules to the
-- the given super module.
concatSubMods :: ModSpec -> Compiler [ModSpec]
concatSubMods mspec = do
    someMods <- collectSubModules mspec
    unless (List.null someMods) $
        logBuild $ "### Combining descendents of " ++ showModSpec mspec
        ++ ": " ++ showModSpecs someMods
    concatLLVMASTModules mspec someMods
    return someMods


-- | Compile and build modules inside a folder, compacting everything into
-- one object file archive.
buildArchive :: FilePath -> Compiler ()
buildArchive arch = do
    let dir = dropExtension arch
    archiveMods <- liftIO $ List.map dropExtension <$> wybeSourcesInDir dir
    logBuild $ "Building modules to archive: " ++ show archiveMods
    mapM_ (\m -> buildModuleIfNeeded False [m] [dir]) archiveMods
    let oFileOf m = joinPath [dir, m] ++ ".o"
    mapM_ (\m -> emitObjectFile [m] (oFileOf m)) archiveMods
    makeArchive (List.map oFileOf archiveMods) arch

-------------------- Actually compiling some modules --------------------

-- |Actually compile a list of modules that form an SCC in the module
--  dependency graph.  This is called in a way that guarantees that
--  all modules on which this module depends, other than those on the
--  mods list, will have been processed when this list of modules is
--  reached.
compileModSCC :: [ModSpec] -> Compiler ()
compileModSCC mspecs = do
    stopOnError $ "preliminary compilation of module(s) " ++ showModSpecs mspecs
    logDump Flatten Types "FLATTENING"
    fixpointProcessSCC handleModImports mspecs
    logBuild $ replicate 70 '='
    logBuild $ "resource and type checking modules "
      ++ showModSpecs mspecs ++ "..."
    mapM_ validateModExportTypes mspecs
    stopOnError $ "checking parameter type declarations in modules " ++
      showModSpecs mspecs
    -- Fixed point needed because eventually resources can bundle
    -- resources from other modules
    fixpointProcessSCC resourceCheckMod mspecs
    stopOnError $ "processing resources for modules " ++
      showModSpecs mspecs
    -- No fixed point needed because public procs must have types declared
    mapM_ typeCheckMod mspecs
    stopOnError $ "type checking of modules " ++
      showModSpecs mspecs
    logDump Types Unbranch "TYPE CHECK"
    mapM_ (transformModuleProcs canonicaliseProcResources)  mspecs
    mapM_ (transformModuleProcs resourceCheckProc)  mspecs
    stopOnError $ "resource checking of modules " ++
      showModSpecs mspecs
    mapM_ (transformModuleProcs unbranchProc)  mspecs
    stopOnError $ "handling loops and conditionals in modules " ++
      showModSpecs mspecs
    logDump Unbranch Clause "UNBRANCHING"
    -- AST manipulation before this line
    mapM_ (transformModuleProcs compileProc)  mspecs
    -- LPVM from here
    stopOnError $ "generating low level code in " ++ showModSpecs mspecs
    mapM_ collectCallers mspecs
    logDump Clause Optimise "COMPILATION TO LPVM"
    fixpointProcessSCC optimiseMod mspecs
    stopOnError $ "optimising " ++ showModSpecs mspecs
    logDump Optimise Optimise "OPTIMISATION"

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
    _ <- finishModule
    logBuild $ "**** Exiting module " ++ showModSpec thisMod
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
    _ <- finishModule
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
    if List.null depends || not (snd (head depends))
        then
            -- No main code in the selected module: don't build executable
            message Error
            ("No main (top-level) code in module '"
             ++ showModSpec targetMod ++ "'; not building executable")
            Nothing
        else do
            -- Filter the modules for which the second element of tuple is True
            let mainImports = List.foldr (\x a -> if snd x then fst x:a else a)
                              [] depends
            logBuild $ show depends
            logBuild $ "o Modules with 'main': " ++ showModSpecs mainImports
            mainMod <- newMainModule mainImports
            logBuild "o Built 'main' module for target: "
            mainModStr <- liftIO $ codeemit mainMod
            logEmit $ BS.unpack mainModStr
            ------------
            logBuild "o Creating temp Main module @ ...../tmp/tmpMain.o"
            tempDir <- liftIO getTemporaryDirectory
            liftIO $ createDirectoryIfMissing False (tempDir ++ "wybetemp")
            let tmpMainOFile = tempDir ++ "wybetemp/" ++ "tmpMain.o"
            liftIO $ makeObjFile tmpMainOFile mainMod

            ofiles <- mapM (loadObjectFile . fst) depends
            let allOFiles = tmpMainOFile:ofiles
            -----------
            makeExec allOFiles fpath
            -- return allOFiles
            logBuild "o Object Files to link: "
            logBuild $ "++ " ++ intercalate "\n++" allOFiles
            logBuild $ "o Building Target (executable): " ++ fpath


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
                List.filter (\x -> notElem x subMods && (not.isStdLib) x) $
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
     _ <- finishModule
     return objFile


objectReBuildNeeded :: ModSpec -> FilePath -> Compiler Bool
objectReBuildNeeded thisMod dir = do
    srcOb <- liftIO $ moduleSources thisMod [dir]
    case srcOb of
        NoSource -> return True

        -- only object file exists, so we have loaded Module from object
        ModuleSource Nothing (Just _) _ _ -> return False

        -- only source file exists
        ModuleSource (Just _) Nothing _ _ -> return True

        ModuleSource (Just srcfile) (Just objfile) _ _ -> do
            srcDate <- (liftIO . getModificationTime) srcfile
            dstDate <- (liftIO . getModificationTime) objfile
            if srcDate > dstDate
              then return True
              else return False
        _ -> return True




-----------------------------------------------------------------------------
-- Module Source Handlers                                                  --
-----------------------------------------------------------------------------

-- |Find the source and/or object files for the specified module. We search
-- the library search path for the files.
{-# DEPRECATED srcObjFiles "Use moduleSources instead, more variety." #-}
srcObjFiles :: ModSpec -> [FilePath] ->
               Compiler (Maybe (FilePath,Bool,FilePath,Bool,Ident))
srcObjFiles modspec possDirs = do
    let splits = List.map (`List.take` modspec) [1..length modspec]
    dirs <- mapM (\d -> mapM (\ms -> do
                                  let srcfile = moduleFilePath sourceExtension
                                                d ms
                                  let objfile = moduleFilePath objectExtension
                                                d ms
                                  let modname = List.last ms
                                  srcExists <- (liftIO . doesFileExist) srcfile
                                  objExists <- (liftIO . doesFileExist) objfile
                                  return
                                      [ (srcfile, srcExists,
                                         objfile, objExists, modname)
                                      | srcExists || objExists
                                      ])
                        splits)
            possDirs
    let validDirs = concat $ concat dirs
    if List.null validDirs
      then return Nothing
      else return $ Just $ List.head validDirs



-- | Search for different sources module `modspec` in the possible directory
-- list `possDirs`. This information is encapsulated as a ModuleSource. The
-- first found non-empty (not of constr NoSource) of ModuleSource is returned.
moduleSources :: ModSpec -> [FilePath] -> IO ModuleSource
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
sourceInDir :: FilePath -> ModSpec -> IO ModuleSource
sourceInDir d ms = do
    let dirName = joinPath [d, showModSpec ms]
    -- Helper to convert a boolean to a Maybe [maybeFile True f == Just f]
    let maybeFile b f = if b then Just f else Nothing
    -- Different paths which can be a source for a module in the directory `d`
    let srcfile = moduleFilePath sourceExtension d ms
    let objfile = moduleFilePath objectExtension d ms
    let arfile = moduleFilePath archiveExtension d ms
    -- Flags checking
    dirExists <- doesDirectoryExist dirName
    srcExists <- doesFileExist srcfile
    objExists <- doesFileExist objfile
    arExists <- doesFileExist arfile
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
