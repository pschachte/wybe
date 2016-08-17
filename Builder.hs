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
--    o  Proc argument types are checked (Types)
--    o  Proc resources are checked and transformed to args (Resources)
--    o  Branches and loops are transformed away (Unbranch)
--    o  Procs are compiled to clausal form (Clause)
--    o  Procs are optimised (Optimise)
--  This is the responsibility of the compileModSCC function.

-- |Code to oversee the compilation process.
module Builder (buildTargets, compileModule) where

import           AST
import           Blocks                    (blockTransformModule,
                                            concatLLVMASTModules, newMainModule)
import           Callers                   (collectCallers)
import           Clause                    (compileProc)
import           Config
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.List                 as List
import           Data.Map                  as Map
import           Data.Maybe
import           Emit
import           Normalise                 (normalise)
import           ObjectInterface
import           Optimise                  (optimiseMod)
import           Options                   (LogSelection (..), Options,
                                            optForce, optForceAll, optLibDirs,
                                            optUseStd)
import           Parser                    (parse)
import           Resources                 (resourceCheckMod, resourceCheckProc)
import           Scanner                   (fileTokens)
import           System.Directory
import           System.FilePath
import           Types                     (typeCheckMod,
                                            validateModExportTypes)
import           Unbranch                  (unbranchProc)
import BinaryFactory

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
    let tType = targetType target
    case tType of
        UnknownFile -> message Error
            ("Unknown target file type " ++ target) Nothing
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
                do when (tType == ObjectFile) $
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
    localDir <- getModule modDirectory
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
            srcOb <- srcObjFiles modspec possDirs
            case srcOb of
                Nothing -> do
                    message Error ("Could not find module " ++
                                   showModSpec modspec) Nothing
                    return False
                Just (_,False,objfile,True,_) -> do
                    -- only object file exists
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
                Just (srcfile,True,objfile,False,modname) -> do
                    -- only source file exists
                    buildModule modname objfile srcfile
                    return True
                Just (srcfile,True,objfile,True,modname) -> do
                    srcDate <- (liftIO . getModificationTime) srcfile
                    dstDate <- (liftIO . getModificationTime) objfile
                    if force || srcDate > dstDate
                      then do
                        unless force (extractModules objfile)
                        buildModule modname objfile srcfile
                        return True
                      else do
                        loaded <- loadModuleFromObjFile modspec objfile
                        unless loaded $ do
                            -- Loading failed, fallback on source building
                            logBuild $ "Falling back on building " ++
                                showModSpec modspec
                            buildModule modname objfile srcfile
                        return $ not loaded
                Just (_,False,_,False,_) ->
                    shouldnt "inconsistent file existence"


-- |Find the source and/or object files for the specified module. We search
-- the library search path for the files.
srcObjFiles :: ModSpec -> [FilePath] ->
               Compiler (Maybe (FilePath,Bool,FilePath,Bool,Ident))
srcObjFiles modspec possDirs = do
    let splits = List.map (`take` modspec) [1..length modspec]
    dirs <- mapM (\d -> mapM (\ms -> do
                                  let srcfile = moduleFilePath sourceExtension
                                                d ms
                                  let objfile = moduleFilePath objectExtension
                                                d ms
                                  let modname = List.last ms
                                  srcExists <- (liftIO . doesFileExist) srcfile
                                  objExists <- (liftIO . doesFileExist) objfile
                                  return $ if srcExists || objExists
                                           then [(srcfile,srcExists,
                                                  objfile,objExists,modname)]
                                           else [])
                         splits)
            possDirs
    let validDirs = concat $ concat dirs
    if List.null validDirs
      then return Nothing
      else return $ Just $ List.head validDirs


-- |Actually load and compile the module
buildModule :: Ident -> FilePath -> FilePath -> Compiler ()
buildModule modname objfile srcfile = do
    tokens <- (liftIO . fileTokens) srcfile
    let parseTree = parse tokens
    let dir = takeDirectory objfile
    let mspec = [modname]
    let currHash = hashItems parseTree
    extractedHash <- extractedItemsHash mspec
    case extractedHash of
        Nothing -> compileModule dir mspec Nothing parseTree
        Just otherHash ->
            if currHash == otherHash
            then do
                logBuild $ "... Hash for module " ++ showModSpec mspec ++
                    " matches the old hash."
                loadModuleFromObjFile mspec objfile
                return () 
            else compileModule dir mspec Nothing parseTree
    


-- |Compile a module given the parsed source file contents.
compileModule :: FilePath -> ModSpec -> Maybe [Ident] -> [Item] -> Compiler ()
compileModule dir modspec params items = do
    logBuild $ "===> Compiling module " ++ showModSpec modspec
    enterModule dir modspec params
    -- Hash the parse items and store it in the module
    let hashOfItems = hashItems items
    -- logBuild $ "HASH: " ++ hashOfItems
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
    underComp <- gets underCompilation
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
                 Just m -> return $ itemsHash m


-- | Parse the stored module bytestring in the 'objfile' and record them in the
-- compiler state for later access.
extractModules :: FilePath -> Compiler ()
extractModules objfile = do
    logBuild $ "=== Preloading Wybe-LPVM modules from " ++ objfile
    extracted <- liftIO $ machoLPVMSection objfile
    if List.null extracted
        then
        message Warning ("Unable to preload serialised LPVM from " ++ objfile)
            Nothing
        else do
        logBuild $ ">>> Extracted Module bytestring from " ++ show objfile
        let extractedSpecs = List.map modSpec extracted
        logBuild $ "+++ Recording modules: " ++ showModSpecs extractedSpecs
        -- Add the extracted modules in the 'objectModules' Map
        exMods <- gets extractedMods
        let addMod m = Map.insert (modSpec m) m
        let exMods' = List.foldr addMod exMods extracted
        modify (\s -> s { extractedMods = exMods' })



loadModuleWithModule :: Module -> Compiler ()
loadModuleWithModule m = do
    let modspec = modSpec m
    deps <- placeExtractedModule m
    subs <- collectSubModules modspec
    storedMods <- gets extractedMods
    let getStoredModule spec =
            fromMaybe
            (shouldnt ("Module " ++ showModSpec spec ++
                      " was not extracted."))
            (Map.lookup spec storedMods)
    let subMods = List.map getStoredModule subs 
    subDeps <- concat <$> mapM placeExtractedModule subMods
    modify (\comp -> let ms = m : underCompilation comp
                     in comp { underCompilation = ms })
    mapM_ buildDependency (subs ++ subDeps)
    void finishModule


loadModuleFromObjFile :: ModSpec -> FilePath -> Compiler Bool
loadModuleFromObjFile modspec objfile = do
    logBuild $ "=== ??? Trying to load LPVM Module for " ++
        showModSpec modspec ++ " from " ++ objfile
    extracted <- liftIO $ machoLPVMSection objfile
    if List.null extracted
        then do
        logBuild $ "xxx Failed extraction of LPVM Modules from object file "
            ++ objfile
        return False
        else do
        logBuild $ "=== >>> Extracted Module bytes from " ++ show objfile
        let extractedSpecs = List.map modSpec extracted
        logBuild $ "=== >>> Found modules: " ++ showModSpecs extractedSpecs
        -- Collect the imports
        imports <- concat <$> mapM placeExtractedModule extracted
        logBuild $ "=== >>> Building dependencies: " ++ showModSpecs imports
        -- Place the super mod under compilation while dependencies are built
        let superMod = head extracted
        modify (\comp -> let ms = superMod : underCompilation comp
                         in comp { underCompilation = ms })
        mapM_ buildDependency imports
        _ <- finishModule
        logBuild $ "=== <<< Extracted Module put in it's place from "
            ++ show objfile
        return True



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
    let dir = takeBaseName arch  ++ "/"
    let isWybe = List.filter ((== ".wybe") . takeExtension)
    archiveMods <- liftIO $ List.map dropExtension . isWybe <$>
        listDirectory dir
    logBuild $ "Building modules to archive: " ++ show archiveMods
    mapM_ (\m -> buildModuleIfNeeded False [m] [dir]) archiveMods
    let oFileOf m = dir ++ m ++ ".o"
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
    mapM_ (transformModuleProcs resourceCheckProc)  mspecs
    stopOnError $ "resource checking of modules " ++
      showModSpecs mspecs
    mapM_ (transformModuleProcs unbranchProc)  mspecs
    stopOnError $ "handling loops and conditionals in modules " ++
      showModSpecs mspecs
    logDump Unbranch Clause "UNBRANCHING"
    mapM_ (transformModuleProcs compileProc)  mspecs
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
isStdLib [] = False
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
    mapM_ (\(msg,pos) -> message Error msg pos) errors
    return ()
fixpointProcessSCC processor scc = do        -- must find fixpoint
    (changed,errors) <-
        foldM (\(chg,errs) mod -> do
                    (chg1,errs1) <- processor scc mod
                    return (chg1||chg, errs1++errs))
        (False,[]) scc
    if changed
    then fixpointProcessSCC processor scc
    else mapM_ (\(msg,pos) -> message Error msg pos) errors



transformModuleProcs :: (ProcDef -> Compiler ProcDef) -> ModSpec ->
                        Compiler ()
transformModuleProcs trans thisMod = do
    reenterModule thisMod
    -- (names, procs) <- :: StateT CompilerState IO ([Ident], [[ProcDef]])
    (names,procs) <- fmap unzip $
                     getModuleImplementationField (Map.toList . modProcs)
    -- for each name we have a list of procdefs, so we must double map
    procs' <- mapM (mapM trans) procs
    updateImplementation
        (\imp -> imp { modProcs = Map.union
                                  (Map.fromList $ zip names procs')
                                  (modProcs imp) })
    finishModule
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
handleModImports modSCC mod = do
    reenterModule mod
    imports <- getModuleImplementationField modImports
    kTypes <- getModuleImplementationField modKnownTypes
    kResources <- getModuleImplementationField modKnownResources
    kProcs <- getModuleImplementationField modKnownProcs
    iface <- getModuleInterface
    mapM (uncurry doImport) $ Map.toList imports
    kTypes' <- getModuleImplementationField modKnownTypes
    kResources' <- getModuleImplementationField modKnownResources
    kProcs' <- getModuleImplementationField modKnownProcs
    iface' <- getModuleInterface
    finishModule
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
buildExecutable targetMod fpath =
    do depends <- orderedDependencies targetMod
       -- Filter the modules for which the second element of the tuple is True
       let mainImports = List.foldr (\x a -> if snd x then (fst x):a else a)
               [] depends
       logBuild $ "o Modules with 'main': " ++ showModSpecs mainImports
       mainMod <- newMainModule mainImports
       logBuild $ "o Built 'main' module for target: "
       mainModStr <- liftIO $ codeemit mainMod
       logEmit $ mainModStr
       ------------
       logBuild "o Creating temp Main module @ ...../tmp/tmpMain.o"
       tempDir <- liftIO $ getTemporaryDirectory
       liftIO $ createDirectoryIfMissing False (tempDir ++ "wybetemp")
       let tmpMainOFile = tempDir ++ "wybetemp/" ++ "tmpMain.o"
       liftIO $ makeObjFile tmpMainOFile mainMod

       ofiles <- mapM loadObjectFile $ List.map fst depends
       let allOFiles = tmpMainOFile:ofiles
       -----------
       makeExec allOFiles fpath
       -- return allOFiles
       logBuild $ "o Object Files to link: "
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
        let subMods = (Map.elems . modSubmods) thisMod
        -- filter out std lib imports and sub-mod imports from imports
        -- since we are looking for imports which need a physical object file
        let imports =
                List.filter (\x -> not (elem x subMods) && (not.isStdLib) x) $
                (keys . modImports) thisMod
        -- Check if this module 'm' has a main procedure.
        let collected' = if "" `elem` procs || "<0>" `elem` procs
                         then (m, True):collected
                         else (m, False):collected
        -- Don't visit any modspec already in `ms' (will be visited as it is)
        let rem = List.foldr (\x acc -> if elem x acc then acc else x:acc)
                ms imports
        visit rem collected'


-- | Load/Build object file for the module in the same directory
-- the module is in.
loadObjectFile :: ModSpec -> Compiler FilePath
loadObjectFile thisMod =
  do reenterModule thisMod
     dir <- getDirectory
     -- generating an name + extension for our object file
     let objFile = moduleFilePath objectExtension dir thisMod
     -- Check if we need to re-emit object file
     rebuild <- objectReBuildNeeded thisMod dir
     when rebuild $ emitObjectFile thisMod objFile
     finishModule
     return objFile


objectReBuildNeeded :: ModSpec -> FilePath -> Compiler Bool
objectReBuildNeeded thisMod dir = do
    srcOb <- srcObjFiles thisMod [dir]
    case srcOb of
        Nothing -> return True
        -- only object file exists, so we have loaded Module from object
        Just (_,False,_,True,_) -> return False
        -- only source file exists
        Just (srcfile,True,objfile,False,_) -> return True
        Just (srcfile,True,objfile,True,_) -> do
            srcDate <- (liftIO . getModificationTime) srcfile
            dstDate <- (liftIO . getModificationTime) objfile
            if srcDate > dstDate
              then return True
              else return False
        Just (_,False,_,False,_) -> return True




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

-- |Given a source or executable file path, return the file path of
--  the corresponding object file.
fileObjFile :: FilePath -> FilePath
fileObjFile filename = replaceExtension filename objectExtension

-- |Given an object or executable file path, return the file path of
--  the corresponding source file.
fileSourceFile :: FilePath -> FilePath
fileSourceFile filename = replaceExtension filename sourceExtension

-- |Find the file path for the specified module spec relative to the
--  specified file path for the referencing module.
moduleFilePath :: String -> FilePath -> ModSpec -> FilePath
moduleFilePath extension dir spec = do
    addExtension (joinPath $ (splitDirectories dir) ++ spec) extension


-- |Log a message, if we are logging builder activity (file-level compilation).
logBuild :: String -> Compiler ()
logBuild s = logMsg Builder s

