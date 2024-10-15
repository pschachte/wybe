--  File     : Config.hs
--  Author   : Peter Schachte
--  Purpose  : Configuration for wybe compiler
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


-- |Compiler configuration parameters.  These may vary between
--  OSes.
module Config (sourceExtension, objectExtension, executableExtension,
               bitcodeExtension, assemblyExtension, nativeAssemblyExtension,
               archiveExtension, moduleDirectoryBasename, currentModuleAlias,
               specialChar, specialName, specialName2, initProcName,
               wordSize, wordSizeBytes,
               availableTagBits, tagMask, smallestAllocatedAddress,
               minimumSwitchCases, magicVersion,
               linkerDeadStripArgs, removeLPVMSection,
               llvmToBitcodeCommand, llvmToNativeAssemblerCommand,
               llvmToObjectCommand,
               lpvmSectionName, localCacheLibDir)
    where

import Options
import Data.Word
import qualified Data.List as List
import Distribution.System (buildOS, OS (..))
import Foreign.Storable
import System.Exit (ExitCode (..))
import System.Process
import System.FilePath
import System.Directory.Extra (getHomeDirectory)


-- |The file extension for source files.
sourceExtension :: String
sourceExtension = "wybe"


-- |The file extension for object files.
objectExtension :: String
objectExtension = "o"


-- |The file extension for executable files.
executableExtension :: String
executableExtension = ""


-- |The file extension for bitcode files.
bitcodeExtension :: String
bitcodeExtension = "bc"


-- |The file extension for LLVM assembly files.
assemblyExtension :: String
assemblyExtension = "ll"


-- |The file extension for native assembly files.
nativeAssemblyExtension :: String
nativeAssemblyExtension = "s"


-- |The file extension for object archive files.
archiveExtension :: String
archiveExtension = "a"


-- |The basename of the Wybe file that must exist in a directory for it to be a
-- module.
moduleDirectoryBasename :: String
moduleDirectoryBasename = "_"


-- |The special name given to the current module.
currentModuleAlias :: String
currentModuleAlias = "_"


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


-- |The proc to initialise each module (using the top-level code of the module)
initProcName :: String
initProcName = ""


-- |Determining word size of the machine in bits
wordSize :: Int
wordSize = wordSizeBytes * 8


-- |Word size of the machine in bytes
wordSizeBytes :: Int
wordSizeBytes = sizeOf (3 :: Word)


-- |The number of tag bits available on this architecture.  This is the base 2
--  log of the word size in bytes, assuming this is a byte addressed machine.
--  XXX this would need to be fixed for non-byte addressed architectures.
availableTagBits :: Int
availableTagBits = floor $ logBase 2 $ fromIntegral wordSizeBytes


-- |The bitmask to use to mask out all but the tag bits of a tagged pointer.
--  This is also the maximim number of non-constant constructors we can
--  handle without boxing.  If we have more than that, we can only have one
--  less than this many unboxed constructors, because we need to use one tag
--  to indicate that the constructor is boxed.
tagMask :: Int
tagMask = 2^availableTagBits - 1


-- |The smallest address that allocation could return.  This the upper limit
--  on the constant constructors we can accommodate without boxing.
smallestAllocatedAddress :: Integer
smallestAllocatedAddress = 65536 -- this is a pretty safe guess


-- |The smallest number of nested equality tests of the same variable we will
-- bother to turn into a switch.
minimumSwitchCases :: Int
minimumSwitchCases = 3


-- |Foreign shared library directory name
sharedLibDirName :: String
sharedLibDirName = "lib/"


localCacheLibDir :: IO FilePath
localCacheLibDir = do
    homeDir <- getHomeDirectory
    return $ homeDir </> ".wybe/cache"


-- | Magic version number for the current iteration of LPVM.
magicVersion :: [Word8]
magicVersion =
    let magicStr = "WB02"
    in List.map (fromIntegral . fromEnum) magicStr


-- | Arguments of dead code elimination for linker
-- Look for "Link time dead code elimination" in "Emit.hs" for more detail
linkerDeadStripArgs :: [String]
linkerDeadStripArgs =
    case buildOS of
        OSX   -> ["-dead_strip"]
        Linux -> ["-Wl,--gc-sections"]
        os    -> error $ "Unsupported OS: " ++ show os


-- | Command and switches to compile a .ll file to bitcode.
llvmToBitcodeCommand :: FilePath -> FilePath -> Options  -> (String, [String])
llvmToBitcodeCommand llFile bcFile _ =
    case buildOS of
        OSX   -> ("llvm-as", ["-o", bcFile, llFile])
        Linux -> ("llvm-as", ["-o", bcFile, llFile])
        os    -> error $ "Unsupported OS: " ++ show os


-- | Command and switches to compile a .ll file to native assembler.
llvmToNativeAssemblerCommand :: FilePath -> FilePath -> Options
                             -> (String, [String])
llvmToNativeAssemblerCommand llFile sFile options =
    let opt = "-O" ++ show (optLLVMOptLevel options)
    in case buildOS of
        OSX   -> ("llc", ["--filetype=asm", opt, "-o", sFile, llFile])
        Linux -> ("llc", ["--filetype=asm", opt, "-o", sFile, llFile])
        os    -> error $ "Unsupported OS: " ++ show os


-- | Command and switches to compile a .ll file to an object file.
llvmToObjectCommand :: FilePath -> FilePath -> Options  -> (String, [String])
llvmToObjectCommand llFile oFile options =
    let opt = "-O" ++ show (optLLVMOptLevel options)
    in case buildOS of
        OSX   -> ("llc", ["--filetype=obj", opt, "-o", oFile, llFile])
        Linux -> ("llc", ["--filetype=obj", opt, "-o", oFile, llFile])
        os    -> error $ "Unsupported OS: " ++ show os


-- | The section name of the LPVM object file section.  This includes the
-- segment name, as well, and the format varies depending on object file format.
lpvmSectionName :: String
lpvmSectionName = "__LPVM,__lpvm"


-- | Remove the lpvm section from the given file. It's only effective on Linux,
-- since we don't need it on macOS.
removeLPVMSection :: FilePath -> IO (Either String ())
removeLPVMSection target =
    case buildOS of
        OSX   -> return $ Right ()
        Linux -> do
            let args = ["--remove-section", lpvmSectionName, target]
            (exCode, _, serr) <-
                    readCreateProcessWithExitCode (proc "objcopy" args) ""
            case exCode of
                ExitSuccess  -> return $ Right ()
                _ -> return $ Left serr
        os    -> error $ "Unsupported OS: " ++ show os
