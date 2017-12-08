

--  File     : Config.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Sat Feb 18 00:38:48 2012
--  Purpose  : Configuration for wybe compiler
--  Copyright: (c) 2012 Peter Schachte.  All rights reserved.

-- |Compiler configuration parameters.  These may vary between
--  OSes.
module Config (sourceExtension, objectExtension, executableExtension,
               interfaceExtension, bitcodeExtension, sharedLibs,
               ldArgs, ldSystemArgs, wordSize, wordSizeBytes,
               availableTagBits, tagMask, smallestAllocatedAddress,
               assemblyExtension, archiveExtension, magicVersion)
    where

import Data.Word
import qualified Data.List as List
import Foreign.Storable


-- |The file extension for source files.
sourceExtension :: String
sourceExtension = "wybe"


-- |The file extension for object files.
objectExtension :: String
objectExtension = "o"


-- |The file extension for executable files.
executableExtension :: String
executableExtension = ""


-- |The file extension for interface files.
interfaceExtension :: String
interfaceExtension = "int"


-- |The file extension for bitcode files.
bitcodeExtension :: String
bitcodeExtension = "bc"


-- |The file extension for assembly files.
assemblyExtension :: String
assemblyExtension = "ll"


-- |The file extension for object archive files.
archiveExtension :: String
archiveExtension = "a"


-- |Determining word size of the machine in bits
wordSize :: Int
wordSize = wordSizeBytes * 8


-- |Word size of the machine in bytes
wordSizeBytes :: Int
wordSizeBytes = sizeOf (fromIntegral 3 :: Word)


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


-- |Foreign shared library directory name
sharedLibDirName :: String
sharedLibDirName = "lib/"


sharedLibs :: [FilePath]
sharedLibs = ["cbits.so"]


ldArgs :: [String]
ldArgs = ["-demangle", "-dynamic"]


ldSystemArgs :: [String]
ldSystemArgs =
    [ "-arch", "x86_64",
      "-macosx_version_min", "10.11.0",
      "-syslibroot",
      "/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX10.11.sdk",
      "-lSystem",
      "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/bin/../lib/clang/7.0.2/lib/darwin/libclang_rt.osx.a"
    ]


-- | Magic version number for the current iteration of LPVM.
magicVersion :: [Word8]
magicVersion =
    let magicStr = "WB01"
    in List.map (fromIntegral . fromEnum) magicStr
