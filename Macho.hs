{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{- | Data.Macho is a module for parsing a ByteString of a Mach-O file into a
Macho record. Original: hackage.haskell.org/package/macho-0.22

This implementation is slightly modified to accomodate new load commands not
accounted for, instead of quitting in an exception.

-}

module Macho ( parseMacho
             , Macho(..)
             , MachoHeader(..)
             , LC_COMMAND(..)
             , CPU_TYPE(..)
             , CPU_SUBTYPE(..)
             , MH_FLAGS(..)
             , VM_PROT(..)
             , MachoSegment(..)
             , SG_FLAG(..)
             , MachoSection(..)
             , S_TYPE(..)
             , S_USER_ATTR(..)
             , S_SYS_ATTR(..)
             , N_TYPE(..)
             , REFERENCE_FLAG(..)
             , MachoSymbol(..)
             , DylibModule(..)
             , R_TYPE(..)
             , Relocation(..)
             , MachoDynamicSymbolTable(..)
             , MH_FILETYPE(..)) where

import Data.Binary
import Data.Binary.Get
import Data.Bits
import Data.Word
import Data.Int
import Numeric
import Control.Monad
import Control.Applicative
import qualified Data.ByteString          as B
import qualified Data.ByteString.Char8    as C
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Lazy     as L

data MH_MAGIC
    = MH_MAGIC32
    | MH_MAGIC64
    | MH_CIGAM32
    | MH_CIGAM64
macho_magic 0xfeedface = MH_MAGIC32
macho_magic 0xfeedfacf = MH_MAGIC64
macho_magic 0xcefaedfe = MH_CIGAM32
macho_magic 0xcffaedfe = MH_CIGAM64

bitfield_le off sz word = (word `shiftL` (32 - off - sz)) `shiftR` (32 - sz)
bitfield_be off sz word = (word `shiftL` off) `shiftR` (32 - sz)

data MachoReader = MachoReader
    { is64bit   :: Bool
    , getWord16 :: Get Word16
    , getWord32 :: Get Word32
    , getWord64 :: Get Word64
    , bitfield  :: Int -> Int -> Word32 -> Word32
    }
macho_reader MH_MAGIC32 = MachoReader { is64bit = False, getWord16 = getWord16le, getWord32 = getWord32le, getWord64 = getWord64le, bitfield = bitfield_le }
macho_reader MH_MAGIC64 = MachoReader { is64bit = True, getWord16 = getWord16le, getWord32 = getWord32le, getWord64 = getWord64le, bitfield = bitfield_le }
macho_reader MH_CIGAM32 = MachoReader { is64bit = False, getWord16 = getWord16be, getWord32 = getWord32be, getWord64 = getWord64be, bitfield = bitfield_be }
macho_reader MH_CIGAM64 = MachoReader { is64bit = True, getWord16 = getWord16be, getWord32 = getWord32be, getWord64 = getWord64be, bitfield = bitfield_be }

data CPU_TYPE
    = CPU_TYPE_X86
    | CPU_TYPE_X86_64
    | CPU_TYPE_ARM
    | CPU_TYPE_POWERPC
    | CPU_TYPE_POWERPC64
    deriving (Show, Eq)
mach_cputype 0x00000007 = CPU_TYPE_X86
mach_cputype 0x01000007 = CPU_TYPE_X86_64
mach_cputype 0x0000000c = CPU_TYPE_ARM
mach_cputype 0x00000012 = CPU_TYPE_POWERPC
mach_cputype 0x01000012 = CPU_TYPE_POWERPC64

data CPU_SUBTYPE
    = CPU_SUBTYPE_INTEL
    | CPU_SUBTYPE_I386_ALL
    | CPU_SUBTYPE_386
    | CPU_SUBTYPE_486
    | CPU_SUBTYPE_486SX
    | CPU_SUBTYPE_PENT
    | CPU_SUBTYPE_PENTPRO
    | CPU_SUBTYPE_PENTII_M3
    | CPU_SUBTYPE_PENTII_M5
    | CPU_SUBTYPE_CELERON
    | CPU_SUBTYPE_CELERON_MOBILE
    | CPU_SUBTYPE_PENTIUM_3
    | CPU_SUBTYPE_PENTIUM_3_M
    | CPU_SUBTYPE_PENTIUM_3_XEON
    | CPU_SUBTYPE_PENTIUM_M
    | CPU_SUBTYPE_PENTIUM_4
    | CPU_SUBTYPE_PENTIUM_4_M
    | CPU_SUBTYPE_ITANIUM
    | CPU_SUBTYPE_ITANIUM_2
    | CPU_SUBTYPE_XEON
    | CPU_SUBTYPE_XEON_MP
    | CPU_SUBTYPE_INTEL_FAMILY
    | CPU_SUBTYPE_INTEL_FAMILY_MAX
    | CPU_SUBTYPE_INTEL_MODEL
    | CPU_SUBTYPE_INTEL_MODEL_ALL
    | CPU_SUBTYPE_X86_ALL
    | CPU_SUBTYPE_X86_64_ALL
    | CPU_SUBTYPE_X86_ARCH1
    | CPU_SUBTYPE_POWERPC_ALL
    | CPU_SUBTYPE_POWERPC_601
    | CPU_SUBTYPE_POWERPC_602
    | CPU_SUBTYPE_POWERPC_603
    | CPU_SUBTYPE_POWERPC_603e
    | CPU_SUBTYPE_POWERPC_603ev
    | CPU_SUBTYPE_POWERPC_604
    | CPU_SUBTYPE_POWERPC_604e
    | CPU_SUBTYPE_POWERPC_620
    | CPU_SUBTYPE_POWERPC_750
    | CPU_SUBTYPE_POWERPC_7400
    | CPU_SUBTYPE_POWERPC_7450
    | CPU_SUBTYPE_POWERPC_970
    | CPU_SUBTYPE_ARM_ALL
    | CPU_SUBTYPE_ARM_V4T
    | CPU_SUBTYPE_ARM_V6
    deriving (Show, Eq)
mach_cpusubtype CPU_TYPE_X86 132       = CPU_SUBTYPE_486SX
mach_cpusubtype CPU_TYPE_X86 5         = CPU_SUBTYPE_PENT
mach_cpusubtype CPU_TYPE_X86 22        = CPU_SUBTYPE_PENTPRO
mach_cpusubtype CPU_TYPE_X86 54        = CPU_SUBTYPE_PENTII_M3
mach_cpusubtype CPU_TYPE_X86 86        = CPU_SUBTYPE_PENTII_M5
mach_cpusubtype CPU_TYPE_X86 103       = CPU_SUBTYPE_CELERON
mach_cpusubtype CPU_TYPE_X86 119       = CPU_SUBTYPE_CELERON_MOBILE
mach_cpusubtype CPU_TYPE_X86 8         = CPU_SUBTYPE_PENTIUM_3
mach_cpusubtype CPU_TYPE_X86 24        = CPU_SUBTYPE_PENTIUM_3_M
mach_cpusubtype CPU_TYPE_X86 40        = CPU_SUBTYPE_PENTIUM_3_XEON
mach_cpusubtype CPU_TYPE_X86 9         = CPU_SUBTYPE_PENTIUM_M
mach_cpusubtype CPU_TYPE_X86 10        = CPU_SUBTYPE_PENTIUM_4
mach_cpusubtype CPU_TYPE_X86 26        = CPU_SUBTYPE_PENTIUM_4_M
mach_cpusubtype CPU_TYPE_X86 11        = CPU_SUBTYPE_ITANIUM
mach_cpusubtype CPU_TYPE_X86 27        = CPU_SUBTYPE_ITANIUM_2
mach_cpusubtype CPU_TYPE_X86 12        = CPU_SUBTYPE_XEON
mach_cpusubtype CPU_TYPE_X86 28        = CPU_SUBTYPE_XEON_MP
mach_cpusubtype CPU_TYPE_X86 3         = CPU_SUBTYPE_X86_ALL
mach_cpusubtype CPU_TYPE_X86 4         = CPU_SUBTYPE_X86_ARCH1
mach_cpusubtype CPU_TYPE_X86_64 3      = CPU_SUBTYPE_X86_64_ALL
mach_cpusubtype CPU_TYPE_POWERPC 0     = CPU_SUBTYPE_POWERPC_ALL
mach_cpusubtype CPU_TYPE_POWERPC 1     = CPU_SUBTYPE_POWERPC_601
mach_cpusubtype CPU_TYPE_POWERPC 2     = CPU_SUBTYPE_POWERPC_602
mach_cpusubtype CPU_TYPE_POWERPC 3     = CPU_SUBTYPE_POWERPC_603
mach_cpusubtype CPU_TYPE_POWERPC 4     = CPU_SUBTYPE_POWERPC_603e
mach_cpusubtype CPU_TYPE_POWERPC 5     = CPU_SUBTYPE_POWERPC_603ev
mach_cpusubtype CPU_TYPE_POWERPC 6     = CPU_SUBTYPE_POWERPC_604
mach_cpusubtype CPU_TYPE_POWERPC 7     = CPU_SUBTYPE_POWERPC_604e
mach_cpusubtype CPU_TYPE_POWERPC 8     = CPU_SUBTYPE_POWERPC_620
mach_cpusubtype CPU_TYPE_POWERPC 9     = CPU_SUBTYPE_POWERPC_750
mach_cpusubtype CPU_TYPE_POWERPC 10    = CPU_SUBTYPE_POWERPC_7400
mach_cpusubtype CPU_TYPE_POWERPC 11    = CPU_SUBTYPE_POWERPC_7450
mach_cpusubtype CPU_TYPE_POWERPC 100   = CPU_SUBTYPE_POWERPC_970
mach_cpusubtype CPU_TYPE_POWERPC64 0   = CPU_SUBTYPE_POWERPC_ALL
mach_cpusubtype CPU_TYPE_POWERPC64 1   = CPU_SUBTYPE_POWERPC_601
mach_cpusubtype CPU_TYPE_POWERPC64 2   = CPU_SUBTYPE_POWERPC_602
mach_cpusubtype CPU_TYPE_POWERPC64 3   = CPU_SUBTYPE_POWERPC_603
mach_cpusubtype CPU_TYPE_POWERPC64 4   = CPU_SUBTYPE_POWERPC_603e
mach_cpusubtype CPU_TYPE_POWERPC64 5   = CPU_SUBTYPE_POWERPC_603ev
mach_cpusubtype CPU_TYPE_POWERPC64 6   = CPU_SUBTYPE_POWERPC_604
mach_cpusubtype CPU_TYPE_POWERPC64 7   = CPU_SUBTYPE_POWERPC_604e
mach_cpusubtype CPU_TYPE_POWERPC64 8   = CPU_SUBTYPE_POWERPC_620
mach_cpusubtype CPU_TYPE_POWERPC64 9   = CPU_SUBTYPE_POWERPC_750
mach_cpusubtype CPU_TYPE_POWERPC64 10  = CPU_SUBTYPE_POWERPC_7400
mach_cpusubtype CPU_TYPE_POWERPC64 11  = CPU_SUBTYPE_POWERPC_7450
mach_cpusubtype CPU_TYPE_POWERPC64 100 = CPU_SUBTYPE_POWERPC_970
mach_cpusubtype CPU_TYPE_ARM 0         = CPU_SUBTYPE_ARM_ALL
mach_cpusubtype CPU_TYPE_ARM 5         = CPU_SUBTYPE_ARM_V4T
mach_cpusubtype CPU_TYPE_ARM 6         = CPU_SUBTYPE_ARM_V6

data MachoHeader = MachoHeader
    { mh_cputype    :: CPU_TYPE    -- ^ CPU family the Mach-O executes on.
    , mh_cpusubtype :: CPU_SUBTYPE -- ^ Specific CPU type the Mach-O executes on.
    , mh_filetype   :: MH_FILETYPE -- ^ Type of Mach-o file.
    , mh_flags      :: [MH_FLAGS]  -- ^ Flags.
    } deriving (Show, Eq)

getMachoHeader :: Get (MachoReader, Int, Int, MachoHeader)
getMachoHeader = do
  magic      <- liftM macho_magic getWord32le
  reader     <- return $ macho_reader magic
  cputype    <- liftM mach_cputype $ getWord32 reader
  cpusubtype <- liftM (mach_cpusubtype cputype)$ getWord32 reader
  filetype   <- liftM mach_filetype $ getWord32 reader
  ncmds      <- liftM fromIntegral $ getWord32 reader
  sizeofcmds <- liftM fromIntegral $ getWord32 reader
  flags      <- getMachHeaderFlags reader
  reserved   <- case magic of
      MH_MAGIC64 -> getWord32 reader
      MH_CIGAM64 -> getWord32 reader
      _          -> return 0
  headerSize <- liftM fromIntegral bytesRead
  return (reader, sizeofcmds, headerSize, MachoHeader cputype cpusubtype filetype flags)

getLoadCommands mr fl mh = do
    empty <- isEmpty
    if empty then
        return []
     else do
        cmd     <- liftM fromIntegral $ getWord32 mr
        cmdsize <- liftM fromIntegral $ getWord32 mr
        lcdata  <- getByteString (cmdsize - 8)
        lc      <- return $ runGet (getLoadCommand cmd mr lcdata fl mh) (L.fromChunks [lcdata])
        rest    <- getLoadCommands mr fl mh
        return $ lc : rest

data Macho = Macho
    { m_header   :: MachoHeader  -- ^ Header information.
    , m_commands :: [LC_COMMAND] -- ^ List of load commands describing Mach-O contents.
    } deriving (Show, Eq)

-- | Parse a ByteString of a Mach-O object into a Macho record.
parseMacho :: B.ByteString -> (Int, Macho)
parseMacho b =
    let (mr, sizeofcmds, hdrSize, header) = runGet getMachoHeader $ L.fromChunks [b]
        commands = runGet (getLoadCommands mr b header) $ L.fromChunks [B.take sizeofcmds $ B.drop hdrSize b]
    in (sizeofcmds, Macho header commands)

data MH_FILETYPE
    = MH_OBJECT                   -- ^ relocatable object file
    | MH_EXECUTE                  -- ^ demand paged executable file
    | MH_CORE                     -- ^ core file
    | MH_PRELOAD                  -- ^ preloaded executable file
    | MH_DYLIB                    -- ^ dynamically bound shared library
    | MH_DYLINKER                 -- ^ dynamic link editor
    | MH_BUNDLE                   -- ^ dynamically bound bundle file
    | MH_DYLIB_STUB               -- ^ shared library stub for static. linking only, no section contents
    | MH_DSYM                     -- ^ companion file with only debug. sections
    deriving (Show, Eq)
mach_filetype 0x1 = MH_OBJECT
mach_filetype 0x2 = MH_EXECUTE
mach_filetype 0x4 = MH_CORE
mach_filetype 0x5 = MH_PRELOAD
mach_filetype 0x6 = MH_DYLIB
mach_filetype 0x7 = MH_DYLINKER
mach_filetype 0x8 = MH_BUNDLE
mach_filetype 0x9 = MH_DYLIB_STUB
mach_filetype 0xa = MH_DSYM

data MH_FLAGS
    = MH_NOUNDEFS                -- ^ the object file has no undefined references
    | MH_INCRLINK                -- ^ the object file is the output of an incremental link against a base file and can't be link edited again
    | MH_DYLDLINK                -- ^ the object file is input for the dynamic linker and can't be staticly link edited again
    | MH_BINDATLOAD              -- ^ the object file's undefined references are bound by the dynamic linker when loaded.
    | MH_PREBOUND                -- ^ the file has its dynamic undefined references prebound.
    | MH_SPLIT_SEGS              -- ^ the file has its read-only and read-write segments split
    | MH_TWOLEVEL                -- ^ the image is using two-level name space bindings
    | MH_FORCE_FLAT              -- ^ the executable is forcing all images to use flat name space bindings
    | MH_NOMULTIDEFS             -- ^ this umbrella guarantees no multiple defintions of symbols in its sub-images so the two-level namespace hints can always be used.
    | MH_NOFIXPREBINDING         -- ^ do not have dyld notify the prebinding agent about this executable
    | MH_PREBINDABLE             -- ^ the binary is not prebound but can have its prebinding redone. only used when MH_PREBOUND is not set.
    | MH_ALLMODSBOUND            -- ^ indicates that this binary binds to all two-level namespace modules of its dependent libraries. only used when MH_PREBINDABLE and MH_TWOLEVEL are both set.
    | MH_SUBSECTIONS_VIA_SYMBOLS -- ^ safe to divide up the sections into sub-sections via symbols for dead code stripping
    | MH_CANONICAL               -- ^ the binary has been canonicalized via the unprebind operation
    | MH_WEAK_DEFINES            -- ^ the final linked image contains external weak symbols
    | MH_BINDS_TO_WEAK           -- ^ the final linked image uses weak symbols
    | MH_ALLOW_STACK_EXECUTION   -- ^ When this bit is set, all stacks  in the task will be given stack execution privilege.  Only used in MH_EXECUTE filetypes.
    | MH_ROOT_SAFE               -- ^ When this bit is set, the binary  declares it is safe for use in processes with uid zero
    | MH_SETUID_SAFE             -- ^ When this bit is set, the binary  declares it is safe for use in processes when issetugid() is true
    | MH_NO_REEXPORTED_DYLIBS    -- ^ When this bit is set on a dylib,  the static linker does not need to examine dependent dylibs to see if any are re-exported
    | MH_PIE                     -- ^ When this bit is set, the OS will load the main executable at a random address.  Only used in MH_EXECUTE filetypes.
    deriving (Show, Eq)
getMachHeaderFlags :: MachoReader -> Get [MH_FLAGS]
getMachHeaderFlags mr = liftM (getMachHeaderFlags_ 31) (getWord32 mr)
    where getMachHeaderFlags_  0 word = []
          getMachHeaderFlags_  1 word | testBit word  0 = MH_NOUNDEFS                : getMachHeaderFlags_  0 word
          getMachHeaderFlags_  2 word | testBit word  1 = MH_INCRLINK                : getMachHeaderFlags_  1 word
          getMachHeaderFlags_  3 word | testBit word  2 = MH_DYLDLINK                : getMachHeaderFlags_  2 word
          getMachHeaderFlags_  4 word | testBit word  3 = MH_BINDATLOAD              : getMachHeaderFlags_  3 word
          getMachHeaderFlags_  5 word | testBit word  4 = MH_PREBOUND                : getMachHeaderFlags_  4 word
          getMachHeaderFlags_  6 word | testBit word  5 = MH_SPLIT_SEGS              : getMachHeaderFlags_  5 word
          getMachHeaderFlags_  8 word | testBit word  7 = MH_TWOLEVEL                : getMachHeaderFlags_  7 word
          getMachHeaderFlags_  9 word | testBit word  8 = MH_FORCE_FLAT              : getMachHeaderFlags_  8 word
          getMachHeaderFlags_ 10 word | testBit word  9 = MH_NOMULTIDEFS             : getMachHeaderFlags_  9 word
          getMachHeaderFlags_ 11 word | testBit word 10 = MH_NOFIXPREBINDING         : getMachHeaderFlags_ 10 word
          getMachHeaderFlags_ 12 word | testBit word 11 = MH_PREBINDABLE             : getMachHeaderFlags_ 11 word
          getMachHeaderFlags_ 13 word | testBit word 12 = MH_ALLMODSBOUND            : getMachHeaderFlags_ 12 word
          getMachHeaderFlags_ 14 word | testBit word 13 = MH_SUBSECTIONS_VIA_SYMBOLS : getMachHeaderFlags_ 13 word
          getMachHeaderFlags_ 15 word | testBit word 14 = MH_CANONICAL               : getMachHeaderFlags_ 14 word
          getMachHeaderFlags_ 16 word | testBit word 15 = MH_WEAK_DEFINES            : getMachHeaderFlags_ 15 word
          getMachHeaderFlags_ 17 word | testBit word 16 = MH_BINDS_TO_WEAK           : getMachHeaderFlags_ 16 word
          getMachHeaderFlags_ 18 word | testBit word 17 = MH_ALLOW_STACK_EXECUTION   : getMachHeaderFlags_ 17 word
          getMachHeaderFlags_ 19 word | testBit word 18 = MH_ROOT_SAFE               : getMachHeaderFlags_ 18 word
          getMachHeaderFlags_ 20 word | testBit word 19 = MH_SETUID_SAFE             : getMachHeaderFlags_ 19 word
          getMachHeaderFlags_ 21 word | testBit word 20 = MH_NO_REEXPORTED_DYLIBS    : getMachHeaderFlags_ 20 word
          getMachHeaderFlags_ 22 word | testBit word 21 = MH_PIE                     : getMachHeaderFlags_ 21 word
          getMachHeaderFlags_  n word = getMachHeaderFlags_ (n-1) word

data LC_COMMAND
    = LC_SEGMENT MachoSegment                        -- ^ segment of this file to be mapped
    | LC_SYMTAB [MachoSymbol] B.ByteString           -- ^ static link-edit symbol table and stab info
    | LC_THREAD [(Word32, [Word32])]                 -- ^ thread state information (list of (flavor, [long]) pairs)
    | LC_UNIXTHREAD [(Word32, [Word32])]             -- ^ unix thread state information (includes a stack) (list of (flavor, [long] pairs)
    | LC_DYSYMTAB MachoDynamicSymbolTable            -- ^ dynamic link-edit symbol table info
    | LC_LOAD_DYLIB String Word32 Word32 Word32      -- ^ load a dynamically linked shared library (name, timestamp, current version, compatibility version)
    | LC_ID_DYLIB String Word32 Word32 Word32        -- ^ dynamically linked shared lib ident (name, timestamp, current version, compatibility version)
    | LC_LOAD_DYLINKER String                        -- ^ load a dynamic linker (name of dynamic linker)
    | LC_ID_DYLINKER String                          -- ^ dynamic linker identification (name of dynamic linker)
    | LC_PREBOUND_DYLIB String [Word8]               -- ^ modules prebound for a dynamically linked shared library (name, list of module indices)
    | LC_ROUTINES Word32 Word32                      -- ^ image routines (virtual address of initialization routine, module index where it resides)
    | LC_SUB_FRAMEWORK String                        -- ^ sub framework (name)
    | LC_SUB_UMBRELLA String                         -- ^ sub umbrella (name)
    | LC_SUB_CLIENT String                           -- ^ sub client (name)
    | LC_SUB_LIBRARY String                          -- ^ sub library (name)
    | LC_TWOLEVEL_HINTS [(Word32, Word32)]           -- ^ two-level namespace lookup hints (list of (subimage index, symbol table index) pairs
    | LC_PREBIND_CKSUM Word32                        -- ^ prebind checksum (checksum)
    | LC_LOAD_WEAK_DYLIB String Word32 Word32 Word32 -- ^ load a dynamically linked shared library that is allowed to be missing (symbols are weak imported) (name, timestamp, current version, compatibility version)
    | LC_SEGMENT_64 MachoSegment                     -- ^ 64-bit segment of this file to mapped
    | LC_ROUTINES_64 Word64 Word64                   -- ^ 64-bit image routines (virtual address of initialization routine, module index where it resides)
    | LC_UUID [Word8]                                -- ^ the uuid for an image or its corresponding dsym file (8 element list of bytes)
    | LC_RPATH String                                -- ^ runpath additions (path)
    | LC_CODE_SIGNATURE Word32 Word32                -- ^ local of code signature
    | LC_SEGMENT_SPLIT_INFO Word32 Word32            -- ^ local of info to split segments
    | LC_NOP
    deriving (Show, Eq)

getLoadCommand 0x00000001 mr lc fl mh = getSegmentCommand32 mr fl mh
getLoadCommand 0x00000002 mr lc fl mh = getSymTabCommand mr fl mh
getLoadCommand 0x00000004 mr lc fl mh = getThreadCommand mr LC_THREAD
getLoadCommand 0x00000005 mr lc fl mh = getThreadCommand mr LC_UNIXTHREAD
getLoadCommand 0x0000000b mr lc fl mh = getDySymTabCommand mr fl mh
getLoadCommand 0x0000000c mr lc fl mh = getDylibCommand mr lc LC_LOAD_DYLIB
getLoadCommand 0x0000000d mr lc fl mh = getDylibCommand mr lc LC_ID_DYLIB
getLoadCommand 0x0000000e mr lc fl mh = getDylinkerCommand mr lc LC_LOAD_DYLINKER
getLoadCommand 0x0000000f mr lc fl mh = getDylinkerCommand mr lc LC_ID_DYLINKER
getLoadCommand 0x00000010 mr lc fl mh = getPreboundDylibCommand mr lc
getLoadCommand 0x00000011 mr lc fl mh = getRoutinesCommand32 mr
getLoadCommand 0x00000012 mr lc fl mh = getSubFrameworkCommand mr lc
getLoadCommand 0x00000013 mr lc fl mh = getSubUmbrellaCommand mr lc
getLoadCommand 0x00000014 mr lc fl mh = getSubClientCommand mr lc
getLoadCommand 0x00000015 mr lc fl mh = getSubLibraryCommand mr lc
getLoadCommand 0x00000016 mr lc fl mh = getTwoLevelHintsCommand mr fl
getLoadCommand 0x00000017 mr lc fl mh = getPrebindCkSumCommand mr
getLoadCommand 0x80000018 mr lc fl mh = getDylibCommand mr lc LC_LOAD_WEAK_DYLIB
getLoadCommand 0x00000019 mr lc fl mh = getSegmentCommand64 mr fl mh
getLoadCommand 0x0000001a mr lc fl mh = getRoutinesCommand64 mr
getLoadCommand 0x0000001b mr lc fl mh = getUUIDCommand mr
getLoadCommand 0x8000001c mr lc fl mh = getRPathCommand mr lc
getLoadCommand 0x0000001d mr lc fl mh = getLinkEditCommand mr lc LC_CODE_SIGNATURE
getLoadCommand 0x0000001e mr lc fl mh = getLinkEditCommand mr lc LC_SEGMENT_SPLIT_INFO
getLoadCommand x _ _ _ _ = return LC_NOP

data VM_PROT
    = VM_PROT_READ    -- ^ read permission
    | VM_PROT_WRITE   -- ^ write permission
    | VM_PROT_EXECUTE -- ^ execute permission
    deriving (Show, Eq)
getVM_PROT mr = liftM (getVM_PROT_ 31) (getWord32 mr)
    where getVM_PROT_ 0 word = []
          getVM_PROT_ 1 word | testBit word 0 = VM_PROT_READ    : getVM_PROT_ 0 word
          getVM_PROT_ 2 word | testBit word 1 = VM_PROT_WRITE   : getVM_PROT_ 1 word
          getVM_PROT_ 3 word | testBit word 2 = VM_PROT_EXECUTE : getVM_PROT_ 2 word
          getVM_PROT_ n word = getVM_PROT_ (n-1) word

data MachoSegment = MachoSegment
    { seg_segname  :: String         -- ^ segment name
    , seg_vmaddr   :: Word64         -- ^ virtual address where the segment is loaded
    , seg_vmsize   :: Word64         -- ^ size of segment at runtime
    , seg_fileoff  :: Word64         -- ^ file offset of the segment
    , seg_filesize :: Word64         -- ^ size of segment in file
    , seg_maxprot  :: [VM_PROT]      -- ^ maximum virtual memory protection
    , seg_initprot :: [VM_PROT]      -- ^ initial virtual memory protection
    , seg_flags    :: [SG_FLAG]      -- ^ segment flags
    , seg_sections :: [MachoSection] -- ^ sections owned by this segment
    } deriving (Show, Eq)

getSegmentCommand32 mr fl mh = do
    segname  <- liftM (takeWhile (/= '\0') . C.unpack) $ getByteString 16
    vmaddr   <- liftM fromIntegral $ getWord32 mr
    vmsize   <- liftM fromIntegral $ getWord32 mr
    fileoff  <- liftM fromIntegral $ getWord32 mr
    filesize <- liftM fromIntegral $ getWord32 mr
    maxprot  <- getVM_PROT mr
    initprot <- getVM_PROT mr
    nsects   <- liftM fromIntegral $ getWord32 mr
    flags    <- getSG_FLAG mr
    sects    <- sequence (replicate nsects (getSection32 mr fl mh))
    return $ LC_SEGMENT MachoSegment
                            { seg_segname = segname
                            , seg_vmaddr  = vmaddr
                            , seg_vmsize  = vmsize
                            , seg_fileoff = fileoff
                            , seg_filesize = filesize
                            , seg_maxprot  = maxprot
                            , seg_initprot = initprot
                            , seg_flags    = flags
                            , seg_sections = sects }
getSegmentCommand64 mr fl mh = do
    segname  <- liftM (takeWhile (/= '\0') . C.unpack) $ getByteString 16
    vmaddr   <- getWord64 mr
    vmsize   <- getWord64 mr
    fileoff  <- getWord64 mr
    filesize <- getWord64 mr
    maxprot  <- getVM_PROT mr
    initprot <- getVM_PROT mr
    nsects   <- liftM fromIntegral $ getWord32 mr
    flags    <- getSG_FLAG mr
    sects    <- sequence (replicate nsects (getSection64 mr fl mh))
    return $ LC_SEGMENT_64 MachoSegment
                            { seg_segname = segname
                            , seg_vmaddr  = vmaddr
                            , seg_vmsize  = vmsize
                            , seg_fileoff = fileoff
                            , seg_filesize = filesize
                            , seg_maxprot  = maxprot
                            , seg_initprot = initprot
                            , seg_flags    = flags
                            , seg_sections = sects }

data SG_FLAG
    = SG_HIGHVM  -- ^ The file contents for this segment is for the high part of the VM space, the low part is zero filled (for stacks in core files).
    | SG_NORELOC -- ^ This segment has nothing that was relocated in it and nothing relocated to it, that is it may be safely replaced without relocation.
    deriving (Show, Eq)
getSG_FLAG mr = liftM (getSG_FLAG_ 31) (getWord32 mr)
    where getSG_FLAG_ 0 word = []
          getSG_FLAG_ 1 word | testBit word 0 = SG_HIGHVM  : getSG_FLAG_ 0 word
          getSG_FLAG_ 3 word | testBit word 2 = SG_NORELOC : getSG_FLAG_ 2 word
          getSG_FLAG_ n word = getSG_FLAG_ (n-1) word

data MachoSection = MachoSection
    { sec_sectname    :: String        -- ^ name of section
    , sec_segname     :: String        -- ^ name of segment that should own this section
    , sec_addr        :: Word64        -- ^ virtual memoy address for section
    , sec_size        :: Word64        -- ^ size of section
    , sec_align       :: Int           -- ^ alignment required by section (literal form, not power of two, e.g. 8 not 3)
    , sec_relocs      :: [Relocation]  -- ^ relocations for this section
    , sec_type        :: S_TYPE        -- ^ type of section
    , sec_user_attrs  :: [S_USER_ATTR] -- ^ user attributes of section
    , sec_sys_attrs   :: [S_SYS_ATTR]  -- ^ system attibutes of section
    } deriving (Show, Eq)

getSection32 mr fl mh = do
    sectname  <- liftM (takeWhile (/= '\0') . C.unpack) $ getByteString 16
    segname   <- liftM (takeWhile (/= '\0') . C.unpack) $ getByteString 16
    addr      <- liftM fromIntegral $ getWord32 mr
    size      <- liftM fromIntegral $ getWord32 mr
    offset    <- liftM fromIntegral $ getWord32 mr
    align     <- liftM (2 ^) $ getWord32 mr
    reloff    <- liftM fromIntegral $ getWord32 mr
    nreloc    <- liftM fromIntegral $ getWord32 mr
    relocs    <- return $ runGet (sequence (replicate nreloc (getRel mr mh))) $ L.fromChunks [B.drop reloff fl]
    flags     <- getWord32 mr
    reserved1 <- getWord32 mr
    reserved2 <- getWord32 mr
    sectype   <- return $ sectionType flags
    userattrs <- return $ sectionUserAttribute flags
    sysattrs  <- return $ sectionSystemAttribute flags
    return MachoSection { sec_sectname   = sectname
                        , sec_segname    = segname
                        , sec_addr       = addr
                        , sec_size       = size
                        , sec_align      = align
                        , sec_relocs     = relocs
                        , sec_type       = sectype
                        , sec_user_attrs = userattrs
                        , sec_sys_attrs  = sysattrs }

getSection64 mr fl mh = do
    sectname  <- liftM (takeWhile (/= '\0') . C.unpack) $ getByteString 16
    segname   <- liftM (takeWhile (/= '\0') . C.unpack) $ getByteString 16
    addr      <- getWord64 mr
    size      <- getWord64 mr
    offset    <- getWord32 mr
    align     <- liftM (2 ^) $ getWord32 mr
    reloff    <- liftM fromIntegral $ getWord32 mr
    nreloc    <- liftM fromIntegral $ getWord32 mr
    relocs    <- return $ runGet (sequence (replicate nreloc (getRel mr mh))) $ L.fromChunks [B.drop reloff fl]
    flags     <- getWord32 mr
    reserved1 <- getWord32 mr
    reserved2 <- getWord32 mr
    reserved3 <- getWord32 mr
    sectype   <- return $ sectionType flags
    userattrs <- return $ sectionUserAttribute flags
    sysattrs  <- return $ sectionSystemAttribute flags
    return MachoSection { sec_sectname   = sectname
                        , sec_segname    = segname
                        , sec_addr       = addr
                        , sec_size       = size
                        , sec_align      = align
                        , sec_relocs     = relocs
                        , sec_type       = sectype
                        , sec_user_attrs = userattrs
                        , sec_sys_attrs  = sysattrs }

data S_TYPE
    = S_REGULAR                    -- ^ regular section
    | S_ZEROFILL                   -- ^ zero fill on demand section
    | S_CSTRING_LITERALS           -- ^ section with only literal C strings
    | S_4BYTE_LITERALS             -- ^ section with only 4 byte literals
    | S_8BYTE_LITERALS             -- ^ section with only 8 byte literals
    | S_LITERAL_POINTERS           -- ^ section with only pointers to literals
    | S_NON_LAZY_SYMBOL_POINTERS   -- ^ section with only non-lazy symbol pointers
    | S_LAZY_SYMBOL_POINTERS       -- ^ section with only lazy symbol pointers
    | S_SYMBOL_STUBS               -- ^ section with only symbol stubs, bte size of stub in the reserved2 field
    | S_MOD_INIT_FUNC_POINTERS     -- ^ section with only function pointers for initialization
    | S_MOD_TERM_FUNC_POINTERS     -- ^ section with only function pointers for termination
    | S_COALESCED                  -- ^ section contains symbols that are to be coalesced
    | S_GB_ZEROFILL                -- ^ zero fill on demand section (that can be larger than 4 gigabytes)
    | S_INTERPOSING                -- ^ section with only pairs of function pointers for interposing
    | S_16BYTE_LITERALS            -- ^ section with only 16 byte literals
    | S_DTRACE_DOF                 -- ^ section contains DTrace Object Format
    | S_LAZY_DYLIB_SYMBOL_POINTERS -- ^ section with only lazy symbol pointers to lazy loaded dylibs
    deriving (Show, Eq)
sectionType flags = case flags .&. 0x000000ff of
    0x00 -> S_REGULAR
    0x01 -> S_ZEROFILL
    0x02 -> S_CSTRING_LITERALS
    0x03 -> S_4BYTE_LITERALS
    0x04 -> S_8BYTE_LITERALS
    0x05 -> S_LITERAL_POINTERS
    0x06 -> S_NON_LAZY_SYMBOL_POINTERS
    0x07 -> S_LAZY_SYMBOL_POINTERS
    0x08 -> S_SYMBOL_STUBS
    0x09 -> S_MOD_INIT_FUNC_POINTERS
    0x0a -> S_MOD_TERM_FUNC_POINTERS
    0x0b -> S_COALESCED
    0x0c -> S_GB_ZEROFILL
    0x0d -> S_INTERPOSING
    0x0e -> S_16BYTE_LITERALS
    0x0f -> S_DTRACE_DOF
    0x10 -> S_LAZY_DYLIB_SYMBOL_POINTERS

data S_USER_ATTR
    = S_ATTR_PURE_INSTRUCTIONS   -- ^ section contains only true machine instructions
    | S_ATTR_NO_TOC              -- ^ setion contains coalesced symbols that are not to be in a ranlib table of contents
    | S_ATTR_STRIP_STATIC_SYMS   -- ^ ok to strip static symbols in this section in files with the MH_DYLDLINK flag
    | S_ATTR_NO_DEAD_STRIP       -- ^ no dead stripping
    | S_ATTR_LIVE_SUPPORT        -- ^ blocks are live if they reference live blocks
    | S_ATTR_SELF_MODIFYING_CODE -- ^ used with i386 code stubs written on by dyld
    | S_ATTR_DEBUG               -- ^ a debug section
    deriving (Show, Eq)
sectionUserAttribute flags = sectionUserAttribute_ 31 (flags .&. 0xff000000)
    where sectionUserAttribute_  0 flags = []
          sectionUserAttribute_ 31 flags | testBit flags 30 = S_ATTR_PURE_INSTRUCTIONS   : sectionUserAttribute_ 30 flags
          sectionUserAttribute_ 30 flags | testBit flags 29 = S_ATTR_NO_TOC              : sectionUserAttribute_ 29 flags
          sectionUserAttribute_ 29 flags | testBit flags 28 = S_ATTR_STRIP_STATIC_SYMS   : sectionUserAttribute_ 28 flags
          sectionUserAttribute_ 28 flags | testBit flags 27 = S_ATTR_NO_DEAD_STRIP       : sectionUserAttribute_ 27 flags
          sectionUserAttribute_ 27 flags | testBit flags 26 = S_ATTR_LIVE_SUPPORT        : sectionUserAttribute_ 26 flags
          sectionUserAttribute_ 26 flags | testBit flags 25 = S_ATTR_SELF_MODIFYING_CODE : sectionUserAttribute_ 25 flags
          sectionUserAttribute_  n flags = sectionUserAttribute_ (n-1) flags

data S_SYS_ATTR
    = S_ATTR_SOME_INSTRUCTIONS -- ^ section contains soem machine instructions
    | S_ATTR_EXT_RELOC         -- ^ section has external relocation entries
    | S_ATTR_LOC_RELOC         -- ^ section has local relocation entries
    deriving (Show, Eq)
sectionSystemAttribute flags = sectionSystemAttribute_ 31 (flags .&. 0x00ffff00)
    where sectionSystemAttribute_  0 flags = []
          sectionSystemAttribute_  8 flags | testBit flags 7 = S_ATTR_LOC_RELOC         : sectionSystemAttribute_  7 flags
          sectionSystemAttribute_  9 flags | testBit flags 8 = S_ATTR_EXT_RELOC         : sectionSystemAttribute_  8 flags
          sectionSystemAttribute_ 10 flags | testBit flags 9 = S_ATTR_SOME_INSTRUCTIONS : sectionSystemAttribute_  9 flags
          sectionSystemAttribute_  n flags = sectionSystemAttribute_ (n-1) flags

nullStringAt offset      = B.takeWhile ((/=) 0) . B.drop offset
substringAt  offset size = B.take size . B.drop offset
getLC_STR mr lc = do
    offset <- liftM fromIntegral $ getWord32 mr
    return $ C.unpack $ nullStringAt offset lc

getDylibCommand :: MachoReader -> B.ByteString -> (String -> Word32 -> Word32 -> Word32 -> LC_COMMAND) -> Get LC_COMMAND
getDylibCommand mr lc con = do
    name                  <- getLC_STR mr lc
    timestamp             <- getWord32 mr
    current_version       <- getWord32 mr
    compatibility_version <- getWord32 mr
    return $ con name timestamp current_version compatibility_version

getSubFrameworkCommand mr lc     = return LC_SUB_FRAMEWORK <*> getLC_STR mr lc
getSubClientCommand    mr lc     = return LC_SUB_CLIENT    <*> getLC_STR mr lc
getSubUmbrellaCommand  mr lc     = return LC_SUB_UMBRELLA  <*> getLC_STR mr lc
getSubLibraryCommand   mr lc     = return LC_SUB_LIBRARY   <*> getLC_STR mr lc
getDylinkerCommand     mr lc con = return con              <*> getLC_STR mr lc

getPreboundDylibCommand mr lc = do
    name           <- getLC_STR mr lc
    nmodules       <- liftM fromIntegral $ getWord32 mr
    modules_offset <- liftM fromIntegral $ getWord32 mr
    modules        <- return $ B.unpack $ B.take ((nmodules `div` 8) + (nmodules `mod` 8)) $ B.drop modules_offset lc
    return $ LC_PREBOUND_DYLIB name modules

getThreadCommand mr con = do
    let getThreadCommand_ mr = do
            empty <- isEmpty
            if empty then
                return []
                else do
                flavor <- getWord32 mr
                count  <- liftM fromIntegral $ getWord32 mr
                state  <- sequence (replicate count (getWord32 mr))
                rest   <- getThreadCommand_ mr
                return ((flavor, state) : rest)
    flavours <- getThreadCommand_ mr
    return $ con flavours

getRoutinesCommand32 mr = do
    init_address <- getWord32 mr
    init_module  <- getWord32 mr
    reserved1    <- getWord32 mr
    reserved2    <- getWord32 mr
    reserved3    <- getWord32 mr
    reserved4    <- getWord32 mr
    reserved5    <- getWord32 mr
    reserved6    <- getWord32 mr
    return $ LC_ROUTINES init_address init_module

getRoutinesCommand64 mr = do
    init_address <- getWord64 mr
    init_module  <- getWord64 mr
    reserved1    <- getWord64 mr
    reserved2    <- getWord64 mr
    reserved3    <- getWord64 mr
    reserved4    <- getWord64 mr
    reserved5    <- getWord64 mr
    reserved6    <- getWord64 mr
    return $ LC_ROUTINES_64 init_address init_module

data N_TYPE
    = N_UNDF       -- ^ undefined symbol, n_sect is 0
    | N_ABS        -- ^ absolute symbol, does not need relocation, n_sect is 0
    | N_SECT       -- ^ symbol is defined in section n_sect
    | N_PBUD       -- ^ symbol is undefined and the image is using a prebound value for the symbol, n_sect is 0
    | N_INDR       -- ^ symbol is defined to be the same as another symbol. n_value is a string table offset indicating the name of that symbol
    | N_GSYM       -- ^ stab global symbol: name,,0,type,0
    | N_FNAME      -- ^ stab procedure name (f77 kludge): name,,0,0,0
    | N_FUN        -- ^ stab procedure: name,,n_sect,linenumber,address
    | N_STSYM      -- ^ stab static symbol: name,,n_sect,type,address
    | N_LCSYM      -- ^ stab .lcomm symbol: name,,n_sect,type,address
    | N_BNSYM      -- ^ stab begin nsect sym: 0,,n_sect,0,address
    | N_OPT        -- ^ stab emitted with gcc2_compiled and in gcc source
    | N_RSYM       -- ^ stab register sym: name,,0,type,register
    | N_SLINE      -- ^ stab src line: 0,,n_sect,linenumber,address
    | N_ENSYM      -- ^ stab end nsect sym: 0,,n_sect,0,address
    | N_SSYM       -- ^ stab structure elt: name,,0,type,struct_offset
    | N_SO         -- ^ stab source file name: name,,n_sect,0,address
    | N_OSO        -- ^ stab object file name: name,,0,0,st_mtime
    | N_LSYM       -- ^ stab local sym: name,,0,type,offset
    | N_BINCL      -- ^ stab include file beginning: name,,0,0,sum
    | N_SOL        -- ^ stab #included file name: name,,n_sect,0,address
    | N_PARAMS     -- ^ stab compiler parameters: name,,0,0,0
    | N_VERSION    -- ^ stab compiler version: name,,0,0,0
    | N_OLEVEL     -- ^ stab compiler -O level: name,,0,0,0
    | N_PSYM       -- ^ stab parameter: name,,0,type,offset
    | N_EINCL      -- ^ stab include file end: name,,0,0,0
    | N_ENTRY      -- ^ stab alternate entry: name,,n_sect,linenumber,address
    | N_LBRAC      -- ^ stab left bracket: 0,,0,nesting level,address
    | N_EXCL       -- ^ stab deleted include file: name,,0,0,sum
    | N_RBRAC      -- ^ stab right bracket: 0,,0,nesting level,address
    | N_BCOMM      -- ^ stab begin common: name,,0,0,0
    | N_ECOMM      -- ^ stab end common: name,,n_sect,0,0
    | N_ECOML      -- ^ stab end common (local name): 0,,n_sect,0,address
    | N_LENG       -- ^ stab second stab entry with length information
    | N_PC         -- ^ stab global pascal symbol: name,,0,subtype,line
    deriving (Show, Eq)
n_type 0x00 = N_UNDF
n_type 0x01 = N_ABS
n_type 0x07 = N_SECT
n_type 0x06 = N_PBUD
n_type 0x05 = N_INDR
n_type 0x20 = N_GSYM
n_type 0x22 = N_FNAME
n_type 0x24 = N_FUN
n_type 0x26 = N_STSYM
n_type 0x28 = N_LCSYM
n_type 0x2e = N_BNSYM
n_type 0x3c = N_OPT
n_type 0x40 = N_RSYM
n_type 0x44 = N_SLINE
n_type 0x4e = N_ENSYM
n_type 0x60 = N_SSYM
n_type 0x64 = N_SO
n_type 0x66 = N_OSO
n_type 0x80 = N_LSYM
n_type 0x82 = N_BINCL
n_type 0x84 = N_SOL
n_type 0x86 = N_PARAMS
n_type 0x88 = N_VERSION
n_type 0x8A = N_OLEVEL
n_type 0xa0 = N_PSYM
n_type 0xa2 = N_EINCL
n_type 0xa4 = N_ENTRY
n_type 0xc0 = N_LBRAC
n_type 0xc2 = N_EXCL
n_type 0xe0 = N_RBRAC
n_type 0xe2 = N_BCOMM
n_type 0xe4 = N_ECOMM
n_type 0xe8 = N_ECOML
n_type 0xfe = N_LENG
n_type 0x30 = N_PC

data REFERENCE_FLAG
    = REFERENCE_FLAG_UNDEFINED_NON_LAZY          -- ^ reference to an external non-lazy symbol
    | REFERENCE_FLAG_UNDEFINED_LAZY              -- ^ reference to an external lazy symbol
    | REFERENCE_FLAG_DEFINED                     -- ^ symbol is defined in this module
    | REFERENCE_FLAG_PRIVATE_DEFINED             -- ^ symbol is defined in this module and visible only to modules within this shared library
    | REFERENCE_FLAG_PRIVATE_UNDEFINED_NON_LAZY  -- ^ reference to an external non-lazy symbol and visible only to modules within this shared library
    | REFERENCE_FLAG_PRIVATE_UNDEFINED_LAZY      -- ^ reference to an external lazy symbol and visible only to modules within this shared library
    | REFERENCED_DYNAMICALLY                     -- ^ set for all symbols referenced by dynamic loader APIs
    | N_WEAK_REF                                 -- ^ indicates the symbol is a weak reference, set to 0 if definition cannot be found
    | N_WEAK_DEF                                 -- ^ indicates the symbol is a weak definition, will be overridden by a strong definition at link-time
    | LIBRARY_ORDINAL Word16                     -- ^ for two-level mach-o objects, specifies the index of the library in which this symbol is defined. zero specifies current image.
    deriving (Show, Eq)
reference_flag_lo16 0 = REFERENCE_FLAG_UNDEFINED_NON_LAZY
reference_flag_lo16 1 = REFERENCE_FLAG_UNDEFINED_LAZY
reference_flag_lo16 2 = REFERENCE_FLAG_DEFINED
reference_flag_lo16 3 = REFERENCE_FLAG_PRIVATE_DEFINED
reference_flag_lo16 4 = REFERENCE_FLAG_PRIVATE_UNDEFINED_NON_LAZY
reference_flag_lo16 5 = REFERENCE_FLAG_PRIVATE_UNDEFINED_LAZY
reference_flag_hi16 word = reference_flag_hi16_ 16 word
    where reference_flag_hi16_ 0 word = []
          reference_flag_hi16_ 1 word | testBit word 0 = REFERENCED_DYNAMICALLY : reference_flag_hi16 0
          reference_flag_hi16_ 3 word | testBit word 2 = N_WEAK_REF             : reference_flag_hi16 1
          reference_flag_hi16_ 4 word | testBit word 3 = N_WEAK_DEF             : reference_flag_hi16 1
          reference_flag_hi16_ n word = reference_flag_hi16_ (n-1) word

reference_flags word mh =
    if MH_TWOLEVEL `elem` mh_flags mh then
        [reference_flag_lo16 (word .&. 0xf), LIBRARY_ORDINAL ((word .&. 0xf0) `shiftR` 16)]
    else
        reference_flag_lo16 (word .&. 0xf) : reference_flag_hi16 word

n_types n = if n .&. 0xe0 == 0 then
               let npext = n .&. 0x10 /= 0
                   ntype = n_type ((n .&. 0x0e) `shiftR` 1)
                   next  = n .&. 0x01 /= 0
               in (False, npext, ntype, next)
           else
               (True, False, n_type n, False)

data MachoSymbol = MachoSymbol
    { sym_name  :: String                         -- ^ symbol name
    , sym_type  :: N_TYPE                         -- ^ symbol type
    , sym_pext  :: Bool                           -- ^ true if limited global scope
    , sym_ext   :: Bool                           -- ^ true if external symbol
    , sym_sect  :: Word8                          -- ^ section index where the symbol can be found
    , sym_flags :: Either Word16 [REFERENCE_FLAG] -- ^ for stab entries, Left Word16 is the uninterpreted flags field, otherwise Right [REFERENCE_FLAG] are the symbol flags
    , sym_value :: Word64                         -- ^ symbol value, 32-bit symbol values are promoted to 64-bit for simpliciy
    } deriving (Show, Eq)

getSymbolName mr strsect = do
    offset <- liftM fromIntegral $ getWord32 mr
    return $ C.unpack $ C.takeWhile (/= '\0') $ B.drop offset strsect

getNList32 mr strsect mh = do
    n_name  <- getSymbolName mr strsect
    n_type  <- getWord8
    let (stabs, npext, ntype, next) = n_types n_type
    n_sect  <- getWord8
    n_desc  <- getWord16 mr
    let ref_flags = if stabs then
                        Left n_desc
                    else
                        Right $ reference_flags n_desc mh
    n_value <- liftM fromIntegral $ getWord32 mr
    return $ MachoSymbol n_name ntype npext next n_sect ref_flags n_value

getNList64 mr strsect mh = do
    n_name  <- getSymbolName mr strsect
    n_type  <- getWord8
    let (stabs, npext, ntype, next) = n_types n_type
    n_sect  <- getWord8
    n_desc  <- getWord16 mr
    let ref_flags = if stabs then
                        Left n_desc
                    else
                        Right $ reference_flags n_desc mh
    n_value <- getWord64 mr
    return $ MachoSymbol n_name ntype npext next n_sect ref_flags n_value

getSymTabCommand mr fl mh = do
    symoff  <- liftM fromIntegral $ getWord32 mr
    nsyms   <- liftM fromIntegral $ getWord32 mr
    stroff  <- liftM fromIntegral $ getWord32 mr
    strsize <- liftM fromIntegral $ getWord32 mr
    strsect <- return $ B.take strsize $ B.drop stroff fl
    symbols <- if is64bit mr then
                   return $ runGet (sequence (replicate nsyms (getNList64 mr strsect mh))) $ L.fromChunks [B.drop symoff fl]
               else
                   return $ runGet (sequence (replicate nsyms (getNList32 mr strsect mh))) $ L.fromChunks [B.drop symoff fl]
    return $ LC_SYMTAB symbols strsect

getTOC mr = do
    symbol_index <- getWord32 mr
    module_index <- getWord32 mr
    return (symbol_index, module_index)

data DylibModule = DylibModule
    { dylib_module_name_offset    :: Word32           -- ^ module name string table offset
    , dylib_ext_def_sym           :: (Word32, Word32) -- ^ (initial, count) pair of symbol table indices for externally defined symbols
    , dylib_ref_sym               :: (Word32, Word32) -- ^ (initial, count) pair of symbol table indices for referenced symbols
    , dylib_local_sym             :: (Word32, Word32) -- ^ (initial, count) pair of symbol table indices for local symbols
    , dylib_ext_rel               :: (Word32, Word32) -- ^ (initial, count) pair of symbol table indices for externally referenced symbols
    , dylib_init                  :: (Word32, Word32) -- ^ (initial, count) pair of symbol table indices for the index of the module init section and the number of init pointers
    , dylib_term                  :: (Word32, Word32) -- ^ (initial, count) pair of symbol table indices for the index of the module term section and the number of term pointers
    , dylib_objc_module_info_addr :: Word32           -- ^ statically linked address of the start of the data for this module in the __module_info section in the __OBJC segment
    , dylib_objc_module_info_size :: Word64           -- ^ number of bytes of data for this module that are used in the __module_info section in the __OBJC segment
    } deriving (Show, Eq)

getModule32 mr = do
    module_name           <- getWord32 mr
    iextdefsym            <- getWord32 mr
    nextdefsym            <- getWord32 mr
    irefsym               <- getWord32 mr
    nrefsym               <- getWord32 mr
    ilocalsym             <- getWord32 mr
    nlocalsym             <- getWord32 mr
    iextrel               <- getWord32 mr
    nextrel               <- getWord32 mr
    iinit_iterm           <- getWord32 mr
    iinit                 <- return (iinit_iterm .&. 0x0000ffff)
    iterm                 <- return $ (iinit_iterm .&. 0xffff0000) `shiftR` 16
    ninit_nterm           <- getWord32 mr
    ninit                 <- return (ninit_nterm .&. 0x0000ffff)
    nterm                 <- return $ (ninit_nterm .&. 0xffff0000) `shiftR` 16
    objc_module_info_addr <- getWord32 mr
    objc_module_info_size <- liftM fromIntegral $ getWord32 mr
    return DylibModule
        { dylib_module_name_offset    = module_name
        , dylib_ext_def_sym           = (iextdefsym, nextdefsym)
        , dylib_ref_sym               = (irefsym, nrefsym)
        , dylib_local_sym             = (ilocalsym, nlocalsym)
        , dylib_ext_rel               = (iextrel, nextrel)
        , dylib_init                  = (iinit, ninit)
        , dylib_term                  = (iterm, nterm)
        , dylib_objc_module_info_addr = objc_module_info_addr
        , dylib_objc_module_info_size = objc_module_info_size
        }

getModule64 mr = do
    module_name           <- getWord32 mr
    iextdefsym            <- getWord32 mr
    nextdefsym            <- getWord32 mr
    irefsym               <- getWord32 mr
    nrefsym               <- getWord32 mr
    ilocalsym             <- getWord32 mr
    nlocalsym             <- getWord32 mr
    iextrel               <- getWord32 mr
    nextrel               <- getWord32 mr
    iinit_iterm           <- getWord32 mr
    iinit                 <- return (iinit_iterm .&. 0x0000ffff)
    iterm                 <- return $ (iinit_iterm .&. 0xffff0000) `shiftR` 16
    ninit_nterm           <- getWord32 mr
    ninit                 <- return (ninit_nterm .&. 0x0000ffff)
    nterm                 <- return $ (ninit_nterm .&. 0xffff0000) `shiftR` 16
    objc_module_info_addr <- getWord32 mr
    objc_module_info_size <- getWord64 mr
    return DylibModule
        { dylib_module_name_offset    = module_name
        , dylib_ext_def_sym           = (iextdefsym, nextdefsym)
        , dylib_ref_sym               = (irefsym, nrefsym)
        , dylib_local_sym             = (ilocalsym, nlocalsym)
        , dylib_ext_rel               = (iextrel, nextrel)
        , dylib_init                  = (iinit, ninit)
        , dylib_term                  = (iterm, nterm)
        , dylib_objc_module_info_addr = objc_module_info_addr
        , dylib_objc_module_info_size = objc_module_info_size
        }

-- | Platform-specific relocation types.
data R_TYPE
    = GENERIC_RELOC_VANILLA
    | GENERIC_RELOC_PAIR
    | GENERIC_RELOC_SECTDIFF
    | GENERIC_RELOC_LOCAL_SECTDIFF
    | GENERIC_RELOC_PB_LA_PTR
    | X86_64_RELOC_BRANCH
    | X86_64_RELOC_GOT_LOAD
    | X86_64_RELOC_GOT
    | X86_64_RELOC_SIGNED
    | X86_64_RELOC_UNSIGNED
    | X86_64_RELOC_SUBTRACTOR
    | X86_64_RELOC_SIGNED_1
    | X86_64_RELOC_SIGNED_2
    | X86_64_RELOC_SIGNED_4
    | PPC_RELOC_VANILLA
    | PPC_RELOC_PAIR
    | PPC_RELOC_BR14
    | PPC_RELOC_BR24
    | PPC_RELOC_HI16
    | PPC_RELOC_LO16
    | PPC_RELOC_HA16
    | PPC_RELOC_LO14
    | PPC_RELOC_SECTDIFF
    | PPC_RELOC_LOCAL_SECTDIFF
    | PPC_RELOC_PB_LA_PTR
    | PPC_RELOC_HI16_SECTDIFF
    | PPC_RELOC_LO16_SECTDIFF
    | PPC_RELOC_HA16_SECTDIFF
    | PPC_RELOC_JBSR
    | PPC_RELOC_LO14_SECTDIFF
    deriving (Show, Eq)
r_type 0 CPU_TYPE_X86        = GENERIC_RELOC_VANILLA
r_type 1 CPU_TYPE_X86        = GENERIC_RELOC_PAIR
r_type 2 CPU_TYPE_X86        = GENERIC_RELOC_SECTDIFF
r_type 3 CPU_TYPE_X86        = GENERIC_RELOC_LOCAL_SECTDIFF
r_type 4 CPU_TYPE_X86        = GENERIC_RELOC_PB_LA_PTR
r_type 0 CPU_TYPE_X86_64     = X86_64_RELOC_UNSIGNED
r_type 1 CPU_TYPE_X86_64     = X86_64_RELOC_SIGNED
r_type 2 CPU_TYPE_X86_64     = X86_64_RELOC_BRANCH
r_type 3 CPU_TYPE_X86_64     = X86_64_RELOC_GOT_LOAD
r_type 4 CPU_TYPE_X86_64     = X86_64_RELOC_GOT
r_type 5 CPU_TYPE_X86_64     = X86_64_RELOC_SUBTRACTOR
r_type 6 CPU_TYPE_X86_64     = X86_64_RELOC_SIGNED_1
r_type 7 CPU_TYPE_X86_64     = X86_64_RELOC_SIGNED_2
r_type 8 CPU_TYPE_X86_64     = X86_64_RELOC_SIGNED_4
r_type 0 CPU_TYPE_POWERPC    = PPC_RELOC_VANILLA
r_type 1 CPU_TYPE_POWERPC    = PPC_RELOC_PAIR
r_type 2 CPU_TYPE_POWERPC    = PPC_RELOC_BR14
r_type 3 CPU_TYPE_POWERPC    = PPC_RELOC_BR24
r_type 4 CPU_TYPE_POWERPC    = PPC_RELOC_HI16
r_type 5 CPU_TYPE_POWERPC    = PPC_RELOC_LO16
r_type 6 CPU_TYPE_POWERPC    = PPC_RELOC_HA16
r_type 7 CPU_TYPE_POWERPC    = PPC_RELOC_LO14
r_type 8 CPU_TYPE_POWERPC    = PPC_RELOC_SECTDIFF
r_type 9 CPU_TYPE_POWERPC    = PPC_RELOC_PB_LA_PTR
r_type 10 CPU_TYPE_POWERPC   = PPC_RELOC_HI16_SECTDIFF
r_type 11 CPU_TYPE_POWERPC   = PPC_RELOC_LO16_SECTDIFF
r_type 12 CPU_TYPE_POWERPC   = PPC_RELOC_HA16_SECTDIFF
r_type 13 CPU_TYPE_POWERPC   = PPC_RELOC_JBSR
r_type 14 CPU_TYPE_POWERPC   = PPC_RELOC_LO14_SECTDIFF
r_type 15 CPU_TYPE_POWERPC   = PPC_RELOC_LOCAL_SECTDIFF
r_type 0 CPU_TYPE_POWERPC64  = PPC_RELOC_VANILLA
r_type 1 CPU_TYPE_POWERPC64  = PPC_RELOC_PAIR
r_type 2 CPU_TYPE_POWERPC64  = PPC_RELOC_BR14
r_type 3 CPU_TYPE_POWERPC64  = PPC_RELOC_BR24
r_type 4 CPU_TYPE_POWERPC64  = PPC_RELOC_HI16
r_type 5 CPU_TYPE_POWERPC64  = PPC_RELOC_LO16
r_type 6 CPU_TYPE_POWERPC64  = PPC_RELOC_HA16
r_type 7 CPU_TYPE_POWERPC64  = PPC_RELOC_LO14
r_type 8 CPU_TYPE_POWERPC64  = PPC_RELOC_SECTDIFF
r_type 9 CPU_TYPE_POWERPC64  = PPC_RELOC_PB_LA_PTR
r_type 10 CPU_TYPE_POWERPC64 = PPC_RELOC_HI16_SECTDIFF
r_type 11 CPU_TYPE_POWERPC64 = PPC_RELOC_LO16_SECTDIFF
r_type 12 CPU_TYPE_POWERPC64 = PPC_RELOC_HA16_SECTDIFF
r_type 13 CPU_TYPE_POWERPC64 = PPC_RELOC_JBSR
r_type 14 CPU_TYPE_POWERPC64 = PPC_RELOC_LO14_SECTDIFF
r_type 15 CPU_TYPE_POWERPC64 = PPC_RELOC_LOCAL_SECTDIFF

data Relocation
    = RelocationInfo
        { ri_address   :: Int32  -- ^ offset from start of section to place to be relocated
        , ri_symbolnum :: Word32 -- ^ index into symbol or section table
        , ri_pcrel     :: Bool   -- ^ indicates if the item to be relocated is part of an instruction containing PC-relative addressing
        , ri_length    :: Word32 -- ^ length of item containing address to be relocated (literal form (4) instead of power of two (2))
        , ri_extern    :: Bool   -- ^ indicates whether symbolnum is an index into the symbol table (True) or section table (False)
        , ri_type      :: R_TYPE -- ^ relocation type
        }
    | ScatteredRelocationInfo
        { rs_pcrel   :: Bool   -- ^ indicates if the item to be relocated is part of an instruction containing PC-relative addressing
        , rs_length  :: Word32 -- ^ length of item containing address to be relocated (literal form (4) instead of power of two (2))
        , rs_type    :: R_TYPE -- ^ relocation type
        , rs_address :: Word32 -- ^ offset from start of section to place to be relocated
        , rs_value   :: Int32  -- ^ address of the relocatable expression for the item in the file that needs to be updated if the address is changed
        }
    deriving (Show, Eq)

getRel mr mh = do
    r_address <- getWord32 mr
    r_value   <- getWord32 mr
    if (r_address .&. 0x80000000) /= 0 then do
        rs_pcrel   <- return $ bitfield mr 1 1 r_address == 1
        rs_length  <- return $ 2 ^ bitfield mr 2 2 r_address
        rs_type    <- return $ flip r_type (mh_cputype mh) $ bitfield mr 4 4 r_address
        rs_address <- return $ bitfield mr 8 24 r_address
        rs_value   <- return $ fromIntegral r_value
        return $ ScatteredRelocationInfo rs_pcrel rs_length rs_type rs_address rs_value
     else do
        ri_address   <- return $ fromIntegral r_address
        ri_symbolnum <- return $ bitfield mr 0 24 r_value
        ri_pcrel     <- return $ bitfield mr 24 1 r_value == 1
        ri_length    <- return $ 2 ^ bitfield mr  25 2 r_value
        ri_extern    <- return $ bitfield mr 27 1 r_value == 1
        ri_type      <- return $ flip r_type (mh_cputype mh) $ bitfield mr 28 4 r_value
        return $ RelocationInfo ri_address ri_symbolnum ri_pcrel ri_length ri_extern ri_type

data MachoDynamicSymbolTable = MachoDynamicSymbolTable
    { localSyms    :: (Word32, Word32)   -- ^ symbol table index and count for local symbols
    , extDefSyms   :: (Word32, Word32)   -- ^ symbol table index and count for externally defined symbols
    , undefSyms    :: (Word32, Word32)   -- ^ symbol table index and count for undefined symbols
    , tocEntries   :: [(Word32, Word32)] -- ^ list of symbol index and module index pairs
    , modules      :: [DylibModule]      -- ^ modules
    , extRefSyms   :: [Word32]           -- ^ list of external reference symbol indices
    , indirectSyms :: [Word32]           -- ^ list of indirect symbol indices
    , extRels      :: [Relocation]       -- ^ external locations
    , locRels      :: [Relocation]       -- ^ local relocations
    } deriving (Show, Eq)

getDySymTabCommand mr fl mh = do
    ilocalsym      <- getWord32 mr
    nlocalsym      <- getWord32 mr
    iextdefsym     <- getWord32 mr
    nextdefsym     <- getWord32 mr
    iundefsym      <- getWord32 mr
    nundefsym      <- getWord32 mr
    tocoff         <- liftM fromIntegral $ getWord32 mr
    ntoc           <- liftM fromIntegral $ getWord32 mr
    toc            <- return $ runGet (sequence (replicate ntoc (getTOC mr))) $ L.fromChunks [B.drop tocoff fl]
    modtaboff      <- liftM fromIntegral $ getWord32 mr
    nmodtab        <- liftM fromIntegral $ getWord32 mr
    modtab         <- if is64bit mr then
                          return $ runGet (sequence (replicate nmodtab (getModule64 mr))) $ L.fromChunks [B.drop modtaboff fl]
                      else
                          return $ runGet (sequence (replicate nmodtab (getModule32 mr))) $ L.fromChunks [B.drop modtaboff fl]
    extrefsymoff   <- liftM fromIntegral $ getWord32 mr
    nextrefsyms    <- liftM fromIntegral $ getWord32 mr
    extrefsyms     <- return $ runGet (sequence (replicate nextrefsyms (getWord32 mr))) $ L.fromChunks [B.drop extrefsymoff fl]
    indirectsymoff <- liftM fromIntegral $ getWord32 mr
    nindirectsyms  <- liftM fromIntegral $ getWord32 mr
    indirectsyms   <- return $ runGet (sequence (replicate nindirectsyms (getWord32 mr))) $ L.fromChunks [B.drop indirectsymoff fl]
    extreloff      <- liftM fromIntegral $ getWord32 mr
    nextrel        <- liftM fromIntegral $ getWord32 mr
    extrels        <- return $ runGet (sequence (replicate nextrel (getRel mr mh))) $ L.fromChunks [B.drop extreloff fl]
    locreloff      <- liftM fromIntegral $ getWord32 mr
    nlocrel        <- liftM fromIntegral $ getWord32 mr
    locrels        <- return $ runGet (sequence (replicate nlocrel (getRel mr mh))) $ L.fromChunks [B.drop locreloff fl]
    return $ LC_DYSYMTAB MachoDynamicSymbolTable
        { localSyms    = (ilocalsym, nlocalsym)
        , extDefSyms   = (iextdefsym, nextdefsym)
        , undefSyms    = (iundefsym, nundefsym)
        , tocEntries   = toc
        , modules      = modtab
        , extRefSyms   = extrefsyms
        , indirectSyms = indirectsyms
        , extRels      = extrels
        , locRels      = locrels
        }

getTwoLevelHint mr = do
    word <- getWord32 mr
    let isub_image = bitfield mr 0 8 word
        itoc       = bitfield mr 8 24 word
    return (isub_image, itoc)

getTwoLevelHintsCommand mr fl = do
    offset  <- liftM fromIntegral $ getWord32 mr
    nhints  <- liftM fromIntegral $ getWord32 mr
    return $ LC_TWOLEVEL_HINTS $ runGet (sequence (replicate nhints (getTwoLevelHint mr))) $ L.fromChunks [B.drop offset fl]

getPrebindCkSumCommand mr = do
    cksum <- getWord32 mr
    return $ LC_PREBIND_CKSUM cksum

getUUIDCommand mr = do
    uuid <- sequence $ replicate 8 getWord8
    return $ LC_UUID uuid

getRPathCommand mr lc = do
    name_offset           <- liftM fromIntegral $ getWord32 mr
    name                  <- return $ C.unpack $ nullStringAt name_offset lc
    return $ LC_RPATH name

getLinkEditCommand :: MachoReader -> B.ByteString -> (Word32 -> Word32 -> LC_COMMAND) -> Get LC_COMMAND
getLinkEditCommand mr lc con = do
    dataoff             <- getWord32 mr
    datasize            <- getWord32 mr
    return $ con dataoff datasize
