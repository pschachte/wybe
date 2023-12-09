--  File     : ObjectInterface.hs
--  Author   : Ashutosh Rishi Ranjan, Modified by Zed(Zijun) Chen.
--  Purpose  : Parse and edit a object file.
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module ObjectInterface (extractLPVMData, getWrappedBitcode) where

import           AST
import Options (LogSelection(Builder))
import           BinaryFactory
import           Control.Monad
import           Data.Binary
import           Data.Binary.Get
import           Data.Binary.Put
import qualified Data.ByteString.Lazy as BL
import           Data.Int
import           Data.List as List
import           Data.Maybe (isJust)
import           Distribution.System       (buildOS, OS (..))
import           System.Exit               (ExitCode (..))
import           System.Process
import System.FilePath (takeBaseName, (</>))
import Control.Monad.Trans (liftIO)
import Macho

----------------------------------------------------------------------------
-- -- * Object file manipulation                                          --
----------------------------------------------------------------------------


-- | Extract LPVM data from the given object file
-- and return it as [BL.ByteString].
-- The first [FilePath] is for [tmpDir]
extractLPVMData :: FilePath -> FilePath -> IO (Either String BL.ByteString)
extractLPVMData tmpDir objFile =
    case buildOS of
        OSX   -> extractLPVMDataMacOS tmpDir objFile
        Linux -> extractLPVMDataLinux tmpDir objFile
        _     -> shouldnt "Unsupported operating system"

----------------------------------------------------------------------------
-- -- * Object file manipulation (Internal)                               --
----------------------------------------------------------------------------

-- | Actual implementation of [extractLPVMData] for macOS
extractLPVMDataMacOS :: FilePath -> FilePath -> IO (Either String BL.ByteString)
extractLPVMDataMacOS _ objFile = do
    objBS <- liftIO $ BL.readFile objFile
    if not $ isMachoBytes objBS
        then return $ Left ("Not a recognised object file: " ++ objFile)
        else do
            let (_, macho) = parseMacho (BL.toStrict objBS)
            case findLPVMSegment (m_commands macho) of
                Just seg -> do
                    -- liftIO $ putStr $ "\n\nParsed Mach-O segment:  " ++ show seg
                    let offset = lpvmFileOffset seg
                    -- liftIO $ putStr $ "\nLPVM Offset = " ++ show offset
                    let modBS = uncurry (readBytes objBS) offset
                    return $ Right modBS
                Nothing ->
                    return $ Left ("No LPVM Segment found in " ++ objFile)


-- | Actual implementation of [extractLPVMData] for Linux
-- Uses system [objcopy]
extractLPVMDataLinux :: FilePath -> FilePath -> IO (Either String BL.ByteString)
extractLPVMDataLinux tmpDir objFile = do
    let modFile = takeBaseName objFile ++ ".out.module"
    let lpvmFile = tmpDir </> modFile
    -- [objcopy] tries to write to the file even we only need read permission.
    -- We force it to write to /dev/null so it's "read-only".
    let args = ["--dump-section", "__LPVM.__lpvm=" ++ lpvmFile] ++ [objFile]
               ++ ["/dev/null"]
    (exCode, _, serr) <- readCreateProcessWithExitCode (proc "objcopy" args) ""
    case exCode of
        ExitSuccess  -> do
            modBS <- BL.readFile lpvmFile
            return $ Right modBS
        _  -> return $ Left serr

---------------------------------------------------------------------------------
-- Bitcode Wrapper Structure                                                   --
---------------------------------------------------------------------------------

makeBitcodeWrapper :: FilePath -> IO ()
makeBitcodeWrapper bcfile =
  do bc <- BL.readFile bcfile
     datStr <- BL.readFile "testFile"
     let wrapped = runPut $ wrapBitcode bc datStr
     BL.writeFile "dump" wrapped

getWrappedBitcode :: BL.ByteString -> BL.ByteString -> BL.ByteString
getWrappedBitcode bc datStr = runPut $ wrapBitcode bc datStr

-- | Bitcode Wrappper structure magic number.
magic :: Word32
magic = 0x0B17C0DE

-- | Put the Bitcode Bytes into a wrapper structure with an additional data
-- bytestring inserted in between. The header of such a wrapper looks like
-- this: [Magic32, Version32, Offset32, Size32, CPUType32] (little endian).
-- Succeeding the header, the data bytestring and ultimately the bitcode
-- bytestring is inserted.
wrapBitcode :: BL.ByteString     -- ^ Bitcode
            -> BL.ByteString     -- ^ Data Bytes to wrap along with bitcode
            -> Put
wrapBitcode bc datStr = do
  let bcsize = BL.length bc
  -- The length data bytestring to be wrapped should be a multiple of 4
  let paddedData = bytePad datStr
  let datsize = BL.length paddedData
  putWord32le magic             -- magic number
  putWord32le 0
  putWord32le (fromIntegral (20 + datsize) :: Word32)
  putWord32le (fromIntegral bcsize :: Word32)
  putWord32le 0
  putLazyByteString paddedData
  putLazyByteString bc

-- | Pad the bytestring with 0x00 bytes until it is of a length which is a
-- multiple of 4.
bytePad :: BL.ByteString -> BL.ByteString
bytePad orig = if remainder == 0
               then orig
               else BL.append orig (BL.replicate remainder 0)
  where remainder = BL.length orig `mod` 4

-- | Extract the wrapped bytestring from the given Wrapper Bitcode file
-- and de-serialise (decode) the bytestring as a AST.Module type.
extractModuleFromWrapper :: FilePath -> IO Module
extractModuleFromWrapper bcfile =
  do bc <- BL.readFile bcfile
     let dump = runGet dataFromBitcode bc
     return (decode dump :: Module)

-- | Run the Binary Get monad on a wrapped bitcode bytestring.
-- The wrapped bytestring exists between the header bytes and the bitcode
-- bytes. The header is of 20 bytes. The offset field in the header
-- (from the 9th byte), gives the offset of the bitcode.
dataFromBitcode :: Get BL.ByteString
dataFromBitcode = do
  skip 8
  offset <- getWord32le
  skip 8
  let datSize = toInteger offset - 20
  getLazyByteString (fromIntegral datSize)


-------------------------------------------------------------------------------
-- Segment Parsing and Extraction                                            --
-------------------------------------------------------------------------------

-- | Find the load command from a 'LC_COMMAND' list which contains
-- section '__lpvm'. This section will usually by in a general segment
-- load command (32 or 64 bit) of the Mach-O file.
findLPVMSegment :: [LC_COMMAND] -> Maybe MachoSegment
findLPVMSegment [] = Nothing
findLPVMSegment (LC_SEGMENT seg : cs) =
    if sectionExists "__lpvm" seg then Just seg else findLPVMSegment cs
findLPVMSegment (LC_SEGMENT_64 seg : cs) =
    if sectionExists "__lpvm" seg then Just seg else findLPVMSegment cs
findLPVMSegment (_:cs) = findLPVMSegment cs

-- | Check if a section of the given 'String' name exists in the
-- 'MachoSegment'.
sectionExists :: String -> MachoSegment -> Bool
sectionExists name seg =
    let sections = seg_sections seg
        found = List.find ((== name) . sec_sectname) sections
    in isJust found

-- | Determine the (offset, size) byte range where the __lpvm section data
-- exists. The offset is determined by adding the segment offset word of the
-- 'MachoSegment' (which contains the lpvm section) and the __lpvm section
-- offset word.
lpvmFileOffset :: MachoSegment -> (Int64, Int64)
lpvmFileOffset seg =
    let foff = seg_fileoff seg
        sections = seg_sections seg
    in case List.find ((== "__lpvm") . sec_sectname) sections of
        Just sec -> let off = fromIntegral $ foff + sec_addr sec
                        size = fromIntegral $ sec_size sec
                    in (off, size)
        Nothing -> shouldnt "LPVM Section not found."


-- | Read bytestring from 'BL.ByteString' in the given range.
readBytes :: BL.ByteString -> Int64 -> Int64 -> BL.ByteString
readBytes bs from size = BL.take size $ BL.drop from bs



-----------------------------------------------------------------------------
-- File Helpers                                                            --
-----------------------------------------------------------------------------


isValidLPVMBytes :: BL.ByteString -> Maybe BL.ByteString
isValidLPVMBytes bs = do
    (hd, tl) <- BL.uncons bs
    if hd == (1 :: Word8) then Just tl else Nothing



-- | Checks the magic number of the given bytestring [bs] to determine whether
-- it is a parasable Macho bytestring or not.
isMachoBytes :: BL.ByteString -> Bool
isMachoBytes bs = flip runGet bs $ do
    word <- getWord32le
    return $ List.elem word [ 0xfeedface
                            , 0xfeedfacf
                            , 0xcefaedfe
                            , 0xcffaedfe ]
