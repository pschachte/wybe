--  File     : ObjectInterface.hs
--  RCS      : $Id$
--  Author   : Ashutosh Rishi Ranjan
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Parse and edit a object file.
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.

module ObjectInterface where

import           AST
import Options (LogSelection(Builder))
import           BinaryFactory
import           Config
import           Control.Monad
import           Data.Binary
import           Data.Binary.Get
import           Data.Binary.Put
import qualified Data.ByteString as B
import           Data.ByteString.Builder
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as C
import           Data.Hex
import           Data.Int
import           Data.List as List
import           Data.Maybe (isJust)
import           Data.Word
import Data.Bits
import           System.Process
import           System.Directory          (createDirectoryIfMissing
                                           ,getTemporaryDirectory
                                           ,removeFile)
import System.FilePath (replaceExtension, takeBaseName)                 
import Control.Monad.Trans (liftIO)
import Macho


----------------------------------------------------------------------------
-- -- * Object file manipulation                                          --
----------------------------------------------------------------------------

-- | Use system `ld' to create a __lpvm section and put the given
-- 'BL.ByteString' into it.
-- ld reads the bs from a new tmpFile which is created with the contents
-- of the given 'BL.ByteString'.
insertLPVMDataLd :: BL.ByteString -> FilePath -> IO ()
insertLPVMDataLd bs obj =
    do tempDir <- getTemporaryDirectory
       liftIO $ createDirectoryIfMissing False (tempDir ++ "wybetemp")
       let modFile = takeBaseName obj ++ ".module"
       let lpvmFile = (tempDir ++ "wybetemp/" ++ modFile)
       BL.writeFile lpvmFile bs
       let args = [obj] ++ ["-r"] 
                  ++ ["-sectcreate", "__LPVM", "__lpvm", lpvmFile]
                  ++ ["-o", obj]
       createProcess (proc "ld" args)
       -- Cleanup
       return ()

-- | Extract string data from the segment __LPVM, section __lpvm of the
-- given object file. An empty string is returned if there is no data
-- in that section. The program 'otool' is used to read the object file.
extractLPVMData :: FilePath -> IO String
extractLPVMData obj =
    do let args = ["-s", "__LPVM", "__lpvm", obj]
       sout <- readProcess "otool" args []
       return $ parseSegmentData sout

-- | Parse the returned segment/section contents from it's HEX form to
-- ASCII form.
-- Sample:
-- "test-cases/foo.o:\nContents of (__LPVM,__lpvm) section
-- 0000000000000000    23 20 70 75 62 6c 69 63 20 66 75 6e ...
parseSegmentData :: String -> String
parseSegmentData str = concat hexLines
    where
      tillHex = dropWhile (\c -> c /= '\t') -- Actual data after \t
      mappedLines = List.map tillHex (lines str)
      filteredLines = List.filter (not . List.null) mappedLines
      hexLines = List.map (hex2char . tail) filteredLines

-- | Convert a string of 2 digit hex values to string of ascii
-- characters.
-- | Example: "23 20 70 75 62 6c 69 63" -> "# public"
hex2char :: String -> String
hex2char s = (concat . join) $ mapM unhex (words s)


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
  where remainder = (BL.length orig) `mod` 4

-- | Extract the wrapped bytestring from the given Wrapper Bitcode file
-- and de-serialise (decode) the bytestring as a AST.Module type.
extractModuleFromWrapper :: FilePath -> IO Module
extractModuleFromWrapper bcfile =
  do bc <- BL.readFile bcfile
     let dump = runGet dataFromBitcode bc
     return $ (decode dump :: Module)

-- | Run the Binary Get monad on a wrapped bitcode bytestring.
-- The wrapped bytestring exists between the header bytes and the bitcode
-- bytes. The header is of 20 bytes. The offset field in the header
-- (from the 9th byte), gives the offset of the bitcode.
dataFromBitcode :: Get BL.ByteString
dataFromBitcode = do
  skip 8
  offset <- getWord32le
  skip 8
  let datSize = (toInteger offset) - 20
  getLazyByteString (fromIntegral datSize)


-------------------------------------------------------------------------------
-- Segment Parsing and Extraction                                            --
-------------------------------------------------------------------------------


-- | Parse the given object file into a 'Macho' structure, determine the
-- offset and size of the '__lpvm' section data, and decode those bytes as
-- a 'AST.Module'.
machoLPVMSection :: FilePath -> Compiler [Module]
machoLPVMSection ofile =
    withMachoFile ofile [] decodeLPVMSegment


decodeLPVMSegment :: BL.ByteString -> Compiler [Module]
decodeLPVMSegment bs = do
    let (_, macho) = parseMacho (BL.toStrict bs)
    case findLPVMSegment (m_commands macho) of
        Just seg ->
            decodeModule $ uncurry (readBytes bs) (lpvmFileOffset seg)
        Nothing -> do
            logMsg Builder "No LPVM Segment found."
            return []
            

withMachoFile :: FilePath -> a -> (BL.ByteString -> Compiler a)
              -> Compiler a
withMachoFile mfile empty action = do
    bs <- liftIO $ BL.readFile mfile
    if isMachoBytes bs then action bs
        else do
        logMsg Builder $ "Not a recognised object file: "
            ++ mfile
        return empty
    

withMachoSegment :: MachoSegment -> (MachoSegment -> Compiler a) -> Compiler a
withMachoSegment with f = f with


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
        Nothing -> error "LPVM Section not found."


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
    
