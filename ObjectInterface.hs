--  File     : ObjectInterface.hs
--  RCS      : $Id$
--  Author   : Ashutosh Rishi Ranjan
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Parse and edit a object file.
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.

module ObjectInterface where

import           AST
import           BinaryFactory
import           Config
import           Control.Monad
import           Data.Binary
import           Data.Binary.Get
import           Data.Binary.Put
import qualified Data.ByteString as B
import           Data.ByteString.Builder
import qualified Data.ByteString.Lazy as BL
import           Data.Hex
import           Data.Int
import           Data.List as List
import           Data.Macho
import           Data.Maybe (isJust)
import           Data.Monoid
import           Data.Word
import           System.Process

getMachoRecord :: FilePath -> IO Macho
getMachoRecord ofile =
  do bs <- B.readFile ofile
     return $ parseMacho bs


listSegments :: FilePath -> IO ()
listSegments ofile = do
  m <-getMachoRecord ofile
  let names = segmentNames (m_commands m)
  putStrLn (show names)

segmentNames :: [LC_COMMAND] -> [String]
segmentNames [] = [] 
segmentNames ((LC_SEGMENT seg):cs) = (seg_segname seg) : segmentNames cs
segmentNames ((LC_SEGMENT_64 seg):cs) = (seg_segname seg) : segmentNames cs
segmentNames (_:cs) = segmentNames cs

----------------------------------------------------------------------------
-- -- * Object file manipulation                                          --
----------------------------------------------------------------------------

-- | Insert string data from first file into the second object file, into
-- the segment '__LPVM', and section '__lpvm' using ld.
insertLPVMData :: FilePath -> FilePath -> IO ()
insertLPVMData datfile obj =
    do let args = ["-r"] ++ ldSystemArgs
                  ++ ["-sectcreate", "__LPVM", "__lpvm", datfile]
                  ++ ["-o", obj]
       createProcess (proc "ld" args)
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
     print $ BL.length dump
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
  
  
