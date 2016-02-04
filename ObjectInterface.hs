--  File     : ObjectInterface.hs
--  RCS      : $Id$
--  Author   : Ashutosh Rishi Ranjan
--  Origin   : Thu Mar 26 14:25:37 AEDT 2015
--  Purpose  : Parse and edit a object file.
--  Copyright: (c) 2015 Peter Schachte.  All rights reserved.

module ObjectInterface where

import           Config
import           Control.Monad
import qualified Data.ByteString as B
import           Data.Hex
import           Data.List as List
import           Data.Macho
import           Data.Maybe (isJust)
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
-- 0000000000000000    23 20 70 75 62 6c 69 63 20 66 75 6e 63 20 74 6f ...
parseSegmentData :: String -> String
parseSegmentData str = concat hexLines
    where
      tillHex = dropWhile (\c -> c /= '\t') -- Actual data after \t 
      mappedLines = List.map tillHex (lines str)
      filteredLines = List.filter (not . List.null) mappedLines
      hexLines = List.map (hex2char . tail) filteredLines

-- | Convert a string of 2 digit hex values to string of ascii characters.
-- | Example: "23 20 70 75 62 6c 69 63" -> "# public"
hex2char :: String -> String
hex2char s = (concat . join) $ mapM unhex (words s)
