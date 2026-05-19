-- Count the number of characters, words, and lines coming from standard input.
-- This is a benchmark for I/O performance.

-- This implementation treats the input as a lazy stream of bytes, but handles
-- the counting eagerly, using a manual state machine.

import qualified Data.ByteString.Lazy as BL
import Data.Word (Word8)
import Data.List (foldl')

-- A simple record to hold our counts
data Stats =
    Stats { lines' :: !Int, words' :: !Int, bytes' :: !Int, beforeWord :: !Bool }

main :: IO ()
main = do
    input <- BL.getContents
    let initial = Stats 0 0 0 True
        final = BL.foldl' step initial input
    
    putStrLn $ show (lines' final) ++ " lines, " ++ 
               show (words' final) ++ " words, " ++ 
               show (bytes' final) ++ " bytes"

-- Manual state machine for wc-like behavior
step :: Stats -> Word8 -> Stats
step (Stats l w c bw) byte = 
    let isSp = byte == 32 || (byte >= 9 && byte <= 13)
        newL = if byte == 10 then l + 1 else l
        newW = if bw && not isSp then w + 1 else w
    in Stats newL newW (c + 1) isSp