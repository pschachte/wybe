-- Count the number of characters, words, and lines coming from standard input.
-- This is a benchmark for I/O performance.

-- This implementation uses the standard library functions 'lines' and 'words',
-- which are not the most efficient way to do this, but is idiomatic Haskell.

import Data.Char (isSpace)
import System.IO (hSetEncoding, stdin, latin1)


main :: IO ()
main = do
    -- Read the entire input from stdin lazily
    hSetEncoding stdin latin1 -- ignore UTF-8 decoding
    input <- getContents
    
    let lCount = length (lines input)
        wCount = length (words input)
        cCount = length input

    putStrLn $ show lCount ++ " lines, " ++ show wCount ++ " words, " ++ show cCount ++ " characters"