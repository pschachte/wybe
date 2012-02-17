--  File     : frgc.hs
--  Author   : Peter Schachte
--  Origin   : Sun Dec  4 18:39:16 2011
--  Purpose  : Frege compiler main code
--  Copyright: © 2011-2012 Peter Schachte.  All rights reserved.
--

module Main where

import Options
import Compiler

main :: IO ()
main = do
    (opts, files) <- handleCmdline
    mapM_ (makeTarget opts) files
