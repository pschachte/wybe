--  File     : frgc.hs
--  Author   : Peter Schachte
--  Origin   : Sun Dec  4 18:39:16 2011
--  Purpose  : Frege compiler main code
--  Copyright: © 2011-2012 Peter Schachte.  All rights reserved.
--

module Main where

import Options
import Builder
import AST

main :: IO ()
main = do
    (opts, files) <- handleCmdline
    runCompiler opts (buildTargets opts files) 
