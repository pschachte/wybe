--  File     : wybemk.hs
--  Author   : Peter Schachte
--  Origin   : Sun Dec  4 18:39:16 2011
--  Purpose  : Wybe compiler/builder main code
--  Copyright: © 2011-2012 Peter Schachte.  All rights reserved.
--

-- |The top level of the compiler.  Delegates the compilation process 
--  to the Builder module.
module Main where

import Options
import Builder
import AST

-- |The main wybe compiler command line.
main :: IO ()
main = do
    (opts, files) <- handleCmdline
    runCompiler opts (buildTargets opts files) 
