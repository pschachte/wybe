--  File     : wybemk.hs
--  Author   : Peter Schachte
--  Purpose  : Wybe compiler/builder main code
--  Copyright: (c) 2011-2015 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

-- |The top level of the compiler.  Delegates the compilation process
--  to the Builder module.  The Options module handles the compiler
--  command line, and the AST module handles the abstract syntax tree
--  and program intermediate representation.


module Main where

import           AST
import           Builder
import           Control.Exception
import           Control.Monad
import           Options
import           System.Exit

-- |The main wybe compiler command line.
main :: IO ()
main = do
    (opts, files) <- handleCmdline
    catchAny
      (runCompiler opts (buildTargets files))
      -- if there's an exception, print to stdout
      -- XXX should probably go to stderr; but for now logging goes there
      (\e -> do
             let msg = show e
             when (msg /= "ExitFailure 1") $
                putStrLn msg
             exitFailure)


catchAny :: IO a -> (SomeException -> IO a) -> IO a
catchAny = Control.Exception.catch


testFile :: String -> IO ()
testFile file =
    runCompiler defaultOptions (buildTargets [file])
