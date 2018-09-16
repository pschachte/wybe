--  File     : Analysis.hs
--  Author   : Ting Lu
--  Origin   : Sun Sep 16 16:08:00 EST 2018
--  Purpose  : Entry point of all kinds of analysis for a single module
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.

module Analysis (analyseMod) where

import           AliasAnalysis
import           AST
import           Control.Monad
import           Data.Graph
import           Options       (LogSelection (Optimise))

analyseMod :: [SCC ProcSpec] -> Compiler ()
analyseMod = mapM_ aliasSccBottomUp
