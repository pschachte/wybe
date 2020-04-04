--  File     : Analysis.hs
--  Author   : Ting Lu
--  Purpose  : Entry point of all kinds of analysis for a single module
--  Copyright: (c) 2018 Ting Lu.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Analysis (analyseMod) where

import           AliasAnalysis (aliasSccBottomUp,
                                currentAliasInfo,
                                isAliasInfoChanged)
import           AST
import           Callers       (getSccProcs)
import           Control.Monad
import           Data.List     as List
import           Data.Map      as Map
import           Data.Set      as Set
import           Options       (LogSelection (Analysis))
import           Util


analyseMod :: [ModSpec] -> ModSpec -> Compiler (Bool,[(String,OptPos)])
analyseMod _ thisMod = do
    reenterModule thisMod
    orderedProcs <- getSccProcs thisMod

    -- Some logging
    logAnalysis $ replicate 60 '='
    logAnalysis $ "analyseMod:" ++ show thisMod
    logAnalysis $ ">>> orderedProcs:" ++ show orderedProcs
    logAnalysis $ ">>> Analyse SCCs: \n" ++
        unlines (List.map ((++) "    " . show . sccElts) orderedProcs)
    logAnalysis $ replicate 60 '='

    ----------------------------------
    -- ALIAS ANALYSIS
    -- MODULE LEVEL ALIAS ANALYSIS
    aliasingInfos1 <- foldM (\list procs -> do
        aliasInfo <- currentAliasInfo procs
        return $ list ++ aliasInfo) [] orderedProcs

    mapM_ aliasSccBottomUp orderedProcs

    aliasingInfos2 <- foldM (\list procs -> do
        aliasInfo <- currentAliasInfo procs
        return $ list ++ aliasInfo) [] orderedProcs
    let chg = List.zipWith isAliasInfoChanged aliasingInfos1 aliasingInfos2

    logAnalysis $ replicate 60 '>'
    logAnalysis $ "Check aliasing for module: " ++ show thisMod
    logAnalysis $ "Module's procs alias info (old): " ++ show aliasingInfos1
    logAnalysis $ "Module's procs alias info (new): " ++ show aliasingInfos2
    logAnalysis $ "Changes: " ++ show chg
    logAnalysis $ "Module level alias changed? " ++ show (or chg)
    logAnalysis $ replicate 60 '>'

    _ <- reexitModule
    return (or chg,[])


-- |Log a message, if we are logging optimisation activity.
logAnalysis :: String -> Compiler ()
logAnalysis = logMsg Analysis
