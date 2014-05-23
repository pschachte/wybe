--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 19:02:05 EST 2014
--  Purpose  : Framework to optimise a single module
--  Copyright: © 2014 Peter Schachte.  All rights reserved.

module Optimise (optimiseModSCCBottomUp) where

import AST
import Expansion
import Data.List as List
import Data.Map as Map
import Data.Graph

-- For now, just a placeholder
optimiseModSCCBottomUp :: [ModSpec] -> Compiler ()
optimiseModSCCBottomUp mods = do
    -- XXX Probably need to repeat this to a fixed point
    mapM_ (optimiseModBottomUp mods) mods


optimiseModBottomUp :: [ModSpec] -> ModSpec -> Compiler ()
optimiseModBottomUp mods thisMod = do
    reenterModule thisMod
    -- First handle submodules
    submods <- getModuleImplementationField modSubmods
    -- liftIO $ putStrLn $ "getModuleImplementationField completed"
    let modspecs = Map.elems submods
      -- liftIO $ putStrLn $ "  Submodules: " ++ showModSpecs modspecs
    mapM_ (optimiseModBottomUp mods) modspecs
    procs <- getModuleImplementationField (Map.toList . modProcs)
    let ordered =
            stronglyConnComp
            [(pspec,pspec,
              nub $ concatMap (localBodyCallees thisMod . procBody) procDefs)
             | (name,procDefs) <- procs,
               (n,def) <- zip [1..] procDefs,
               let pspec = ProcSpec thisMod name n
             ]
    mapM_ optimiseSCCBottomUp ordered
    finishModule
    return ()


optimiseSCCBottomUp :: SCC ProcSpec -> Compiler ()
optimiseSCCBottomUp (AcyclicSCC pspec) = do
    optimiseProc pspec
optimiseSCCBottomUp (CyclicSCC pspecs) = do
    mapM_ optimiseProc pspecs


optimiseProc :: ProcSpec -> Compiler ()
optimiseProc pspec = do
    updateProcDef (procExpansion identityExpansion) pspec


localBodyCallees :: ModSpec -> ProcBody -> [ProcSpec]
localBodyCallees modspec body =
    mapBodyPrims (localCallees modspec) (++) [] (++) [] body


localCallees :: ModSpec -> Prim -> [ProcSpec]
localCallees modspec (PrimCall m name (Just pspec) _)
    | m == modspec = [pspec]
localCallees _ _ = []

