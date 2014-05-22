--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 19:02:05 EST 2014
--  Purpose  : Framework to optimise a single module
--  Copyright: © 2014 Peter Schachte.  All rights reserved.

module Optimise (optimiseModSCCBottomUp) where

import AST

-- For now, just a placeholder
optimiseModSCCBottomUp :: [ModSpec] -> Compiler ()
optimiseModSCCBottomUp mods = do
    mapM_ (optimiseModBottomUp mods) mods


optimiseModBottomUp :: [ModSpec] -> ModSpec -> Compiler ()
optimiseModBottomUp mods thisMod = do
    -- reenterModule thisMod
    -- -- First handle submodules
    -- submods <- getModuleImplementationField modSubmods
    -- -- liftIO $ putStrLn $ "getModuleImplementationField completed"
    -- let modspecs = Map.elems submods
    --   -- liftIO $ putStrLn $ "  Submodules: " ++ showModSpecs modspecs
    -- mapM_ (optimiseModBottomUp mods) modspecs
    -- procs <- getModuleImplementationField (Map.toList . modProcs)
    -- let ordered =
    --         stronglyConnComp
    --         [(pspec,pspec,
    --           nub $ concatMap (localBodyProcs thisMod . procBody) procs)
    --          | (name,procDefs) <- procs,
    --            (n,def) <- zip [1..] procDefs,
    --            let pspec = ProcSpec thisMod name n
    --          ]
    -- (changed,reasons) <-
    --     foldMChangeReasons (typecheckProcSCC thisMod modSCC) 
    --                        changed0 reasons0 ordered
    -- finishModule
    return ()