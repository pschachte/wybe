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
optimiseModSCCBottomUp mods = return ()
