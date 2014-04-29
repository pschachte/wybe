--  File     : Normalise.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Tue Apr 29 19:02:05 EST 2014
--  Purpose  : Framework to optimise a single module
--  Copyright: © 2014 Peter Schachte.  All rights reserved.

module Optimise (optimise) where

import AST

-- For now, just a placeholder
optimise :: Module -> Compiler Module
optimise mod = return mod
