--  File     : LastUse.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri May 31 22:53:12 2013
--  Purpose  : Mark last use of each variable and remove unneeded parameters
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--

module LastUse (markLastUse) where

import AST
import Data.Set as Set
import Data.List as List
import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Monad

markLastUse :: ProcDef -> Compiler (ProcDef, Maybe ProcDef)
markLastUse (ProcDef nm proto@(PrimProto _ params) body pos tmp ccount vis) = do
    (body',needed) <- runStateT (bodyLastUse body) Set.empty
    return (ProcDef nm proto body' pos tmp ccount vis, Nothing)


----------------------------------------------------------------
--                       The NeededVars Monad
--
-- records the variables that will be used later in a proc definition 
-- as we process it from end to beginning. 
----------------------------------------------------------------

type NeededVars = StateT (Set PrimVarName)  Compiler


bodyLastUse :: ProcBody -> NeededVars ProcBody
bodyLastUse body = return body