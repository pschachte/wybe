--  File     : BodyBuilder.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Fri 22 May 2015 10:59:56 AEST
--  Purpose  : A monad to build up a procedure Body
--  Copyright: © 2015 Peter Schachte.  All rights reserved.
--

module BodyBuilder (BodyBuilder(..)) where

import AST
import Options (LogSelection(Expansion))
import Data.Map as Map
import Data.List as List
import Data.Set as Set
import Data.Maybe
import Control.Monad
import Control.Monad.Trans (lift,liftIO)
import Control.Monad.Trans.State

import Debug.Trace

----------------------------------------------------------------
--                       The BodyBuilder Monad
--
-- This monad keeps track of variable renaming needed to keep inlining
-- hygenic.  To do this, we rename all the input parameters of the proc to 
-- be inlined, and when expanding the body, we rename any variables when 
-- first assigned.  The exception to this is the proc's output parameters.  
-- These are kept as a set.  We also maintain a counter for temporary 
-- variable names.
----------------------------------------------------------------

data BodyBuilder = BodyBuilder {
    substitution :: Substitution,     -- ^The current variable substitution
    protected    :: Set PrimVarName,  -- ^Variables that cannot be renamed
    tmpCount     :: Int,              -- ^Next available tmp variable number
    finalFork    :: PrimFork,         -- ^The fork ending this body
    doInline     :: Bool,             -- ^Whether currently expanding inlined code
    doInlineFork :: Bool              -- ^Whether final fork is being inlined
    }


type Expander = StateT ExpanderState Compiler


