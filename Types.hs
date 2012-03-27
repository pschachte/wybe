--  File     : Types.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Type checker/inferencer for Frege
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

-- |Support type checking/inference.
module Types (typeCheck
             ) where

import AST
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.State

-- |Type check the current module.
typeCheck :: Compiler ()
typeCheck = do
    return ()
