--  File     : Resources.hs
--  Author   : Peter Schachte
--  Origin   : Sun Jan 15 16:00:18 2012
--  Purpose  : Resource checker for Wybe
--  Copyright: © 2012 Peter Schachte.  All rights reserved.

module Resources (resourceCheck) where

import AST
import Util
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Control.Monad.State
import Data.Maybe
import Data.Graph

import Debug.Trace

-- |Check use of resources in a single a single procedure definition,
-- updating parameters and body to thread extra arguments as needed.
resourceCheck :: ProcDef -> Compiler ProcDef
resourceCheck pd
    = return pd


resourceParams :: ResourceFlowSpec -> OptPos -> Compiler [Param]
resourceParams (ResourceFlowSpec res flow) pos = do
    maybeDef <- lookupResource res pos
    let var = resourceVar res
    case maybeDef of
        Nothing -> return []
        Just (SimpleResource typ _ _) ->
            return $
                  (if flowsIn flow
                   then [Param var typ ParamIn (Resource res)]
                   else []) ++
                  (if flowsOut flow
                   then [Param var typ ParamOut (Resource res)]
                   else [])
        Just (CompoundResource specs _) ->
            fmap concat $ mapM (\s -> resourceParams (ResourceFlowSpec s flow)
                                      pos)
                          specs


resourceVar :: ResourceSpec -> String
resourceVar (ResourceSpec mod name) = intercalate "." mod ++ name ++ "$"


