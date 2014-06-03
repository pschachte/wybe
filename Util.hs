--  File     : Util.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu May 22 14:43:47 2014
--  Purpose  : Various small utility functions
--  Copyright: © 2014 Peter Schachte.  All rights reserved.
--

module Util (checkMaybe, setMapInsert) where


import Data.Map as Map
import Data.Set as Set


-- | Test the value in a maybe, and if it fails, return Nothing.
checkMaybe :: (a -> Bool) -> Maybe a -> Maybe a
checkMaybe test Nothing = Nothing
checkMaybe test (Just val) = if test val then Just val else Nothing


-- |Insert an element into the set mapped to by the specified key in 
--  the given map.  Maps to a singleton set if there is no current 
--  mapping for the specified key.
setMapInsert :: (Ord a, Ord b) => a -> b -> Map a (Set b) -> Map a (Set b)
setMapInsert key item dict =
    Map.alter (\ms -> case ms of
                    Nothing -> Just $ Set.singleton item
                    Just s -> Just $ Set.insert item s)
    key dict