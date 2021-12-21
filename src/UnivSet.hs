--  File     : Util.hs
--  Author   : Peter Schachte
--  Purpose  : Provide a set type supporting the universal set.
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

{-# LANGUAGE DeriveGeneric #-}


module UnivSet (
    UnivSet(..), UnivSet.union, UnivSet.intersection, subtractUnivSet,
    UnivSet.member, isEmpty, isUniv, emptyUnivSet,
    UnivSet.fromList, UnivSet.toList, UnivSet.toSet,
    showUnivSet, showSet,
    mapFromUnivSetM
    ) where


import Data.Set as S
import Data.List
import Data.Map as M
import qualified GHC.IO.Buffer as S
import           GHC.Generics (Generic)
import qualified Data.Functor as UnivSet


----------------------------------------------------------------
--
-- A set type that supports a top (universal set) value, making this a lattice.
--
----------------------------------------------------------------

data UnivSet a = UniversalSet | FiniteSet (Set a) deriving (Show, Generic)


-- | Take the union of two UnivSets.
union :: Ord a => UnivSet a -> UnivSet a -> UnivSet a
union UniversalSet _ = UniversalSet
union _ UniversalSet = UniversalSet
union (FiniteSet s1) (FiniteSet s2) = FiniteSet $ s1 `S.union` s2


-- | Take the intersection of two UnivSets.
intersection :: Ord a => UnivSet a -> UnivSet a -> UnivSet a
intersection UniversalSet s = s
intersection s UniversalSet = s
intersection (FiniteSet s1) (FiniteSet s2) = FiniteSet $ s1 `S.intersection` s2


-- | Subtract the given UnivSet from an ordinary set.
subtractUnivSet :: Ord a => Set a -> UnivSet a -> Set a
subtractUnivSet _ UniversalSet    = S.empty
subtractUnivSet s1 (FiniteSet s2) = s1 S.\\ s2 


-- | Is the specified value a member of the given UnivSet?
member :: Ord a => a -> UnivSet a -> Bool
member elt UniversalSet = True
member elt (FiniteSet s) = elt `S.member` s


-- | Is the specified UnivSet empty?
isEmpty :: UnivSet a -> Bool
isEmpty UniversalSet = False
isEmpty (FiniteSet s) = S.null s


-- | Is the specified UnivSet universal?
isUniv :: UnivSet a -> Bool
isUniv UniversalSet = True
isUniv (FiniteSet s) = False


-- | The empty UnivSet
emptyUnivSet :: UnivSet a
emptyUnivSet = FiniteSet S.empty


-- | Make a finite UnivSet from a list of elements
fromList :: Ord a => [a] -> UnivSet a
fromList = FiniteSet . S.fromList


-- | Make a list from a finite UnivSet
toList :: [a] -> UnivSet a -> [a]
toList _   (FiniteSet set) = S.toList set
toList lst UniversalSet    = lst


-- | Make an ordinarly set from a UnivSet
toSet :: Ord a => Set a -> UnivSet a -> Set a
toSet _       (FiniteSet s) = s
toSet univSet UniversalSet  = univSet

-- | Nicely show a Maybe set, given the supplied fn to show each element.
-- Nothing is treated as signifying the universal set.
showUnivSet :: (a -> String) -> UnivSet a -> String
showUnivSet f UniversalSet = "Everything"
showUnivSet f (FiniteSet set) = showSet f set


-- | Nicely show a set, given the supplied fn to show each element
showSet :: (a -> String) -> Set a -> String
showSet showFn set =
    "{" ++ intercalate ", " (showFn <$> S.toList set) ++ "}"


-- | Produce a map from a UnivSet using a monadic mapping function.
mapFromUnivSetM :: (Monad m, Ord a) => (a -> m b) -> Set a -> UnivSet a
                -> m (Map a b)
mapFromUnivSetM f set uset = do
    let keys = S.toAscList $ toSet set uset
    M.fromAscList . zip keys <$> mapM f keys
