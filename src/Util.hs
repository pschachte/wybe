--  File     : Util.hs
--  Author   : Peter Schachte
--  Purpose  : Various small utility functions
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Util (sameLength, maybeNth, setMapInsert,
             fillLines, nop, sccElts, DisjointSet,
             emptyDS, addOneToDS, unionTwoInDS,
             combineTwoDS, removeSingletonFromDS,
             addConnectedGroupToDS, removeOneFromDS,
             removeFromDS, connectedItemsInDS,
             mapDS, filterDS, dsToTransitivePairs,
             intersectMapIdentity) where


import           Data.Graph
import           Data.List    as List
import           Data.Map     as Map
import           Data.Map.Merge.Lazy (merge,dropMissing,zipWithMaybeMatched)
import           Data.Set     as Set
import           Data.Maybe   (isJust)
import           GHC.Generics (Generic)
import           Flow         ((|>))


-- |Do the the two lists have the same length?
sameLength :: [a] -> [b] -> Bool
sameLength [] [] = True
sameLength (_:as) (_:bs) = sameLength as bs
sameLength _ _ = False


-- |Return the nth element of the list, if present, else Nothing.
maybeNth :: (Eq n, Ord n, Num n) => n -> [a] -> Maybe a
maybeNth _ []     = Nothing
maybeNth 0 (e:_ ) = Just e
maybeNth n (_:es)
 | n > 0          = maybeNth (n - 1) es
 | otherwise      = Nothing


-- |Insert an element into the set mapped to by the specified key in
--  the given map.  Maps to a singleton set if there is no current
--  mapping for the specified key.
setMapInsert :: (Ord a, Ord b) => a -> b -> Map a (Set b) -> Map a (Set b)
setMapInsert key item dict =
    Map.alter (\ms -> case ms of
                    Nothing -> Just $ Set.singleton item
                    Just s -> Just $ Set.insert item s)
    key dict



-- |fillLines marginText currColumn lineLength text
--  Fill lines with text.  marginText is the string to start each
--  line but the first.  currColumn is the output column at the start
--  of the first word, and lineLength is the maximum line length.
fillLines :: String -> Int -> Int -> String -> String
fillLines marginText currColumn lineLength text =
    fillLines' marginText currColumn lineLength $ words text

fillLines' :: String -> Int -> Int -> [String] -> String
fillLines' marginText currColumn lineLength [] = []
fillLines' marginText currColumn lineLength [word] = word
fillLines' marginText currColumn lineLength (word1:word2:words) =
    let nextColumn = currColumn + length word1 + 1
    in  word1 ++
        if nextColumn + length word2 >= lineLength
        then "\n" ++ marginText ++
             fillLines' marginText (length marginText) lineLength (word2:words)
        else " " ++ fillLines' marginText nextColumn lineLength (word2:words)

-- |Do nothing monadically.
nop :: Monad m => m ()
nop = return ()


sccElts :: SCC a -> [a]
sccElts (AcyclicSCC single) = [single]
sccElts (CyclicSCC multi)   = multi


----------------------------------------------------------------
--
-- Disjoint set for alias map
--
----------------------------------------------------------------
-- TODO: Using Union-Find instead of this naive implementation
-- The old implement is wrong https://github.com/pschachte/wybe/issues/25
-- So we use this version as a quick fix.

type DisjointSet a = Set (Set a)

emptyDS = Set.empty


_findOneInSet :: (a -> Bool) -> Set a -> Maybe a
_findOneInSet f = 
    Set.foldr 
        (\x result -> 
            case result of
                Just _ -> result
                Nothing -> if f x then Just x else Nothing
            ) Nothing


addOneToDS :: Ord a => a -> DisjointSet a -> DisjointSet a
addOneToDS x ds = 
    case _findOneInSet (Set.member x) ds of
        Just _ -> ds
        Nothing -> 
            Set.insert (Set.singleton x) ds


addConnectedGroupToDS :: Ord a => [a] -> DisjointSet a -> DisjointSet a
addConnectedGroupToDS l ds = 
    case l of 
        [] -> ds
        x:xs -> 
            let ds' = addOneToDS x ds in
            List.foldl (flip (unionTwoInDS x)) ds' xs


unionTwoInDS :: Ord a => a -> a -> DisjointSet a -> DisjointSet a
unionTwoInDS x y ds = 
    let xSet = _findOneInSet (Set.member x) ds in 
    let ySet = _findOneInSet (Set.member y) ds in 
        if (isJust xSet) && (xSet == ySet)
        then ds
        else 
            let (ds', newSet') = case xSet of 
                    Nothing -> (ds, Set.singleton x)
                    Just xSet -> (Set.delete xSet ds, xSet)
            in
            let (ds'', newSet'') = case ySet of
                    Nothing -> (ds', Set.insert y newSet')
                    Just ySet -> (Set.delete ySet ds', Set.union newSet' ySet)
            in
                Set.insert newSet'' ds''


combineTwoDS :: Ord a => DisjointSet a -> DisjointSet a -> DisjointSet a
combineTwoDS =
    Set.foldr (\set ds -> addConnectedGroupToDS (Set.toList set) ds)


removeOneFromDS :: Ord a => a -> DisjointSet a -> DisjointSet a
removeOneFromDS x ds = 
    case _findOneInSet (Set.member x) ds of 
        Nothing -> ds
        Just xSet -> 
            let xSet' = Set.delete x xSet in
            let ds' = Set.delete xSet ds in
                if Set.null xSet' 
                    then ds'
                    else  Set.insert xSet' ds'


removeFromDS :: Ord a => Set a -> DisjointSet a -> DisjointSet a
removeFromDS set = 
    filterDS (\x -> not $ Set.member x set)


removeSingletonFromDS :: Ord a => DisjointSet a -> DisjointSet a
removeSingletonFromDS =
    Set.filter (\x -> Set.size x > 1)


-- return a set of items that the given item is connected to.
connectedItemsInDS :: Ord a => a -> DisjointSet a -> Set a
connectedItemsInDS x ds =
    case _findOneInSet (Set.member x) ds of 
        Nothing -> Set.empty
        Just xSet -> Set.delete x xSet


-- The map function must be a bijection, i.e. 1-to-1 mapping.
mapDS :: (Ord a, Ord b) => (a -> b) -> DisjointSet a -> DisjointSet b
mapDS f = 
    Set.map (Set.map f)


filterDS :: Ord a => (a -> Bool) -> DisjointSet a -> DisjointSet a
filterDS f ds =
    Set.map (Set.filter f) ds
    |> Set.filter (not . Set.null)


dsToTransitivePairs :: Ord a => DisjointSet a -> Set (a, a)
dsToTransitivePairs =
    Set.foldr
        (\singleSet result ->
            cartesianProduct singleSet singleSet
            |> Set.union result |> Set.filter (uncurry (<))
            ) Set.empty


-- | Intersect two maps keeping only mappings that are identical between the two
-- maps, eliminating any mappings that are not present in both and not identical
-- in both.
intersectMapIdentity :: (Ord k, Eq v) => Map k v -> Map k v -> Map k v
intersectMapIdentity = merge dropMissing dropMissing
                       (zipWithMaybeMatched
                        $ \_ v1 v2 -> if v1 == v2 then Just v1 else Nothing)
