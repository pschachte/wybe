--  File     : Util.hs
--  RCS      : $Id$
--  Author   : Peter Schachte
--  Origin   : Thu May 22 14:43:47 2014
--  Purpose  : Various small utility functions
--  Copyright: (c) 2014 Peter Schachte.  All rights reserved.
--

{-# LANGUAGE DeriveGeneric #-}

module Util (sameLength, maybeNth, checkMaybe, setMapInsert,
             fillLines, nop, sccElts, reverseE,
             UnionFind, UFInfo, initUnionFind, newUfItem, addUfItem,
             connectedUf, uniteUf, convertUf, combineUf, filterUf) where


import           Data.Graph
import           Data.Map     as Map
import           Data.Set     as Set
import           GHC.Generics (Generic)


-- |Do the the two lists have the same length?
sameLength :: [a] -> [b] -> Bool
sameLength [] []         = True
sameLength (_:as) (_:bs) = sameLength as bs
sameLength _ _           = False


-- |Return the nth element of the list, if present, else Nothing.
maybeNth :: (Eq n, Ord n, Num n) => n -> [a] -> Maybe a
maybeNth _ []     = Nothing
maybeNth 0 (e:_ ) = Just e
maybeNth n (_:es)
 | n > 0          = maybeNth (n - 1) es
 | otherwise      = Nothing


-- |Test the value in a maybe, and if it fails, return Nothing.
checkMaybe :: (a -> Bool) -> Maybe a -> Maybe a
checkMaybe test Nothing    = Nothing
checkMaybe test (Just val) = if test val then Just val else Nothing


-- |Insert an element into the set mapped to by the specified key in
--  the given map.  Maps to a singleton set if there is no current
--  mapping for the specified key.
setMapInsert :: (Ord a, Ord b) => a -> b -> Map a (Set b) -> Map a (Set b)
setMapInsert key item dict =
    Map.alter (\ms -> case ms of
                    Nothing -> Just $ Set.singleton item
                    Just s  -> Just $ Set.insert item s)
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


-- King, D.J. and Launchbury, J., 1994, March. Lazy depth-first search and
-- linear graph algorithms in haskell. In Glasgow Workshop on Functional
-- Programming (pp. 145-155).
reverseE :: Graph -> [Edge]
reverseE g = [ (w,v) | (v,w) <- edges g]


-- Union Find implemented by Map
type UnionFind a = Map.Map a (UFInfo a)

data UFInfo a = UFInfo {
    root   :: a,
    weight :: Int
    } deriving (Eq, Generic)


instance Show a => Show (UFInfo a) where
    show (UFInfo root _) = show root


initUnionFind :: UnionFind a
initUnionFind = Map.empty


-- Insert new item with default UFInfo
newUfItem :: Ord a => a -> UnionFind a -> UnionFind a
newUfItem k = Map.insert k (UFInfo k 1)


addUfItem :: Ord a => a -> UFInfo a -> UnionFind a -> UnionFind a
addUfItem = Map.insert


connectedUf :: Ord a => UnionFind a -> a -> a -> Bool
connectedUf uf p q =
    let infoP = Map.lookup p uf
        infoQ = Map.lookup q uf
    in case (infoP, infoQ) of
        (Just ip, Just iq) -> root ip == root iq
        (_, _)             -> False


uniteUf :: Ord a => UnionFind a -> a -> a -> UnionFind a
uniteUf uf p q =
    case (infoP, infoQ) of
        (Just ip, Just iq) ->
            -- if root is the same between two existing UFInfo then no need to
            -- update anything
            if root ip == root iq then uf
            else updateUf p q ip iq uf
        (Just ip, _) ->
            -- Insert q to the map
            let iq = ufInfo q
                uf1 = Map.insert q iq uf
            in updateUf p q ip iq uf1
        (_, Just iq) ->
            -- Insert p to the map
            let ip = ufInfo p
                uf1 = Map.insert p ip uf
            in updateUf p q ip iq uf1
        (_, _) ->
            -- Insert both p and q to the map
            let ip = ufInfo p
                iq = ufInfo q
                uf1 = Map.insert p ip uf
                uf2 = Map.insert q iq uf1
            in updateUf p q ip iq uf2
    where
        infoP = Map.lookup p uf
        infoQ = Map.lookup q uf
        updateUf :: Ord a => a -> a -> UFInfo a -> UFInfo a -> UnionFind a
                                -> UnionFind a
        updateUf p q ip iq currMap =
            let rp = root ip
                rq = root iq
                currRootP = Map.lookup rp currMap
                currRootQ = Map.lookup rq currMap
            in case (currRootP, currRootQ) of
                (Just rootP, Just rootQ) ->
                    if weight rootP < weight rootQ then
                        let
                            -- update p's root to q's root
                            ip' = ip {root = rq}
                            -- append p's weight to q's root's weight
                            rootQ' = rootQ {weight = weight rootQ + weight ip}
                            currMap' = Map.insert p ip' currMap
                        in Map.insert rq rootQ' currMap'
                    else
                        let
                            -- update q's root to p's root
                            iq' = iq {root = rp}
                            -- append q's weight to p's root's weight
                            rootP' = rootP {weight = weight rootP + weight iq}
                            currMap' = Map.insert q iq' currMap
                        in Map.insert rp rootP' currMap'
                (_,_) -> currMap

-- Set default UFInfo that with root to itself and weight to 1
ufInfo :: a -> UFInfo a
ufInfo i = UFInfo i 1

-- Convert UnionFind map by mapping value with type 'a' to another value
convertUf :: (Ord a) => Map.Map a a -> a -> UFInfo a -> UnionFind a
                        -> UnionFind a
convertUf mp k info uf =
    case Map.lookup k mp of
        Just y ->
            let rootX = root info
                rootY = Map.lookup rootX mp
            in case rootY of
                Just rootY ->
                    addUfItem y info{root = rootY} uf
                _ -> uf
        _        -> uf


-- Combine two UnionFind
combineUf :: Ord a => UnionFind a -> UnionFind a -> UnionFind a
combineUf fromUf toUf =
    Map.foldrWithKey (\k info currUf ->
                        if k == root info then currUf
                        else uniteUf currUf k (root info)
                        ) toUf fromUf


-- Filter out UnionFind where key is not in the given list
filterUf :: (Ord a) => [a] -> a -> UFInfo a -> UnionFind a -> UnionFind a
filterUf ls k info uf = if k `elem` ls then Map.insert k info uf else uf


-- -- Reset key and value in UnionFind to default (so it's not connected to anyone)
-- resetUf :: (Ord a) => UnionFind a -> a -> UnionFind a
-- resetUf uf k = Map.insert k (ufInfo k) uf
