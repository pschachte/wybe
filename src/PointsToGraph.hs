--  File     : PointsToGraph.hs
--  Author   : Saumitra Lohokare
--  Purpose  : Field- and direction-sensitive Points-To Graph (Andersen-style)
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.
--
--  This module defines the intraprocedural Points-To Graph (PTG) that replaces
--  the Steensgaard/union-find alias representation.
--
--  MILESTONE 1 (scaffold): this module provides the data types and the pure
--  graph operations only.  It is deliberately NOT wired into AliasAnalysis /
--  Transform / AST yet -- that is Milestone 2 onwards.  The types and helpers
--  here are the building blocks the transfer function and queries will compose.
--
--  NOTE on FieldKey / EscapeState: for this scaffold they live here.  In
--  Milestone 3 (when the serialized interprocedural summary ProcPTGSummary is
--  introduced in AST.hs) FieldKey and EscapeState move to AST.hs and this
--  module imports them, because AST.hs cannot import PointsToGraph (PointsToGraph
--  imports AST) without an import cycle.

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module PointsToGraph (
    -- * Core types
    NodeOrigin(..), Node(..), FieldKey(..), EscapeState(..), PointsToGraph(..),
    -- * Construction / lookup
    emptyPTG, varNodes, setVarNodes, addVarNodes, dropVars,
    freshLocalNode, nodeOrigin,
    -- * Directional copy (Andersen inclusion)
    copyVar,
    -- * Field edges (field-sensitive, with FieldAny fallback)
    keyOfOffset, readField, writeField,
    -- * Escape
    joinEscape, escapeOf, raiseEscape, raiseEscapeReachable,
    -- * Reachability / queries support
    reachableNodes, originsOf, varsReferencing,
    -- * Merge (fork / call combine)
    joinPTG
    ) where

import           AST         (PrimVarName, GlobalInfo, StructID, ParameterID)
import           Data.Map    (Map)
import qualified Data.Map    as Map
import           Data.Set    (Set)
import qualified Data.Set    as Set
import           Flow        ((|>))
import           GHC.Generics (Generic)


-- | Origin and identity of an abstract memory node.  The origin drives escape
-- classification: LocalNode is a candidate to be captured (stack-allocatable),
-- while ParamNode/ReturnNode/GlobalNode are visible outside the procedure.
data NodeOrigin
    = LocalNode  PrimVarName   -- ^ born at an `lpvm alloc`, keyed by its SSA out-var
    | ParamNode  ParameterID   -- ^ external node reachable from a formal parameter
    | ReturnNode ParameterID   -- ^ external node written to an output parameter
    | GlobalNode GlobalInfo    -- ^ a resource / global sink (always escaping)
    | ConstNode  StructID      -- ^ a constant memory block (ArgConstRef)
    deriving (Eq, Ord, Show, Generic)


-- | An abstract memory node.  A newtype over its origin so that node identity is
-- exactly its origin (allocation-site abstraction: one node per alloc site /
-- param / return / global / const).
newtype Node = Node NodeOrigin
    deriving (Eq, Ord, Show, Generic)


-- | A field selector.  LPVM addresses fields by byte offset, almost always a
-- compile-time constant (`Field k`).  A non-constant offset (e.g. a dynamic
-- array index) collapses to `FieldAny`, the sound field-insensitive fallback
-- (see readField / writeField for its fan-out / gather semantics).
data FieldKey
    = Field !Int   -- ^ a constant byte offset
    | FieldAny     -- ^ unknown offset: the catch-all, a supertype of every Field
    deriving (Eq, Ord, Show, Generic)


-- | Escape lattice (Choi et al.).  The derived Ord gives the lattice order
-- NoEscape < ArgEscape < GlobalEscape, so the join (least upper bound) is `max`
-- and escape can only ever grow.  NoEscape is the optimistic starting point.
data EscapeState
    = NoEscape      -- ^ provably local; safe to stack-allocate
    | ArgEscape     -- ^ escapes only to the caller's frame (via return/out-param)
    | GlobalEscape  -- ^ globally reachable
    deriving (Eq, Ord, Show, Generic)


-- | The intraprocedural Points-To Graph.
--
--   * 'ptgEnv'    maps each variable to the set of nodes it may point to.
--   * 'ptgEdges'  maps each (node, field) to the set of nodes that field may
--                 point to -- the (node, field-offset) key IS the field
--                 sensitivity.
--   * 'ptgEscape' records the escape state of each node (absent = 'NoEscape').
--   * 'ptgMaybeAliasParams' are the parameters whose external aliasing is still
--                 unknown; they are the source of the `requiredParams` that
--                 `isArgUnaliased` reports (feeding multi-specialization).
data PointsToGraph = PointsToGraph
    { ptgEnv              :: Map PrimVarName (Set Node)
    , ptgEdges            :: Map Node (Map FieldKey (Set Node))
    , ptgEscape           :: Map Node EscapeState
    , ptgMaybeAliasParams :: Set ParameterID
    } deriving (Eq, Ord, Show, Generic)


----------------------------------------------------------------
-- Construction / lookup
----------------------------------------------------------------

-- | The empty graph.
emptyPTG :: PointsToGraph
emptyPTG = PointsToGraph Map.empty Map.empty Map.empty Set.empty


-- | The nodes a variable may point to (empty if unknown).
varNodes :: PointsToGraph -> PrimVarName -> Set Node
varNodes ptg v = Map.findWithDefault Set.empty v (ptgEnv ptg)


-- | Set a variable's points-to set, replacing any previous binding.
setVarNodes :: PrimVarName -> Set Node -> PointsToGraph -> PointsToGraph
setVarNodes v ns ptg = ptg { ptgEnv = Map.insert v ns (ptgEnv ptg) }


-- | Add nodes to a variable's points-to set (union with any existing binding).
addVarNodes :: PrimVarName -> Set Node -> PointsToGraph -> PointsToGraph
addVarNodes v ns ptg =
    ptg { ptgEnv = Map.insertWith Set.union v ns (ptgEnv ptg) }


-- | Remove a set of (dead) variables from the environment.  Nodes and edges are
-- retained -- they are the persistent aliasing substrate -- only the var->node
-- bindings go.  Mirrors the old `removeDeadVar`.
dropVars :: Set PrimVarName -> PointsToGraph -> PointsToGraph
dropVars vs ptg =
    ptg { ptgEnv = Map.filterWithKey (\v _ -> not (Set.member v vs)) (ptgEnv ptg) }


-- | Create a fresh 'LocalNode' for an `lpvm alloc` output variable: bind the
-- variable to the new node (replacing any prior binding, since SSA guarantees a
-- single definition), give the node an empty field map and 'NoEscape'.  Returns
-- the node and the updated graph.
freshLocalNode :: PrimVarName -> PointsToGraph -> (Node, PointsToGraph)
freshLocalNode out ptg =
    let n    = Node (LocalNode out)
        ptg' = ptg { ptgEnv    = Map.insert out (Set.singleton n) (ptgEnv ptg)
                   , ptgEdges  = Map.insertWith (\_ old -> old) n Map.empty
                                     (ptgEdges ptg)
                   , ptgEscape = Map.insertWith (\_ old -> old) n NoEscape
                                     (ptgEscape ptg) }
    in (n, ptg')


-- | Unwrap a node to its origin.
nodeOrigin :: Node -> NodeOrigin
nodeOrigin (Node o) = o


----------------------------------------------------------------
-- Directional copy (Andersen inclusion)
----------------------------------------------------------------

-- | Andersen copy for a value-preserving assignment `dst = src`:
-- @pts(dst) ⊇ pts(src)@.  Direction-sensitive: @src@ does not acquire @dst@'s
-- other pointees.  Used for `llvm move` and `lpvm cast`.
copyVar :: PrimVarName -> PrimVarName -> PointsToGraph -> PointsToGraph
copyVar dst src ptg = addVarNodes dst (varNodes ptg src) ptg


----------------------------------------------------------------
-- Field edges
----------------------------------------------------------------

-- | Turn a (maybe-constant) byte offset into a 'FieldKey'.  A known constant
-- offset becomes 'Field'; anything else becomes 'FieldAny'.
keyOfOffset :: Maybe Int -> FieldKey
keyOfOffset (Just k) = Field k
keyOfOffset Nothing  = FieldAny


-- | Read a field of a node.  Returns the field's own pointees unioned with the
-- 'FieldAny' bucket (an earlier unknown-offset write may have landed there);
-- and, when reading through 'FieldAny', the union over ALL of the node's field
-- buckets.  This is the sound gather semantics for the field-insensitive
-- fallback (Balatsouras-Smaragdakis generalization order).
readField :: PointsToGraph -> Node -> FieldKey -> Set Node
readField ptg n key =
    let fields  = Map.findWithDefault Map.empty n (ptgEdges ptg)
        anyBkt  = Map.findWithDefault Set.empty FieldAny fields
    in case key of
        FieldAny -> Map.foldr Set.union Set.empty fields
        Field _  -> Set.union (Map.findWithDefault Set.empty key fields) anyBkt


-- | Write into a field of a node: @writeField n key S@ adds @S@ to the field's
-- pointees.  When writing through 'FieldAny', the values fan out into every
-- existing field bucket of the node AND the 'FieldAny' bucket, so a later read
-- of any specific field still sees them.
writeField :: Node -> FieldKey -> Set Node -> PointsToGraph -> PointsToGraph
writeField n key ns ptg
    | Set.null ns = ptg
    | otherwise   =
        let fields  = Map.findWithDefault Map.empty n (ptgEdges ptg)
            fields' = case key of
                FieldAny ->
                    -- fan out into all existing buckets + the FieldAny bucket
                    Map.insertWith Set.union FieldAny ns
                        (Map.map (Set.union ns) fields)
                Field _  ->
                    Map.insertWith Set.union key ns fields
        in ptg { ptgEdges = Map.insert n fields' (ptgEdges ptg) }


----------------------------------------------------------------
-- Escape
----------------------------------------------------------------

-- | Lattice join of two escape states (the more-escaping wins).
joinEscape :: EscapeState -> EscapeState -> EscapeState
joinEscape = max


-- | The escape state of a node (absent = 'NoEscape').
escapeOf :: PointsToGraph -> Node -> EscapeState
escapeOf ptg n = Map.findWithDefault NoEscape n (ptgEscape ptg)


-- | Raise the escape state of a set of nodes to at least the given state.
raiseEscape :: EscapeState -> Set Node -> PointsToGraph -> PointsToGraph
raiseEscape st ns ptg =
    ptg { ptgEscape =
            Set.foldr (\n -> Map.insertWith joinEscape n st) (ptgEscape ptg) ns }


-- | Raise the escape state of a set of nodes AND every node forward-reachable
-- from them (through 'ptgEdges').  This is what a global store / opaque-call
-- argument does: the escape taints everything reachable.
raiseEscapeReachable :: EscapeState -> Set Node -> PointsToGraph -> PointsToGraph
raiseEscapeReachable st ns ptg = raiseEscape st (reachableNodes ptg ns) ptg


----------------------------------------------------------------
-- Reachability / query support
----------------------------------------------------------------

-- | The set of nodes forward-reachable from a set of roots, following every
-- field edge (field-sensitively -- all buckets).  Includes the roots.
reachableNodes :: PointsToGraph -> Set Node -> Set Node
reachableNodes ptg = go Set.empty
  where
    go seen frontier
        | Set.null frontier = seen
        | otherwise =
            let seen'    = Set.union seen frontier
                nexts    = frontier
                            |> Set.toList
                            |> concatMap successors
                            |> Set.fromList
                frontier' = Set.difference nexts seen'
            in go seen' frontier'
    successors n =
        Map.findWithDefault Map.empty n (ptgEdges ptg)
        |> Map.elems
        |> Set.unions
        |> Set.toList


-- | The origins of a set of nodes.
originsOf :: Set Node -> Set NodeOrigin
originsOf = Set.map nodeOrigin


-- | The variables whose points-to set intersects the given node set -- i.e. the
-- variables that (may) refer to any of those nodes.  Used by the alias queries
-- to find what a value is co-referenced with.
varsReferencing :: PointsToGraph -> Set Node -> Set PrimVarName
varsReferencing ptg ns =
    ptgEnv ptg
    |> Map.filter (not . Set.null . Set.intersection ns)
    |> Map.keysSet


----------------------------------------------------------------
-- Merge
----------------------------------------------------------------

-- | Merge two graphs (least upper bound), used to combine fork branches and to
-- fold in a callee summary's effect.  Environments and edges are unioned
-- pointwise; escape states are joined with 'max'; maybe-alias params are unioned.
joinPTG :: PointsToGraph -> PointsToGraph -> PointsToGraph
joinPTG a b = PointsToGraph
    { ptgEnv    = Map.unionWith Set.union (ptgEnv a) (ptgEnv b)
    , ptgEdges  = Map.unionWith (Map.unionWith Set.union)
                                (ptgEdges a) (ptgEdges b)
    , ptgEscape = Map.unionWith joinEscape (ptgEscape a) (ptgEscape b)
    , ptgMaybeAliasParams =
        Set.union (ptgMaybeAliasParams a) (ptgMaybeAliasParams b)
    }
