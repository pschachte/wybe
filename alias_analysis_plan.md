# Field- and Direction-Sensitive Alias Analysis Implementation Plan

## 1. Problem Description
Currently, Wybe's alias analysis uses a `DisjointSet` of variable names (`AliasMapLocal` and `AliasMap`). This causes the analysis to be:
- **Direction-insensitive**: If memory cell `x` points to `y`, both fall into the same disjoint set. So `y` is considered to alias `x`, and anything aliasing `y` also aliases `x`.
- **Field-insensitive**: If a structure `p` contains fields `f1` and `f2` pointing to distinct memory, reading `v1 = p^f1` and `v2 = p^f2` places `p`, `v1`, and `v2` into the same disjoint set. This makes the compiler falsely believe `v1` and `v2` alias each other.

Because of this, the compiler cannot safely perform destructive in-place updates or memory reuse on fields containing pointers, since it assumes everything reachable from the struct is highly aliased. We need to implement a standard Points-To Graph (PTG).

## 2. Proposed Data Structures

We will replace `DisjointSet PrimVarName` in `AST.hs` and `AliasAnalysis.hs` with a Points-To Graph representing abstract memory cells and their interconnecting field edges.

### `AliasAnalysis.hs` Updates

```haskell
type NodeId = Int
type Offset = Int

-- Represents an abstract memory cell
data PTGNode
    = LocalNode NodeId              -- A locally allocated cell inside the proc
    | ParamNode PrimVarName Offset  -- Memory passed in via parameter (with offset path)
    | GlobalNode GlobalInfo         -- Memory from global state
    | ReturnNode PrimVarName        -- Node representing the returned pointer
    deriving (Eq, Ord, Show)

-- Replaces current AliasMapLocal
data PointsToGraph = PTG {
    nextNodeId    :: NodeId,
    varPointsTo   :: Map PrimVarName (Set PTGNode),
    fieldPointsTo :: Map (PTGNode, Offset) (Set PTGNode)
}

type AliasMapLocal = PointsToGraph
```

### `AST.hs` Updates
The `AliasMap` (procedure summary) will no longer be a `DisjointSet PrimitiveVarName`. Instead, it will be a summary subgraph containing only `ParamNode` and `GlobalNode` instances, describing how inputs alias each other and how outputs map to inputs.

## 3. Analysis Logic Updates

We will implement standard abstract interpretation rules over the `PointsToGraph` for fundamental LPVM instructions in `AliasAnalysis.hs`:

- **Move (`x = y`)**: `varPointsTo[x] = varPointsTo[y]`.
- **Alloc (`p = alloc(...)`)**: 
  Create a new `LocalNode n`, set `varPointsTo[p] = {n}`.
- **Access (`v = access(p, offset)`)**: 
  `varPointsTo[v] = Union(fieldPointsTo(n, offset) for n in varPointsTo[p])`. 
  *(If `n` is a `ParamNode` and has no outgoing edges for this offset, we lazily instantiate a new `ParamNode` to represent the nested parameter field).*
- **Mutate (`p1 = mutate(p, offset, x)`)**:
  Create a new `LocalNode n` (or reuse a node if it's destructive). Setup `varPointsTo[p1] = {n}`. Copy all `fieldPointsTo` edges from `p`'s nodes to `n`, but overwrite: `fieldPointsTo(n, offset) = varPointsTo[x]`.
- **Call (`foo(a, b, c)`)**:
  Apply `foo`'s `AliasMap` summary to the current PTG. Map the formal parameters in the summary graph to the actual argument nodes passed in from the current PTG.

## 4. Unaliased Checks (`isArgUnaliased`)

The critical function `isArgUnaliased` determines if a variable can be destructively mutated. With a PTG, a variable `v` is unaliased if:
1. The node(s) pointed to by `v` have an in-degree of 1 in the PTG (meaning no other field or variable points to them).
2. The node(s) are NOT reachable from any other **live** variable or unmodified parameter/global nodes.

If `isArgUnaliased` returns True, the compiler can safely perform destructive mutations (e.g., updating a linked list node in place, modifying a tree in place).

## 5. Verification Plan

### Automated Tests
1. **Existing Test Suite**: Run `make test` to ensure that standard programs do not regress in behavior or performance. The existing test suite will capture bugs where we improperly mutate shared state.
2. **New Alias Tests**: Add new test cases (e.g., `test-cases/alias_fields.wybe`) that construct complex data structures (like graphs, binary trees, or nested lists) where multiple pointers exist. Assert the program logic executes correctly.

### Manual Verification
1. **Inspect LPVM Output**: Compile the newly added `test-cases/alias_fields.wybe` with the `--dump-lpvm` and `--dump-alias` flags.
2. **Verify Memory Reuse**: In the dumped LPVM, verify that `alloc` instructions have been elided and `access` followed by `mutate` have been collapsed into purely destructive `mutate` instructions (`des=1`) for independent fields.

## Literature Review & Justification

To ground our architectural decisions, here is a summary of relevant compiler research regarding alias analysis:

### 1. General Alias Analysis and its Benefits
Alias analysis is a fundamental compiler optimization technique that determines whether different memory references might point to the same memory location. 
*   **Purpose:** It enables/enhances optimizations like dead code elimination, loop-invariant code motion, and automatic vectorization.
*   **Relevant Paper/Concept:** *Pointer Analysis: Haven't We Solved This Problem Yet?* by Michael Hind (2001) summarizes the long-standing importance and trade-offs of pointer analysis in compilers. It highlights that precise alias information is critical for transforming code safely.

### 2. Field-Insensitive and Direction-Insensitive Analysis (Our Current Implementation)
Wybe's current disjoint-set implementation is essentially a variation of **Steensgaard's Alias Analysis**.
*   **Definition:** Steensgaard's algorithm is a unification-based approach that is field-insensitive (treats all fields of a struct as the same memory cell) and direction-insensitive (if `a = b`, it unifies their targets rather than making `a` a subset of `b`).
*   **Benefits:** It is extremely fast (running in near-linear time) and highly scalable.
*   **Relevant Paper:** *Points-to Analysis in Almost Linear Time* by Bjarne Steensgaard (POPL 1996). This paper introduced this highly scalable approach. Our current use of `DisjointSet` perfectly mimics Steensgaard's unification constraint approach.

### 3. Field-Sensitive and Direction-Sensitive Analysis (Our Proposed Implementation)
To support advanced in-place mutation and safe memory reuse for complex data structures, we need a **Points-To Graph (PTG)** that is field- and direction-sensitive.
*   **Definition:** Field-sensitive analysis distinguishes between `Object.field1` and `Object.field2`. Direction-sensitive (or inclusion-based) analysis respects the direction of assignments (e.g., if `a = b`, `a` can point to what `b` points to, but `b` doesn't necessarily point to what `a` points to).
*   **Implementation Strategy:** We are migrating towards a points-to graph approach, similar to **Andersen's Alias Analysis**, but extended to track individual fields. This models pointer assignments as directed subset constraints rather than bidirectional equivalence classes.
*   **Relevant Paper:** *Program Analysis and Optimization for C* by Lars Ole Andersen (Ph.D. Thesis, 1994) introduced the foundational inclusion-based (direction-sensitive) alias analysis. Subsequent research, such as *Field-Sensitive Pointer Analysis for C* by David J. Pearce et al. (2004), expands on how to model struct fields accurately in points-to graphs.

### 4. Tradeoffs: Compile Time vs. Run Time
Migrating from a Steensgaard-style Disjoint-Set analysis to an Andersen-style Points-To Graph (PTG) introduces a clear tradeoff between compiler performance and produced code efficiency.

*   **Compile Time Impact:** Steensgaard's analysis operates in near-linear time `O(N * α(N))` because assignments are treated bidirectionally, collapsing variables into equivalence classes. Andersen's inclusion-based analysis treats assignments as directed constraints and propagates points-to sets iteratively. The worst-case complexity for Andersen's is cubic `O(N^3)`. Consequently, the new implementation will increase Wybe's compile times, as constructing and solving the PTG per procedure is computationally heavier than simple union-find operations.
*   **Run Time Impact:** The more precise alias information yielded by the PTG allows the compiler to accurately identify when pointers strictly do not overlap. This precision unlocks aggressive run-time optimizations: the compiler can confidently collapse sequences of `access` and `alloc` instructions into purely destructive tracking `mutate` instructions. By avoiding fresh heap allocations for updating fields in complex data structures, the compiled Wybe programs will experience reduced memory footprint, minimal garbage collection pressure, and overall faster execution times.