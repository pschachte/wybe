# Research Thesis Plan: Field- and Direction-Sensitive Alias Analysis in Wybe

> **Working Title:** Migrating the Wybe Compiler from Steensgaard-Style Disjoint-Set Alias Analysis to a Field- and Direction-Sensitive Points-To Graph
>
> **Research Area:** Compilers, Program Analysis, Memory Optimisation

---

## Background

Wybe currently employs a Steensgaard-style alias analysis based on disjoint-set union. This approach is efficient but suffers from two main types of imprecision:

- **Direction-insensitivity:** If memory cell `x` points to `y`, both fall into the same disjoint set. Consequently, `y` is considered to alias `x`, and anything aliasing `y` also aliases `x`.
- **Field-insensitivity:** If a structure `p` contains fields `f1` and `f2` pointing to distinct memory, reading `v1 = p^f1` and `v2 = p^f2` places `p`, `v1`, and `v2` into the same disjoint set. This causes the compiler to falsely conclude that `v1` and `v2` alias each other.

---

## Overview

This document is your research roadmap — what to do, in what order, and why. It covers the full arc from initial literature review through to thesis submission, and includes notes on thesis structure, things to watch out for, and a full bibliography.

The core research question is:

> *Can a field- and direction-sensitive Points-To Graph (PTG) replace Wybe's current Steensgaard-style alias analysis in a way that unlocks measurably more destructive in-place mutations, without imposing unacceptable compile-time overhead?*

---

## Phase 1 — Literature Review and Gap Analysis (Weeks 1–3)

Do this before touching any code. Your thesis will be evaluated on how well you situate your work in the existing research landscape, and the literature also contains solutions to problems you will hit during implementation.

### What to Read (in this order)

1. **Hind (2001)** — Start here. It's a short survey that orients you to the whole field and the fundamental trade-offs. Read it to understand *why* alias analysis is hard, not just *how* to do it.
2. **Steensgaard (1996)** — Read this to deeply understand the algorithm your current implementation is based on. You need to be able to explain its limitations from first principles, not just say "it's field-insensitive."
3. **Andersen (1994)** — The foundational PTG approach you're moving toward. Focus on how inclusion constraints differ from unification constraints.
4. **Pearce, Kelly & Hankin (2004/2007)** — The key field-sensitive extension. This is closest to what you are building.
5. **Hardekopf & Lin (2007)** — HCD/LCD cycle collapsing. Read this once you understand the basic Andersen solver, because you'll want to implement at least LCD.
6. **Zheng & Rugina (2008)** — Demand-driven analysis. Important because `isArgUnaliased` is your only real query site — this paper justifies the demand-driven design choice.
7. **Sridharan & Fink (2012)** — Explains why O(N³) worst-case doesn't mean O(N³) in practice for typed languages. Important for justifying your complexity claims.
8. **Smaragdakis & Balatsouras (2015)** — Read this as a comprehensive modern reference once you've read the foundational papers. Good for understanding the design space you're working in.

### What to Produce

- A written gap analysis (~2–3 pages) identifying exactly what the existing literature does and does not provide for your specific problem (LPVM instruction set, Wybe's type system, the `isArgUnaliased` use case). This becomes Section 2 of your thesis.
- A personal notes document mapping each paper's key idea to a concrete decision you'll make in your implementation.

### Important Notes for This Phase

- Pay close attention to **soundness conditions** in each paper. Every rule you implement must be justifiable against a soundness argument, and examiners will ask about this.
- Note that most papers target C or Java. You'll need to translate their concepts to LPVM's specific instruction set. This translation *is* a research contribution — don't treat it as trivial.

---

## Phase 2 — Design the PTG Data Model (Weeks 4–5)

Before writing any implementation code, fully specify the data model on paper (or in a design doc). Changing the data model mid-implementation is very costly in Haskell.

### Key Decisions to Make and Document

**Node types.** Your four node types are:
- `LocalNode NodeId` — freshly allocated cells inside the current procedure
- `ParamNode PrimVarName Offset` — memory passed in via parameter (with offset path for nested fields)
- `GlobalNode GlobalInfo` — memory from global state
- `ReturnNode PrimVarName` — pointers returned from a called procedure

**Graph structure.** Two directed maps:
- `varPointsTo :: Map PrimVarName (Set PTGNode)` — maps variables to the nodes they may point to
- `fieldPointsTo :: Map (PTGNode, Offset) (Set PTGNode)` — maps (node, field offset) pairs to the nodes that field may point to

**Procedure summary.** The `AliasMap` exported from a procedure should be a subgraph containing only `ParamNode` and `GlobalNode` instances — this makes it caller-independent and instantiable at call sites.

### What to Produce

- A formal written specification of the data types before you write any Haskell. Include the types for `AliasMapLocal`, `AliasMap`, and `PointsToGraph`.
- A worked example: trace through a small hand-written LPVM program (e.g., one that builds a two-field struct and reads both fields) and manually derive what the PTG should look like after each instruction. This example will go directly into your thesis and is invaluable for debugging later.

### Important Notes for This Phase

- **The `AliasMap` summary design is the hardest part of the whole project interprocedurally.** Spend disproportionate time here. A bad summary design will either be unsound or will fail to propagate aliasing correctly across call boundaries.
- Discuss the node type design with your supervisor before coding. The choice of what counts as a `ParamNode` vs a `LocalNode` has downstream consequences for soundness.

---

## Phase 3 — Implement Core PTG and Abstract Interpretation Rules (Weeks 6–10)

This is the main implementation phase. Work instruction by instruction, with tests after each one.

### Implementation Order

Do these in this order — each one builds on the previous:

1. **Move (`x = y`)** — Simplest rule. `varPointsTo[x] = varPointsTo[y]`. Implement first to validate your data structure.
2. **Alloc (`p = alloc(...)`)** — Create a fresh `LocalNode`, assign to `varPointsTo[p]`. Validates node creation.
3. **Access (`v = access(p, offset)`)** — Reads from `fieldPointsTo`. Implement lazy `ParamNode` instantiation here for the case where a parameter field has not yet been written.
4. **Mutate (`p1 = mutate(p, offset, x)`)** — Most complex rule. Creates a new node (or reuses destructively), copies existing field edges, overwrites the target offset. Get this right before moving on.
5. **Call (`foo(a, b, c)`)** — Summary instantiation. Map formal parameter names in `foo`'s `AliasMap` to the actual argument nodes in the current PTG.

### What to Produce

- Working Haskell implementation of `PointsToGraph` and each rule in `AliasAnalysis.hs`.
- Unit tests for each rule in isolation (construct a minimal PTG, apply the rule, assert the result). Write these *before* the implementation where possible.

### Important Notes for This Phase

- **The Access rule's lazy instantiation is a soundness-critical detail.** When a `ParamNode` has no outgoing edge for a given offset, you must create a fresh `ParamNode` to represent the unknown nested field rather than returning an empty set — returning empty would be unsound (it would claim nothing is pointed to when the truth is unknown).
- **The Mutate rule must correctly handle the non-destructive case.** When a mutation is not known to be destructive, you must create a new `LocalNode` and copy all existing edges from the old node — you cannot mutate in place in the PTG, because the old pointer may still be live.
- Keep the `nextNodeId` counter in your `PointsToGraph` state and never reuse IDs. Reuse would merge abstract nodes that represent distinct allocation sites.

---

## Phase 4 — Re-implement `isArgUnaliased` (Weeks 11–12)

This is the payoff of the whole project. The `isArgUnaliased` predicate is what gates destructive mutation, and getting it right is the primary correctness requirement.

### The New Check

A variable `v` is unaliased if:
1. Every node `n` in `varPointsTo[v]` has **in-degree 1** in the combined variable-and-field edge graph — meaning no other variable or field edge also points to `n`.
2. No node in `varPointsTo[v]` is reachable from any other **live** variable that is not `v` itself, nor from any unmodified parameter or global node.

Both conditions must hold. Condition 1 alone is insufficient because a node may have in-degree 1 in the current frame but still be reachable via a longer path from a parameter.

### What to Produce

- Re-implemented `isArgUnaliased` in `AliasAnalysis.hs` using PTG traversal.
- A test case where the old disjoint-set analysis returns False (conservative) but the new PTG returns True (precise) — this is your core empirical demonstration and will anchor your evaluation chapter.

### Important Notes for This Phase

- **Soundness over precision always.** If you are uncertain whether a node is aliased, return False. The cost of a false True is a runtime memory corruption bug; the cost of a false False is merely a missed optimisation.
- Track liveness carefully. A node that is pointed to only by dead variables counts as having effective in-degree 0 for the purposes of this check.

---

## Phase 5 — Implement Compile-Time Optimisations (Weeks 13–14)

The move from Steensgaard to Andersen-style analysis increases compile-time cost. The literature offers well-researched mitigations. Implement at least one; two or three make for a stronger thesis.

### Option A — Demand-Driven Query Evaluation (Recommended First)

Rather than computing the full PTG eagerly, only build the portion of the PTG needed to answer a specific `isArgUnaliased` query. Traverse backwards from the target variable's nodes, stopping when you can determine aliasedness. This is architecturally clean for Wybe because `isArgUnaliased` is the only real query site.

**Key reference:** Zheng & Rugina (2008).

### Option B — Lazy Cycle Detection (LCD)

During constraint solving, when a variable's points-to set is updated, check whether a cycle has formed in the constraint graph. If so, collapse the SCC into a single node (reverting to Steensgaard-style unification for that subgraph). This dramatically reduces solver iterations for programs with pointer cycles.

**Key reference:** Hardekopf & Lin (2007).

### Option C — Hybrid Steensgaard + PTG

Keep the existing Steensgaard pass as a fast pre-filter. Only invoke PTG construction for procedures where the Steensgaard analysis reports aliasing at a mutation site. This bounds the PTG cost to the fraction of procedures that actually contain interesting alias relationships.

**Key reference:** The Unias system design philosophy.

### What to Produce

- Implementation of at least one option above.
- Compile-time measurements before and after (see Phase 7).

### Important Notes for This Phase

- Options A and B compose well together. Option C is architecturally simpler but gives up on the long-term goal of retiring the Steensgaard pass entirely.
- If you implement Option A (demand-driven), make sure the demand-driven traversal is still sound — you cannot stop early just because you haven't *found* an alias yet; you need to prove there is *no* path.

---

## Phase 6 — Testing and Verification (Weeks 15–17)

### Regression Testing

Run `make test` against the full existing Wybe test suite. Every program that previously compiled and ran correctly must continue to do so. Any behavioral regression means you have a soundness bug.

### New Alias-Specific Tests

Add `test-cases/alias_fields.wybe` and related test cases. These should:
- Construct complex heap data structures with multiple pointer fields (binary trees, linked lists, directed graphs with shared nodes).
- Assert correct program output at runtime.
- Be inspectable with `--dump-alias` to verify the PTG reports distinct alias sets for independent fields.
- Be inspectable with `--dump-lpvm` to verify that `access` + `mutate` sequences are collapsed into destructive `mutate` (`des=1`) instructions where the new analysis confirms unaliasedness.

### Manual Verification Checklist

For each new test case:
- [ ] Program output is correct.
- [ ] `--dump-alias` shows that `v1 = p^f1` and `v2 = p^f2` do **not** alias each other when `f1 ≠ f2`.
- [ ] `--dump-lpvm` shows `des=1` on the mutate instruction for at least one case where the old analysis would have set `des=0`.
- [ ] The same test with the old analysis produces `des=0` (confirming the improvement is real).

### Important Notes for This Phase

- **Test cases with shared pointers are your highest-risk area.** Construct a test where two variables genuinely do point to the same node and confirm your analysis correctly reports aliasing (not just that it reports non-aliasing for independent fields).
- Keep a log of every bug you find and fix during this phase. This log is evidence of your process and is valuable material for your thesis's evaluation chapter.

---

## Phase 7 — Evaluation and Benchmarking (Weeks 18–20)

This phase produces the empirical results your thesis will be judged on.

### Precision Metric

Count the number of mutation sites where `isArgUnaliased` returns True under the new PTG analysis versus the old disjoint-set analysis. Report this as an absolute number and as a percentage improvement across your benchmark suite. This is your headline result.

### Compile-Time Benchmarks

Measure wall-clock compilation time across three configurations:
1. Baseline Steensgaard only (current implementation)
2. Full PTG without mitigation
3. PTG with your chosen mitigation strategy (Phase 5)

Report results per benchmark and as a geometric mean across the suite. The overhead of configuration 2 over configuration 1 is the raw cost of precision; the overhead of configuration 3 over configuration 1 is the net cost after mitigation.

### Runtime Benchmarks

For benchmarks where additional destructive mutations are unlocked:
- Measure heap allocation count (wrap the allocator to count calls).
- Measure total execution time.
- Report reduction in allocations and execution time versus the baseline.

### What to Produce

- A table of precision results per benchmark.
- A table of compile-time overhead per benchmark and configuration.
- A table of runtime improvements for mutation-heavy benchmarks.
- Analysis of any outliers — programs where the PTG is unexpectedly expensive or unexpectedly imprecise.

### Important Notes for This Phase

- **Discuss your benchmark selection with your supervisor early.** Using only programs from your own new test cases is weak evidence; you want to show results on a variety of existing Wybe programs.
- If compile-time overhead is higher than expected, do not hide it — explain it and use it to motivate future work on further mitigation strategies.

---

## Phase 8 — Thesis Writing (Weeks 21–24)

### Recommended Chapter Structure

| # | Chapter | Purpose |
|---|---------|---------|
| 1 | Introduction | Motivate the problem, state research questions, outline contributions, describe thesis structure |
| 2 | Background & Literature Review | Survey existing approaches; justify your design choices against prior work |
| 3 | The Existing Wybe Alias Analysis | Document the current DisjointSet system and its deficiencies — necessary before presenting your replacement |
| 4 | Points-To Graph Design | Formal specification of node types, graph structure, and procedure summaries |
| 5 | Abstract Interpretation Rules | Rules for Move, Alloc, Access, Mutate, Call — with formal or semi-formal justification |
| 6 | Compile-Time Optimisation Strategies | What you implemented and why, with reference to the literature |
| 7 | Implementation | Code-level description of changes to AST.hs and AliasAnalysis.hs |
| 8 | Evaluation | Precision, compile-time, and runtime results with analysis |
| 9 | Conclusion & Future Work | Summarise contributions, note limitations, suggest extensions |
| — | References | Full bibliography |

### Writing Order

Write in this order, not in chapter order:
1. **Chapter 3** (existing analysis) — you know this best right now, warm up with it
2. **Chapter 4 and 5** (design and rules) — write while implementation is fresh
3. **Chapter 8** (evaluation) — write immediately after collecting results
4. **Chapter 2** (literature review) — refine from your Phase 1 notes
5. **Chapter 1** (introduction) — always write this last; you can't introduce what you haven't done yet
6. **Abstract** — very last, once you know exactly what you found

### Important Things to Note When Writing

- **Chapter 3 is often undervalued by students but scrutinised by examiners.** You must thoroughly document what you are replacing and precisely characterise its limitations with concrete examples. Don't just say "it's field-insensitive" — show a specific LPVM program and trace exactly what the disjoint-set produces vs. what a PTG would produce.

- **Soundness must be argued, not assumed.** For every abstract interpretation rule in Chapter 5, include either a formal proof or a clear informal argument for why the rule overapproximates (i.e., includes all possible runtime behaviours). The access rule's lazy instantiation and the mutate rule's node copying are the two most soundness-critical points.

- **The evaluation chapter should present negative results honestly.** If compile-time overhead is significant, say so and explain what mitigation reduces it to. Examiners trust candidates who report limitations honestly more than those who only report successes.

- **Scope your claims carefully.** Your analysis is intraprocedural with interprocedural summaries but is not context-sensitive or flow-sensitive. Say this clearly in both the introduction and the conclusion. These are natural future-work directions, not failures.

- **Every design decision should be justified.** Why four node types and not three? Why index field edges by byte offset rather than field name? Why include `ReturnNode` separately? The answer to each of these should appear somewhere in Chapters 3–4.

---

## Bibliography

All papers are listed with full citation details. Papers marked **[Core]** are directly cited in the implementation plan or discussion above; papers marked **[Supplementary]** are recommended background reading.

---

### Core References

**[And94]** Andersen, L.O. (1994). *Program Analysis and Optimization for C*. Ph.D. Thesis, DIKU, University of Copenhagen.
— Foundational inclusion-based (direction-sensitive) PTG analysis. Defines the subset constraint model that underlies your proposed implementation.

**[Ste96]** Steensgaard, B. (1996). Points-to Analysis in Almost Linear Time. *Proceedings of POPL 1996*, pp. 32–41.
— Introduces the unification-based alias analysis your current Wybe implementation mirrors. Essential to understand before arguing for the replacement.

**[Hin01]** Hind, M. (2001). Pointer Analysis: Haven't We Solved This Problem Yet? *Proceedings of PASTE 2001*, pp. 54–61.
— Survey of the alias analysis field emphasising the persistent precision/scalability trade-off. Good orientation reading; cite in your introduction and related work.

**[Pea04]** Pearce, D.J., Kelly, P.H.J., & Hankin, C. (2004). Efficient Field-Sensitive Pointer Analysis for C. *Proceedings of PASTE 2004*. Extended version published in *ACM Transactions on Programming Languages and Systems (TOPLAS)*, 2007.
— The primary reference for field-sensitive PTG over struct types. Their offset-based field modelling is directly applicable to LPVM's `access(p, offset)` instruction.

**[Bal16]** Balatsouras, G., & Smaragdakis, Y. (2016). Structure-Sensitive Points-To Analysis for C and C++. *Proceedings of SAS 2016*.
— Extends field sensitivity to handle byte-offset aliasing and type reinterpretation. Relevant for reasoning about when fields must be collapsed for soundness.

**[Har07]** Hardekopf, B., & Lin, C. (2007). The Ant and the Grasshopper: Fast and Accurate Pointer Analysis for Millions of Lines of Code. *Proceedings of PLDI 2007*, pp. 290–299.
— Introduces HCD (Hybrid Cycle Detection) and LCD (Lazy Cycle Detection) for Andersen-style solvers, and HVN/HU equivalence-based pre-processing. Essential reading for compile-time mitigation.

**[Zhe08]** Zheng, X., & Rugina, R. (2008). Demand-Driven Alias Analysis for C. *Proceedings of POPL 2008*, pp. 197–208.
— Formulates alias query answering as CFL-reachability, enabling demand-driven PTG traversal. Directly applicable to Wybe's `isArgUnaliased` query pattern.

**[Har11]** Hardekopf, B., & Lin, C. (2011). Flow-Sensitive Pointer Analysis for Millions of Lines of Code. *Proceedings of CGO 2011*, pp. 289–298.
— Demonstrates staged inclusion-based + flow-sensitive analysis at scale. Useful background for understanding the design space beyond what this thesis covers.

**[Sri12]** Sridharan, M., & Fink, S.J. (2012). The Complexity of Andersen's Analysis in Practice. *Proceedings of SAS 2012*, pp. 205–221.
— Shows that for strongly-typed languages, Andersen's analysis runs in O(N²) practically, not O(N³). Use this to justify your complexity claims.

**[Sui13]** Sui, Y., Ye, D., Xue, J., & Zhang, J. (2013). Making Context-Sensitive Inclusion-Based Pointer Analysis Practical for Highly Recursive Programs. *Software: Practice and Experience*, 44(12), pp. 1485–1510.
— Demonstrates Andersen-style scalability via parameterised procedure summaries. Confirms the `AliasMap` summary approach in Wybe's architecture is the right design pattern.

**[Sma15]** Smaragdakis, Y., & Balatsouras, G. (2015). Pointer Analysis. *Foundations and Trends in Programming Languages*, 2(1), pp. 1–69.
— Comprehensive modern reference covering the full pointer analysis design space. Read this after the foundational papers for a bird's-eye view. Useful for related work positioning.

**[Ber03]** Berndl, M., Lhoták, O., Qian, F., Hendren, L., & Umanee, N. (2003). Points-to Analysis Using BDDs. *Proceedings of PLDI 2003*, pp. 103–114.
— BDD-based field-sensitive PTG for Java. Useful for understanding alternative implementation strategies for the points-to sets themselves.

---

### Supplementary References

**[Wil95]** Wilson, R.P., & Lam, M.S. (1995). Efficient Context-Sensitive Pointer Analysis for C Programs. *Proceedings of PLDI 1995*, pp. 1–12.
— Introduces the summary-based interprocedural pointer analysis framework. Background reading for the `AliasMap` summary design.

**[Rou00]** Rountev, A., & Chandra, S. (2000). Off-line Variable Substitution for Scaling Points-to Analysis. *Proceedings of PLDI 2000*, pp. 47–56.
— Offline simplification of constraint graphs before solving. Complementary to HVN/HU; useful if compile-time is a major concern.

**[Wha99]** Whaley, J., & Rinard, M. (1999). Compositional Pointer and Escape Analysis for Java Programs. *Proceedings of OOPSLA 1999*, pp. 187–206.
— Early PTG-based escape analysis enabling stack allocation — directly analogous to Wybe's allocation elision goal. Good motivational citation for the runtime benefits chapter.

**[Lat07]** Lattner, C., Lenharth, A., & Adve, V. (2007). Making Context-Sensitive Points-to Analysis with Heap Cloning Practical for the Real World. *Proceedings of PLDI 2007*, pp. 278–289.
— LLVM's DSA analysis: a production field-sensitive PTG. Useful for understanding how theory translates to a real compiler.

**[Lho06]** Lhoták, O., & Hendren, L. (2006). Context-Sensitive Points-to Analysis: Is It Worth It? *Proceedings of CC 2006*, pp. 47–64.
— Empirical evaluation of precision gains from context-sensitivity over context-insensitive analysis. Useful for scoping the future-work discussion of what your intraprocedural analysis leaves on the table.