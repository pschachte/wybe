# Wybe compiler

The architecture of the Wybe compiler exhibits the following structure:

![Compiler Architecture](Compiler.png)

`wybemk.hs` holds the top level of the compiler, which delegates the bulk of the
work to `Builder.hs`.  This module overseas the phases of compilation, as well
as determining which files actually need to be (re-)compiled.  All of the
compiler phases are built upon the basic data structures and operations, which
are defined in `AST.hs`

The body of the compiler lies in the semantic analysis, compilation, and
optimisation.  This part can be seen in more detail as several separate passes:

![Compilation detail](Detail.png)

# Wybe compiler source directory
The source files in this directory and their purposes are:

| File | Purpose                                      |
| ---- | -------------------------------------------- |
| [AST.hs](#AST)       | Wybe Abstract Syntax Tree and LPVM representation |
| [ASTShow.hs](#ASTShow) | Show Wybe intermediate representation |
| [AliasAnalysis.hs](#AliasAnalysis) | Alias analysis for a single module |
| [Analysis.hs](#Analysis) | Entry point of all kinds of analysis for a single module |
| [BinaryFactory.hs](#BinaryFactory) | Deriving AST Types to be Binary instances |
| [BodyBuilder.hs](#BodyBuilder) | A monad to build up a procedure Body, with copy propagation |
| [Builder.hs](#Builder) | Handles compilation at the module level. |
| [CConfig.hs](#CConfig) | Relate C types to Wybe types for foreign interface |
| [Callers.hs](#Callers) | Find all callers for each proc and count static calls per caller |
| [Clause.hs](#Clause) | Convert Wybe code to clausal (LPVM) form |
| [Config.hs](#Config) | Configuration for wybe compiler |
| [Emit.hs](#Emit)     | Emit LLVM code |
| [Expansion.hs](#Expansion) | Replace certain procedure calls with others |
| [Flatten.hs](#Flatten) | Flatten function calls (expressions) into procedure calls |
| [LLVM.hs](#LLVM)     | Generate LLVM code from LPVM form |
| [LastCallAnalysis.hs](#LastCallAnalysis) | Transform proc bodies and their output arguments so that |
| [Macho.hs](#Macho)   | Extended version of parser for Mach-O object format files |
| [Normalise.hs](#Normalise) | Convert parse tree into an AST |
| [ObjectInterface.hs](#ObjectInterface) | Parse and edit a object file. |
| [Optimise.hs](#Optimise) | Framework to optimise a single module |
| [Options.hs](#Options) | Handle compiler options/switches |
| [Parser.hs](#Parser) | Parser for the Wybe language using Parsec. |
| [Resources.hs](#Resources) | Resource checker for Wybe |
| [Scanner.hs](#Scanner) | Lexical scanner for the Wybe language |
| [Snippets.hs](#Snippets) | Convenience functions for generation of Wybe AST |
| [Transform.hs](#Transform) | Transform LPVM after alias analysis |
| [Types.hs](#Types)   | Type checker/inferencer for Wybe |
| [Unbranch.hs](#Unbranch) | Turn loops and conditionals into separate procedures |
| [Unique.hs](#Unique) | The unique typing system for Wybe |
| [UnivSet.hs](#UnivSet) | Provide a set type supporting the universal set. |
| [Util.hs](#Util)     | Various small utility functions |
| [wybemk.hs](#wybemk) | Wybe compiler/builder main code |


# Modules in more detail


## AST <a id=AST></a>

## ASTShow <a id=ASTShow></a>

## AliasAnalysis <a id=AliasAnalysis></a>

## Analysis <a id=Analysis></a>

## BinaryFactory <a id=BinaryFactory></a>

## BodyBuilder <a id=BodyBuilder></a>
# The BodyBuilder Monad

This monad is used to build up a ProcBody one instruction at a time,
optimising it as it goes.

buildBody runs the monad, producing a ProcBody.
instr adds a single instruction to then end of the procBody being built.
Forks are produced by the following functions:
  buildFork     initiates a fork on a specified variable
  beginBranch   starts a new branch of the current fork
  endBranch     ends the current branch
  completeFork  completes the current fork

No instructions can be added between buildFork and beginBranch, or
between endBranch and beginBranch, or if the current state does not have
a unique continuation. A new fork can be built within a branch, but must
be completed before the branch is ended.

A ProcBody is considered to have a unique continuation if it either
does not end in a branch, or if all but at most one of the branches
it ends with ends with a definite failure (a PrimTest (ArgInt 0 _)).

The ProcBody type does not support having anything follow a fork. Once a
ProcBody forks, the branches do not join again. Instead, each branch of
a fork should end with a call to another proc, which does whatever
should come after the fork. To handle this, once a fork is completed,
the BodyBuilder starts a new Unforked instruction sequence, and records
the completed fork as the prev of the Unforked sequence. This
also permits a fork to follow the Unforked sequence which follows a
fork. When producing the final ProcBody, if the current Unforked
sequence is short (or empty) and there is a prev fork, we simply
add the sequence to the end of each of branch of the fork and remove the
Unforked sequence. If it is not short and there is a prev, we
create a fresh proc whose input arguments are all the live variables,
whose outputs are the current proc's outputs, and whose body is built
from Unforked sequence, add a call to this fresh proc to each branch of
the previous Forked sequence, and remove the Unforked.

We handle a Forked sequence by generating a ProcBody for each branch,
collecting these as the branches of a ProcBody, and taking the
instructions from the preceding Unforked as the instruction sequence of
the ProcBody.

Note that for convenience/efficiency, we collect the instructions in a
sequence and the branches in a fork in reverse order, so these are
reversed when converting to a ProcBody.

Some transformation is performed by the BodyBuilder monad; in
particular, we keep track of variable=variable assignments, and replace
references to the destination (left) variable with the source (right)
variable.  This usually leaves the assignment dead, to be removed in
the backward pass.  We also keep track of previous instructions, and later
calls to the same instructions with the same inputs are replaced by
assignments to the outputs with the old outputs.  We also handle some
arithmetic equivalences, entailments, and tautologies (eg, on a branch
where we know x==y, a call to x<=y will always return true; for
unsigned x, x<0 is always false, and x>0 is replaced with x!=0).
We also maintain a counter for temporary variable names.

The BodyState has two constructors:  Unforked is used before the first
fork, and after each new branch is created. Instructions can just be
added to this. Forked is used after a new fork is begun and before its
first branch is created, between ending a branch and starting a new one,
and after the fork is completed. New instructions can be added and new
forks built only when in the Unforked state. In the Forked state, we can
only create a new branch.

These constructors are used in a zipper-like structure, where the top of the
structure is the part we're building, and below that is the parent, ie,
the fork structure of which it's a part. This is implemented as follows:

   buildFork is called when the state is Unforked.  It creates a new
   Forked state, with the old state as its origin and an empty list
   of bodies.  The new parent is the same as the old one.

   beginBranch is called when the state is Forked.  It creates a new
   Unforked state with the old state as parent.

   endBranch is called with either a Forked or Unforked state.  It
   adds the current state to the parent state's list of bodies and
   makes that the new state.

   completeFork is called when the state is Forked.  It doesn't
   change the state.
## Inferring constant structures

We keep track of memory structures as they are constructed, so we can detect
when a structure contains only constants.  A fresh allocation is considered
to be fully constant, and any mutation of a constant structure to store a
constant value is considered to create a new constant structure (regardless
of whether the mutation is destructive).  Any other mutation of a constant
does not produce a new constant.  We track which variables hold constant
structures, and the contents of those structures.  References to such
variables are replaced with references to the constant data.  Constant
structures are registered with the module; this is handled in AST.hs.
## Tracking Global Flows
Global flows track where global variables (holding resource values) are used
and modified in the program.  This allows us to determine when a global
variable must be loaded from memory, when it must be stored back to memory,
and when we can omit these operations and instead use local variable values.
Global flows are a triple, <ins, outs, params>. ins is the (possibly
infinite) inwards flowing resources (read: globals) and outs is obviously the
outwards flowing globals. params is a set of indexes, for the arguments that
may be called when a proc is called. These sets are used in the body builder
to track which globals are known (and hence don't need to be read again) and
may not need to be written to (if they are not read inside the proc).
These sets are initially set quite liberally, being the set of inwards
flowing resources, outwards flowing, and the indexes of all resourceful HO
parameters. I believe in the body builder, there's some analysis that
restricts these sets where possible. If a HO param is never called (for
whatever reason), then you can remove that param from the set of indexes; if
a global is never written to, then you can remove it from outs for a proc.
When it comes to calling a proc, we first take the global flows of each
argument -- if a HO parameter is a known proc then you take the global flows
of that proc; if it's a parameter of the proc then it's <{}, {}, {idx}>; else
it's a triple of universal sets. With the union of the global flows of the
arguments, and the (non-params) global flows of the called proc. Inside the
body builder, sets of "known" globals that were recently written to in the
execution path are stored. After the call, these resources that are
referenced in the outs are removed from the "known" globals, and must be read
again -- this is because the proc may clobber the global. 
## Reassembling the ProcBody

Once we've built up a BodyState, this code assembles it into a new ProcBody.
While we're at it, we also mark the last use of each variable, eliminate
calls that don't produce any output needed later in the body, and eliminate
any move instruction that moves a variable defined in the same block as the
move and not used after the move.  Most other move instructions were removed
while building BodyState, but that approach cannot eliminate moves to output
parameters.
All of this is mediated by the BkwdBuilder monad.  This monad is used to run
backwards through the body we are currently building, keeping track of the
variables that are used later in the computation but not defined later.
We also try to detect nexted branches on the same variable, and fuse them
into a single switch.
In the end, this produces a new ProcBody equivalent to the initial one, but
somewhat optimised.

## Builder <a id=Builder></a>
The wybe compiler handles module dependencies, and builds
executables by itself, without the need for build tools like
make.  The function buildTarget is responsible for determining
what source files need to be compiled, and for building the
final outputs (whether executable, object file, archive, etc.).

Wybe allows a module to be defined by a single .wybe file, or
by a directory containing multiple submodules.  In the latter
case, the directory must contain a (possibly empty) file named
_.wybe, which should contain all of that module's source code
other than its submodules.

The compiler can generate all these output formats, using the file
extension to work out which type of file to build:  executable,
object code, LLVM bitcode, LLVM assembly code, or archive file.
In general, it can build any type of output from either type of
input, but note that on unix-style systems, both directories and
executables have empty file extensions, so it is not possible to
build an executable from a directory.  Asking to build an object,
LLVM bitcode, or LLVM assembler file for a directory module is
interpreted as asking to recursively build that type of file for
each wybe source file and module directory within that directory.

The compiler stores its internal data structures in object files it
generates, and extracts that information from the object file, rather
than loading and compiling the source file, if the object file is
younger than the source file.  In the case of a directory module, the
nested _.o, _.bc, or _.ll file holds all of the contents of that
module that come from the _.wybe file.  That is, the _.wybe file is
compiled much like other modules, except that its module name is that
of the parent directory, rather than the file itself.

To keep compile times manageable while supporting optimisation,
we compile modules bottom-up, ensuring that all a module's
imports are compiled before compling the module itself. In the
case of circular module dependencies, each strongly-connected
component in the module dependency graph is compiled as a unit.
This is handled by the compileModule function, which includes
the functionality for finding the SCCs in the module dependency
graph.  Then each SCC is compiled by the compileModSCC function.

One shortcoming of the bottom-up approach is that some optimisations
depend upon the way a procedure is used, which cannot be determined
from the code itself.  Such analyses are best performed top-down.
For example, if we can determine that a structure will not be
referenced after the call to a procedure, that procedure may be
compiled to destructively modify or reuse that structure.  Our
approach to this is to apply multiple specialisation:  we compile
different versions of this code for calls that may reference
that argument again and calls that cannot.  Our approach is to
to have the bottom-up analysis produce "requests", which indicate
what top-down analysis results would allow more efficient
specialisations of the code.  This information is produced bottom-
up.  Then, when generating the final executable, when all the code
is available, we determine how beneficial each specialisation would
be, and select the most useful specialisations to actually produce,
and generate code for any that have not already been generated.

Ensuring that all compiler phases happen in the right order is
subtle, particularly in the face of mutual module dependencies.
Following are the ordering dependencies.

* Types: the types a type depends on need to have been processed
before the type itself, so that sizes are known. In the case of
recursive or mutually recursive type dependencies, all types in
the recursion must be implemented as pointers. Types are transformed
into (sub)modules, and constructors, deconstructors, accessors,
mutators, and auxiliary type procedures (equality tests, plus
eventually comparisons, printers, pretty printers, etc.) are all
generated as procedures within those submodules.  Therefore,
these must be handled as submodules are.

* Resources:  the resources a resource depends on must have been
processed before the resource itself.  (We currently don't
support defining resources in terms of others, but the plan is
to support that.)  The types in the module that defines a
resource, and all module dependencies, must have been processed
at least enough to know they have been defined before processing
the resource declaration.

* Top-level statements in a module: these are transformed to
statements in a special procedure whose name is the empty string
as the statements are processed, so their dependencies are the
same as for statements in ordinary procedure bodies.

* Functions: functions and function calls are transformed to
procedures and procedure calls without reference to anything
external to the functions themselves, so function dependencies
behave exactly like procedure dependencies.

* Procedures: the procedures a procedure calls must have been
type and mode checked before they can themselves be type/mode
checked, and must be analysed and optimised before they can
themselves be analysed/optimised. All the procedures in the
(sub)modules that define each type a procedure uses, as either a
parameter or local variable type, must have been processed the
same way before processing the procedure itself.

* Nested submodules: the submodules defined within a module file,
including the types, must be processed as mutual dependencies of
that module, which they are. The nested submodules of a module
(including types) have access to all public and private members
of the parent module, and the parent has access to all public
members of the parent, so they are mutual dependencies.

* Directory modules:  A directory containing a file named _.wybe
is also a module, with all the contained .wybe files as submodules.
However, these submodules do not automatically import all the other
modules in that directory, although they can explicitly import any
sibling modules they need.

This means only minimal processing can be done before module
dependencies are noted and read in.  So we handle all these
dependencies by initially reading a module to be compiled and
handling contents as follows:

* Types:  create and enter the submodule, note that the parent
imports it, and process its constructors and other contents.

* Submodules:  create and enter the submodule, note that parent
imports it, and process its contents.

* Resources:  Record for later processing.

* Pragmas:  Record for later processing.

* Constructors and low-level (representation) types: record for
later type layout, code generation, etc.

* Top level statements:  add statements to the special "" proc
in the module, creating it if necessary.

* Procs and functions:  record them for later normalisation,
analysis, optimisation, etc.

Once we have finished loading the sources for the specified
targets, and all their dependencies, we compute the SCCs in
the module dependency graph.  Then for each SCC, in topographic
order, we call compileModSCC, which does the following:

  1. Traverse all recorded type submodules in the module list
     finding all type dependencies; topologically sort them and
     identify SCCs. For each SCC:

       1. Determine the type representation for all
          constructors.

       2. Record the primitive representation of the type.

       3. Generate and record all constructor, accessor,
          mutator, and utility procs.

     This is handled in the Normalise module.

  2. Check all resource imports and exports. (Resources.hs)

  3. Normalise all recorded procs in their modules, including
     generated constructors, etc. (Normalise.hs)

  4. Validate the types of exported procs. (Types.hs)

  5. Check proc argument types, resolve overloading, and
     mode check all procs. (Types.hs)

  6. Check proc resources and transform them to args.
    (Resources.hs)

  7. Transform away branches, loops, and nondeterminism.
     (Unbranch.hs)

  8. Topologically sort proc call graph and identify SCCs.  For
     each SCC, bottom-up, do the following:

       1. Compile procs to clausal form (Clause)

       2. Optimise procs (Optimise)


## CConfig <a id=CConfig></a>

## Callers <a id=Callers></a>

## Clause <a id=Clause></a>

## Config <a id=Config></a>

## Emit <a id=Emit></a>

## Expansion <a id=Expansion></a>

## Flatten <a id=Flatten></a>
We transform away all expression types except for constants and
variables.  Where, let, conditional, and function call
expressions are turned into statements that bind a variable, and
then the variable is used in place of the expression.  All function
calls are transformed into procedure calls by adding an extra
argument corresponding to the function result.

Function call expressions can take one of three forms.  Expressions
where all arguments are inputs are turned into a procedure call
with a fresh temporary variable as an output, which is called before
the statement in which that function call appears.  The function
call itself is then replaced by a referenced to the temporary
variable.  For example, p(f(x,y),z) is replaced by f(x,y,?t); p(t,z).

A function call containing some output arguments, and perhaps some
inputs, is transformed into a fresh input variable, with a later
proc call to that function with that variable as an added input.
For example, p(f(?x,y),z) is transformed to p(?t,z); f(?x,y,t).
Finally, a function call containing some input-output arguments,
and perhaps some input arguments, is transformed into an
input-output variable, plus two procedure calls, one to compute
the initial value of the expression, and a second to assign it
the specified new value.  For example, a statement p(f(!x,y),z) is
transformed to f(x,y,?t); p(!t,z); f(!x,y,t).

## LLVM <a id=LLVM></a>

# Generating LLVM code

We generate a `.ll` text file directly for each Wybe `.wybe` file, compiling
this as necessary to build `.o`, `.bc` `.s`, or executable files.  For each
generated `.ll` file, we produce the following, in order:

* **Prologue** — contains an introductory comment and any configuration info
  needed for LLVM.

* **Constants** — LLVM definitions of the manifest constants used in this
  module; mostly used for strings.

* **Global variables** —  LLVM declarations of the global variables used to
  implement the resources defined in this module.

* **Externs** — Extern declarations for all symbols used, but not defined,
  in this module; this includes imported Wybe procedures, C functions,  and
  global variables.

* **Definitions** — Definitions of the procs of this module.

* **Exports** — Everything needed by the Wybe compiler to compile users of
  this module; currently this is represented as a serialisation of the
  Module data structure, placed in the LLVM section.


## LastCallAnalysis <a id=LastCallAnalysis></a>

# Last Call Optimisation

The compiler relies on the LLVM compiler to perform last call optimisation,
turning the last call in a procedure body into a jump, if no other
instructions follow the last call.  This module tries to increase the number
of procedures where this optimisation applies by moving code that follows the
last call before it, whenever all the inputs to those instructions are
available before the last call.

One particular trick employed to make this possible is
last-call-modulo-construction optimisation.  The idea here is to invert the
direction of data flow, turing an output into an input, by passing in the
address to which to write the output.  When the instruction following the
last call in a body simply writes an output of that call into one memory
location, without using it in any other way, and when the called procedure is
defined in the module currently being compiled (so we can transform it), we
can change that output argument into a pointer input, and modify the
procedure definition to write the output value to memory through that
pointer.  This is done by changing that parameter from FlowOut to
FlowOutByReference, and similarly changing the corresponding argument in all
calls to that procedure.  Likewise, we change the instruction intended to
write the procedure output to memory from FlowIn to FlowTakeReference.

Note that this transformation leaves the call that notionally produces the
output before the instruction that notionally writes the value to memory,
despite the fact that now the latter actually takes the address to be written
to, and the former actually passes that address into a procedure call.
Therefore, when the LLVM code is actually generated, the procedure call must
be deferred until after the address is taken.  This is performed by the LLVM
module.


## Macho <a id=Macho></a>

## Normalise <a id=Normalise></a>

## ObjectInterface <a id=ObjectInterface></a>

## Optimise <a id=Optimise></a>

## Options <a id=Options></a>

## Parser <a id=Parser></a>

## Resources <a id=Resources></a>
###                 Resource Transformations.

There are two passes related to resources within the Wybe compiler.

The first pass canonicalises the `use` declarations in procedure prototypes.
This resolves the module which each resource refers to.

The second, performed after type checking, transforms resource usage into
references to global variables. Each reference to an in scope resource by 
name is transformed into a load (input) or a store (output), or both (in/out). 
Finally, `use` blocks are also transformed to save (load) and then restore
(store) each out-of-scope resource.

The final pass assume that type and mode checking has occured. Type
checking ensures that resources have the correct types, and mode checking
ensures that resources, where applicable are in scope.


## Scanner <a id=Scanner></a>

## Snippets <a id=Snippets></a>

## Transform <a id=Transform></a>
# Escape Analysis & Stack Allocation in the Wybe Compiler

This document explains how the Wybe compiler decides that some heap allocations
can safely become *stack* allocations, and how that decision is carried through
to the LLVM backend. It starts with the intuition and builds up to the precise
algorithm, the soundness argument, and the known limitations.

The relevant code lives in:

- [`src/Transform.hs`](/src/Transform.hs) — the analysis and the alloc-site decision.
- [`src/AliasAnalysis.hs`](/src/AliasAnalysis.hs) — the supporting alias check (`isArgEscaped`).
- [`src/LLVM.hs`](/src/LLVM.hs) — lowering a `{stack}` alloc to an `alloca`, and the tail-call interaction.
- [`src/Options.hs`](/src/Options.hs) — the `stack-alloc` optimisation flag and `--stack-alloc-limit`.

---

## 1. The intuition

When a Wybe program builds a structure — a tuple, a record, a list cell — the
compiler emits an `lpvm alloc` instruction that, by default, calls
`wybe_malloc` and gets memory from the **heap**. Heap memory is managed by the
Boehm garbage collector: it lives until nothing references it any more, and
reclaiming it costs CPU time.

But a great many allocations don't need to live that long. Consider:

```wybe
def {noinline} distance(x1:int, y1:int, x2:int, y2:int):int use !io {
   ?p = point(x1, y1)        # allocate a point
   ?q = point(x2, y2)        # allocate another
   (p^x - q^x) + (p^y - q^y) # read both, then we're done with them
}
```

Here `p` and `q` are created, read a few times, and then forgotten. Nothing
outside `distance` ever sees them. Their lifetime is exactly the lifetime of
the call. That is *precisely* what the machine stack is for: memory that is
born when a function is entered and dies when it returns, reclaimed for free by
popping the stack frame.

So the optimisation is: **if a structure cannot outlive the procedure call that
created it, allocate it on the stack instead of the heap.** This removes GC
pressure and is usually faster.

The catch is the word *cannot*. If we put a structure on the stack and the
program keeps a pointer to it after the procedure returns, that pointer now
points into a stack frame that has been torn down and reused — a classic
**use-after-free**. Getting this wrong does not produce a compile error or a
clean crash; it produces silent garbage. So the analysis must be **sound**: it
may keep something on the heap that could have gone on the stack (a missed
optimisation), but it must **never** put something on the stack that escapes.

The analysis that answers "can this structure outlive its procedure?" is called
**escape analysis**. A structure *escapes* if a reference to it can survive past
the procedure's return.

---

## 2. How a value can escape

A pointer created inside a procedure can outlive that procedure in only a few
ways. The analysis must catch every one of them:

1. **It is returned.** The pointer is written to an output parameter, so the
  caller receives it.

2. **It is passed to a call we can't see into.** Once a pointer is handed to
  another procedure (a Wybe `PrimCall`), a higher-order call (`PrimHigher`), or
  a foreign C function, that callee might stash it in a global, the heap, or
  one of its own outputs. From this procedure's point of view, the pointer has
  left the building.

3. **It is stored into a global.** Wybe has no raw globals, but it has
  *resources*, which lower to global variables. Writing a pointer into a
  resource (`lpvm store` to a global) lets it outlive any single call.

4. **It is embedded in another structure that escapes.** If we store pointer
  `a` into structure `b` (via `lpvm mutate`), and `b` later escapes by any of
  the routes above, then `a` escapes too — the escaping `b` carries `a` out
  with it.

If none of these apply, the pointer is *captured* — confined to the procedure —
and is a candidate for stack allocation.

---

## 3. Where the analysis runs in the pipeline

Escape analysis is part of the **Transform** pass
([`transformProcBody`](/src/Transform.hs)), which runs after alias analysis has
reached its fixed point. Transform already walks every procedure body to set
the *destructive* flag on `mutate` instructions (the in-place-update
optimisation). Stack allocation piggy-backs on that same walk.

For each (non-inline) procedure, Transform:

1. Computes `escapedVars`, the set of variables that may escape — see
  [`computeEscapedVars`](/src/Transform.hs) (§5). This is computed **once**,
  up front, over the whole body.
2. Walks the body instruction by instruction
  ([`transformPrim`](/src/Transform.hs)), maintaining an incremental alias map.
3. At each `lpvm alloc`, decides heap vs stack (§6).

One ordering fact matters a great deal and is the source of a subtle bug class
(see §9): the alias map in step 2 is built **forward** — at the point we reach
an alloc, it reflects only the parameters and the instructions *before* the
alloc. An escape caused by an instruction *after* the alloc is invisible to the
alias map. That is exactly why the up-front, whole-body `computeEscapedVars`
exists, and why it must be complete on its own.
---

## 4. The two escape checks

At an alloc site the analysis combines two independent checks
([`transformPrim`, the `lpvm alloc` case](/src/Transform.hs)):

```haskell
let escapedByAlias    = isArgEscaped aliasMap outVar
let escapedByMutation = Set.member n escapedVars
let escaped           = escapedByAlias || escapedByMutation
```

- **`escapedByAlias`** ([`isArgEscaped` in `AliasAnalysis.hs`](/src/AliasAnalysis.hs)):
 consults the *incremental* alias map. It returns `True` if the alloc result
 is aliased to a global (`AliasByGlobal`), a parameter (`AliasByParam`), or a
 maybe-aliased parameter (`MaybeAliasByParam`). Because the map is built
 forward (§3), this check only catches aliasing established *before* the
 alloc. It is therefore best understood as an *opportunistic early* check, not
 the authoritative one.

 **In practice this check is inert — it is always `False` for an alloc's own
 result.** `isArgEscaped` queries the alias map *as it stands before this
 alloc*, but `outVar` is created *by* this alloc, so it cannot yet be connected
 to any global or parameter in that map. A sweep of the whole final-dump suite
 confirms it: `escapedByAlias=True` appears in **zero** of the 57 alloc
 decisions, while genuinely-escaping allocs are all caught by
 `escapedByMutation`. The stored whole-body `procArgAliasMap` would not help
 either — it is *parameter-level* and does not track local alloc temporaries.

 It is kept (rather than deleted) because it is harmless: being part of an
 `||`, it can only *add* escapes, never remove them, so it cannot make the
 analysis unsound. But it must **not** be mistaken for a safety net covering
 the global/parameter routes — it provides no such coverage. Treating it as
 one is precisely the misconception that produced the original global-store
 bug (§9): the authoritative, complete check is `escapedByMutation` alone.

- **`escapedByMutation`** ([`computeEscapedVars`](/src/Transform.hs)): the
 whole-body, order-independent analysis. This is the authoritative check and
 carries the soundness guarantee.

An alloc is stack-allocated only if **neither** check fires (and the size
constraints in §6 hold).

---

## 5. `computeEscapedVars` in detail

This function answers, for one procedure body, "which variables may escape?".
It works in two parts: **seeds** (variables that definitely escape) and
**edges** (a may-point-to graph along which escape propagates backward). It then
takes the least fixed point.

### 5.1 Collecting the instructions

```haskell
prims = collectAllBodyPrims body
```

[`collectAllBodyPrims`](/src/Transform.hs) flattens every instruction in the
body, **including all branches of every fork**. This is deliberately
conservative: the analysis ignores control flow entirely and treats the body as
one flat bag of instructions. If a value escapes on *any* path, it is treated
as escaping on *all* paths. (Recall LPVM is roughly SSA — variables are uniquely
named — so merging branches into one set does not conflate distinct values.)

### 5.2 The seeds — variables that definitely escape

```haskell
escaped0 = Set.fromList (outParamEsc ++ callArgEsc ++ storeEsc)
```

**Seed 1 — output parameters** (`outParamEsc`). Every output parameter escapes
by definition: the caller receives its value.

**Seed 2 — arguments to opaque calls** (`callArgEsc`). Every pointer passed as a
non-output argument to a call we cannot analyse escapes *unconditionally*. The
predicate is [`isConservativeCall`](/src/Transform.hs):

```haskell
isConservativeCall PrimCall{}               = True   -- user-defined Wybe call
isConservativeCall PrimHigher{}             = True   -- higher-order call
isConservativeCall (PrimForeign lang _ _ _) = lang /= "llvm" && lang /= "lpvm"  -- e.g. C
```

There are two reasons this is unconditional, not "escapes only if the call's
output escapes":

- The callee may retain the pointer (store it in a global, the heap, or an
 output).
- The call may be **tail-call optimised**. TCO reuses the current stack frame
 for the callee. If a stack-allocated pointer from this frame were passed to a
 tail call, the frame — and the allocation — would be torn down while the
 callee still uses it. Tail position is only decided much later, in the LLVM
 backend, so we cannot know here which calls will be tail calls. Treating every
 pointer reaching such a call as escaping side-steps the question entirely.

**Seed 3 — values stored into globals** (`storeEsc`). Every pointer that is the
value argument of an `lpvm store` escapes. `lpvm store` writes into a global
variable (a Wybe resource), which outlives any single call:

```haskell
storeEsc = [ argVarName val
          | PrimForeign "lpvm" "store" _ (val:_) <- prims
          , argIsVar val ]
```

This seed *must* live here rather than relying on the alias map. The store that
makes a value escape almost always comes *after* the value is built (`?c =
cell(...)` then `?global = c`), so the forward alias map at the alloc site
cannot see it. `computeEscapedVars` scans the whole body, so it does.

### 5.3 The edges — how escape propagates

Escape flows *backward*: if a value escapes, the values that flow *into* it also
escape. There are two kinds of edge.

**Mutate edges.** For `mutate(fIn, fOut, offset, destr, size, startOff,
member)` — which produces `fOut`, a copy of `fIn` with one field set to
`member`:

```haskell
mutateEdges = [ (argVarName fOut, argVarName vin)
       | PrimForeign "lpvm" "mutate" _ args@(fIn:fOut:_) <- prims
       , argIsVar fIn, argIsVar fOut
       , vin <- fIn : [ m | m <- List.drop 6 args, argIsVar m ] ]
```

The edge `(fOut, vin)` means "if `fOut` escapes, then `vin` escapes." Two things
flow in:

- `fIn` — the struct being updated. `fOut` is just a new version of it, so if
 the new version escapes, so does the old. (This is conservative for
 *non-destructive* mutates, where `fOut` is genuinely a fresh copy and `fIn`
 need not escape — but escape analysis runs *before* the destructive-update
 transformation sets the `destr` flag, so it cannot yet tell the two apart.
 See §9.)
- `member` — the field value being stored *into* the struct. If the struct
 escapes, the embedded pointer escapes with it. This is route 4 from §2.

Because mutates form a chain (`s0 = alloc; s1 = mutate s0; s2 = mutate s1; …`),
these edges chain too: if the final version `sN` escapes, escape propagates back
through every intermediate version and every member stored along the way.

**Pass-through edges.** For any other `llvm`/`lpvm` instruction that is not an
alloc, mutate, or opaque call:

```haskell
passEdges = [ (outName, inName)
           | prim <- prims
           , not (isAllocOrMutate prim)
           , not (isConservativeCall prim)
           , ...
           , ArgVar{...outName, outType, outFlow} <- allArgs, isOutputFlow outFlow
           , ArgVar{...inName,  inType,  inFlow}  <- allArgs, not (isOutputFlow inFlow)
           , valuePreserving || inType == outType ]
```

This adds an edge from each output to each input when either:

- the instruction is **value-preserving** ([`isValuePreserving`](/src/Transform.hs)
 — `lpvm cast` or `llvm move`), which carries the *same address* into a result
 of a possibly different type; or
- the input and output have the **same type**, a conservative proxy for "the
 address might be passed through."

### 5.4 The fixed point

```haskell
go escaped =
   let newEsc = Set.fromList [ vin | (vout, vin) <- allEdges, Set.member vout escaped ]
       escaped' = Set.union escaped newEsc
   in if Set.size escaped' == Set.size escaped then escaped else go escaped'
```

Starting from the seeds, repeatedly add any `vin` whose `vout` is already known
to escape, until nothing new is added. The result is every variable from which
an escaping value is reachable backward through the graph. Allocs whose result
is **not** in this set are escape-free.

---

## 6. The alloc-site decision

Back in [`transformPrim`](/src/Transform.hs), for `lpvm alloc(size, ?out)`:

```haskell
let escaped      = escapedByAlias || escapedByMutation
let constSize    = argIsConst sizeArg               -- size known at compile time?
let alreadyStack = "stack" `elem` flags
let withinLimit  = maybe False (<= stackLimit) (argIntVal sizeArg)
-- (stackLimit and doStackAlloc are read from the compiler options)
```

The alloc becomes a stack alloc — tagged with a `{stack}` flag — only when **all**
of:

- `not escaped` — the escape analysis cleared it;
- `constSize` — the size is a compile-time constant;
- `withinLimit` — the size is at or below `--stack-alloc-limit` (default 4096
 bytes, see [`Options.hs`](/src/Options.hs));
- `not alreadyStack` — idempotence;
- `doStackAlloc` — the `stack-alloc` optimisation is enabled.

Otherwise it stays a heap alloc.

**Why require a constant size?** LLVM can do variable-sized `alloca` (C99 VLAs),
but a dynamic `alloca` forces a frame pointer, which blocks tail-call
optimisation, and makes `--stack-alloc-limit` impossible to enforce at compile
time. In practice this costs nothing: Wybe types are always statically sized.

**Why a size limit?** Stack space is finite and a single oversized `alloca` (or
one inside a deep recursion) can blow the stack. The limit keeps stack usage
bounded; anything larger falls back to the heap.

---

## 7. Lowering to LLVM

A `{stack}`-tagged alloc reaches the backend in
[`writeLPVMCall "alloc"`](/src/LLVM.hs):

```haskell
if "stack" `elem` flags
then case argIntVal sz of
   Just sizeVal -> do
       (writeTmp, readTmp) <- freshTempArgs $ Representation CPointer
       stackAlloc writeTmp (fromIntegral sizeVal)   -- emit `alloca i8, i64 N`
       typeConvert readTmp out                      -- ptrtoint to the i64 Wybe uses
   Nothing -> shouldnt "stack alloc with non-constant size"
else heapAlloc out sz pos                            -- the normal wybe_malloc path
```

[`stackAlloc`](/src/LLVM.hs) emits the `alloca` and records the result in
`stackAllocedVars`. Wybe represents pointers as `i64`, so the raw `ptr` from
`alloca` is immediately `ptrtoint`-converted to the variable the rest of the
code expects.

### Keeping track of stack-allocated addresses

The backend maintains a set, `stackAllocedVars`, of variables that hold a
stack address:

- [`recordStackAlloced`](/src/LLVM.hs) adds the `alloca` result.
- [`propagateStackAlloced`](/src/LLVM.hs), called from `typeConvert`, follows the
 address through moves and pointer conversions (`ptrtoint`, casts) so that
 LLVM-level renaming doesn't lose track of which `i64` values are really stack
 addresses. It is also called explicitly across the `llvm add` that forms a
 non-zero-offset *interior* pointer in the `mutate` lowering (which does not go
 through `typeConvert`), so that the address of a field of a stack struct is
 tracked as a stack address too — see §9, point 5.

This set powers the tail-call check (§8).

---

## 8. Interaction with tail calls

Tail-call optimisation reuses the current frame for the callee. That is fatal if
the callee receives a pointer into the current frame's `alloca` space — the
frame is gone but the pointer is still used.

Earlier the backend used a single boolean `doesAlloca`: *any* `alloca` in a body
blocked *all* tail calls in it. The current design is more precise. At each call,
[`tailMarker`](/src/LLVM.hs) checks whether any input argument *actually*
references a stack-allocated variable:

```haskell
tailMarker must ins = do
   stackVars <- gets stackAllocedVars
   let passesStackVar = any (\arg -> case arg of
           ArgVar{argVarName=n} -> Set.member n stackVars
           _                    -> False) ins
   return $ case (passesStackVar, must) of
       (True,_)      -> ""            -- stack address flows in: no tail marker
       (False,True)  -> "musttail "
       (False,False) -> "tail "
```

If no input references a stack address, TCO is still safe even when the body
contains other `alloca`s, because escape analysis has already guaranteed those
allocations do not reach this callee.

(Note the two layers reinforce each other: escape analysis already refuses to
stack-allocate anything passed to a Wybe/foreign call — seed 2 — so in practice
a stack address rarely reaches a call argument at all. The `tailMarker` check is
the backend's belt-and-suspenders guarantee for the addresses that legitimately
flow into inlined `llvm`/`lpvm` operations.)

---

## 9. Known conservative limitations

These are *imprecisions*, not *unsoundness* — they cause missed optimisations,
never use-after-free.

1. **Non-destructive mutate treats `fIn` as escaping.** Because escape analysis
  runs before the destructive-update transformation, it cannot tell a
  destructive mutate (writes `fIn` in place) from a non-destructive one
  (produces a fresh `fOut`). For a truly non-destructive mutate, `fIn` need not
  escape when `fOut` does. Recovering this would need either a preliminary
  sub-pass to annotate `destr` flags before escape analysis, or marking
  stack-friendly mutates directly (`{stack}` on the mutate).

2. **Pass-through to opaque calls is always an escape.** A value passed to a
  `pass_back(p, ?q)`-style call that merely returns its argument is treated as
  escaping, even when the result is used purely locally. Recovering this
  soundly requires interprocedural escape *summaries* plus tail-position
  analysis (a later, more precise pass).

3. **Branch-insensitivity.** Escaping on any path marks a value as escaping on
  all paths (§5.1).

### Bugs this design originally had (now fixed)

**Bug 1 — stores into a global were missed.** `computeEscapedVars` did not have
seed 3, and so missed pointers stored into a global *after* their alloc — the
forward alias map couldn't see the later store either, so such a value was
wrongly stack-allocated. The symptom was a global resource pointing into a
freed stack frame:

```wybe
resource saved:cell = cell(0, 0)
def {noinline} stash(x:int) use !saved {
   ?c = cell(x, x)    # built locally...
   ?saved = c         # ...then stored into a global: it ESCAPES
}
```

Adding seed 3 (`storeEsc`) closed the hole. The regression tests are
[`test-cases/execution/stack_alloc_global_escape.wybe`](/test-cases/execution/stack_alloc_global_escape.wybe)
(catches the miscompilation at runtime) and
[`test-cases/final-dump/stack_alloc_global.wybe`](/test-cases/final-dump/stack_alloc_global.wybe)
(asserts no stray `{stack}` flag in the IR).

**Bug 2 — dead-cell reuse handed stack memory to an escaping value.** This one
is the most subtle, and it is a three-way interaction between stack allocation,
the *destructive-update* transformation, and *dead-cell reuse* (CTGC) — all of
which happen in the same Transform pass, in that order, **after**
`computeEscapedVars`.

Wybe already has a compile-time-garbage-collection optimisation: when a
structure is provably dead (read by an `lpvm access` while unaliased and final),
its memory is recorded as a *dead cell* and the next same-sized `alloc` is
rewritten to **reuse** it (an `llvm sub` off the dead cell's address) instead of
allocating fresh. Crucially, that reuse path in
[`transformPrim`](/src/Transform.hs) does **not** consult the escape analysis.

Now consider:

```wybe
resource saved:cell = cell(0, 0)
def {noinline} stash(x:int) use !saved {
   ?c = cell(x, x)    # c is local -> escape analysis STACK-allocates it
   ?tmp = c^a         # read c -> c is now a dead cell
   ?d = cell(tmp, x)  # same size as c -> reuses c's memory
   ?saved = d         # d ESCAPES via the global
}
```

The two field writes that build `c` become *destructive* mutates (set after
escape analysis), so the dead cell's memory *is* `c`'s stack slot. Dead-cell
reuse then gives that stack memory to `d` — which escapes into `saved`. The
global ends up pointing into a torn-down frame: a use-after-free that prints
silent garbage (and only with `stack-alloc` enabled).

The fix threads a set of **stack variables** through the transform: the result
of every `{stack}` alloc, plus anything that comes to share that memory through
a destructive mutate or a value-preserving op (`lpvm cast` / `llvm move`). At a
reuse site, if the dead cell is a stack variable the reuse is **refused** and a
fresh allocation is emitted instead — which the escape check then heap-allocates
(because the new value escapes) or stack-allocates afresh (if it is local).
Reuse of *heap* dead cells — the common and valuable CTGC case, e.g. a
functional update that returns the updated record — is unaffected, because such
dead cells never enter the stack-variable set.

The regression test is
[`test-cases/execution/stack_alloc_reuse_escape.wybe`](/test-cases/execution/stack_alloc_reuse_escape.wybe)
(catches the miscompilation at runtime; the bug is invisible in the dumped IR
beyond the presence of an `llvm sub` reuse).

### Audit of every transformation that runs *after* the escape decision

Both bugs above were *later passes re-routing memory the escape analysis had
already judged*. To be confident there are no more, here is every transformation
that touches a proc body after `computeEscapedVars` has fixed the `{stack}` flag,
with the reason each is sound. (Pass order, from
[`Builder.hs`](/src/Builder.hs): OPTIMISE/inlining → ANALYSIS → TRANSFORM/escape
analysis → LAST CALL ANALYSIS, then later the top-down multi-specialisation pass
re-runs TRANSFORM.)

1. **Inlining** runs *before* escape analysis, so an inlined alloc is judged in
  the caller's context. Inline procs are themselves never transformed
  (`transformProcBody` rejects them). Nothing to break.
2. **Destructive-update transformation** (same pass, after the escape set is
  computed). `computeEscapedVars` already treats a mutate's input as escaping
  whenever its output does, *regardless of the destr flag*, so turning a mutate
  destructive never enlarges the set of reachable-after-return values.
3. **Dead-cell reuse (CTGC)** — Bug 2. Fixed by the stack-variable set.
4. **Last-call analysis: `FlowOut` → `FlowOutByReference` on the proc's output
  param.** When the specz pass re-runs `computeEscapedVars` on the rewritten
  body, `isOutputFlow FlowOutByReference` is `True`, so the param is still seed 1
  — the escaped set cannot shrink.
5. **Last-call analysis: `FlowTakeReference` on a mutate member + a resulting
  tail call.** This hands the *address of a struct field* to the callee. It is
  sound because **every struct LCA take-references is connected to the proc's
  output** (that connection is precisely why the deferral is valid), so escape
  analysis always heap-allocates it — verified empirically: the canonical
  "build a struct, fill its non-first field with the last call's result, return
  it" pattern emits `wybe_malloc`, never `{stack}`. The only way to get a *local*
  (non-escaping) struct in that position is for its post-call write to be dead,
  and a dead mutate is eliminated by the backward pass *before* LCA sees it
  (also verified: the body collapses to just the tail call). A latent
  fragility remains — `propagateStackAlloced` (§8) was not applied across the
  `llvm add` that computes a non-zero-offset interior pointer, so the LLVM-level
  tail-call guard had an asymmetry (offset 0 protected, offset ≠ 0 not). It is
  unreachable today for the reason just given, but a one-line defensive
  propagation now closes it so the guard does not silently depend on the
  escape-analysis ⟺ LCA invariant holding forever.
6. **`convertOutByRefArg` allocating a fresh slot** for an out-by-reference arg
  at a *non*-tail call site stack-allocates a temporary, records it, and
  suppresses the call's tail marker (it must load the result afterward). Sound.
7. **The multi-specialisation top-down re-run of TRANSFORM.** It re-runs the same
  conservative `computeEscapedVars` on the LCA-rewritten body. A specialised
  alias map can only make *more* mutates destructive or enable *more* reuse —
  neither of which shrinks the escaped set (point 2) and the latter is guarded
  (point 3). It cannot newly stack-allocate something an earlier pass kept on the
  heap and LCA then relied on.
8. **LLVM tail-call optimisation** itself is the headline interaction, handled by
  `tailMarker`/`stackAllocedVars` — see §8.

The thread common to all of these: a later pass is only dangerous if it lets a
stack address reach a point the escape analysis did not model. Each one either
runs before the analysis, preserves the conservative escaped set when the
analysis is re-run, or is caught by a dedicated guard (the stack-variable set in
TRANSFORM, and `stackAllocedVars` in LLVM lowering).

---

## 10. Soundness, informally

Stack allocation of an alloc `A` is sound iff `A`'s address cannot be referenced
after the procedure returns. The analysis guarantees this by ensuring that if
`A` could be referenced afterward, `A`'s result variable lands in `escaped`:

- **Returned** → the variable flows to an output parameter; output params are
 seed 1, and mutate/pass-through edges propagate escape backward to `A`.
- **Passed to an opaque call** → seed 2 marks it directly.
- **Stored to a global** → seed 3 marks the stored value; mutate edges propagate
 to anything embedded in it.
- **Embedded in an escaping struct** → mutate edges propagate from the struct to
 the member.

Every escape route from §2 maps onto a seed or an edge, and the seeds are all
computed over the *whole* body (order-independent), so an escape anywhere in the
procedure is caught regardless of where the alloc sits relative to it. The
soundness guarantee therefore rests entirely on `escapedByMutation`
(`computeEscapedVars`); the order-dependent `escapedByAlias` check is inert for
alloc results (§4) and contributes nothing, but since it sits in an `||` it can
only ever *add* escapes, so its presence cannot break soundness.

One caveat completes the argument: a *later* transform must not re-route a
stack address to a value the escape analysis never saw. Dead-cell reuse (CTGC)
can do exactly that — it rewrites a fresh alloc to reuse dead memory without
re-checking escape — so soundness additionally requires that **a stack-allocated
dead cell is never reused** (§9, Bug 2). With that rule in place, every value
that reuses memory either reuses heap memory (which outlives the frame) or is
allocated afresh and re-judged by the escape check.

---

## 11. Trying it yourself

Dump the analysis decisions for a file:

```sh
cd test-cases
../wybemk --log=Transform --force-all -n -L ../wybelibs final-dump/stack_alloc.o 2>&1 \
   | grep -E "escapedVars:|alloc result:"
```

Each alloc prints a line like:

```
alloc result: ?tmp#3##0:... | escapedByAlias=False | escapedByMutation=False
   | constSize=True | withinLimit=True | alreadyStack=False
   | reuseAvailable=False | reuseIsStack=False => stack-allocate
```

The decision suffix is one of `=> reuse dead cell`, `=> stack-allocate`, or
`=> heap-allocate`. `reuseIsStack=True` is the Bug 2 guard firing: a dead cell
that traces back to a `{stack}` alloc is refused for reuse (so `reuseAvailable`
is `True` but the alloc still stack- or heap-allocates afresh).

Toggle the optimisation off to compare behaviour:

```sh
../wybemk --force-all -x no-stack-alloc -L ../wybelibs execution/<name>
```

Adjust the size threshold:

```sh
../wybemk --force-all --stack-alloc-limit 256 -L ../wybelibs <target>
```

## Types <a id=Types></a>
###                 Type Checking Module SCCs

Our type inference is flow sensitive, that is, types flow from callees to
callers, but not vice versa.  Therefore, types must be uniquely determined by
proc definitions.

Because submodules in a file automatically have access to all items (even
private ones) in their supermodule, submodules in that file are considered to
depend on their supermodules.  Likewise, supermodules automatically import
everything exported by their submodules in the same file, so supermodules
depend on their submodules. This means all modules in a given file are always
in the same module dependency SCC.  Since SCCs are type checked in
topological order, this ensures that all proc calls can only refer to procs
that have already been type checked or are defined in the current SCC.

Type checking is responsible for overloading resolution, therefore during
type checking, there may be multiple possible procs that could be referenced
by an individual call.  To support this, we use a type RoughProcSpec which
represents a proc as best we are able to identify it.  This is only used
during type checking to determine potential call graph SCCs.  Type
checking/inference is then performed bottom-up by potential call graph SCC.

Handling of resources here is a little tricky, because resources in lower
SCCs will have been transformed into parameters, but resources in the current
SCC will not have been transformed.  This problem is unavoidable because types
must be determined (so that overloading can be resolved) before resources can
be transformed.  Therefore, type checking must be prepared to handle both
calls that have had resources transformed to parameters and calls that
haven't.

## Unbranch <a id=Unbranch></a>
This code transforms loops into fresh recursive procs, and ensures
that all conditionals are the last statements in their respective
bodies. Note that conditionals can be nested, but at the end of
the conditional, they must return to the caller. This is handled
by introducing a fresh continuation proc for any code that follows
the conditional. The reason for this transformation is that a
later pass will convert to a logic programming form which
implements conditionals with separate clauses, each of which
returns on completion.

Loops are a little more complicated.  do {a b} c d would be
transformed into next1, where next1 is defined as def next1 {a b
next1}, and break1 is defined as def break1 {c d}.  Then Next
and Break are handled so that they cancel all the following code
in their clause body.  For example, Next a b would be transformed
to just next1, where next1 is the next procedure for that loop.
Similarly Break a b would be transformed to just break1, where
break1 is the break procedure for that loop.  Inside a loop, a
conditional must be handled specially, to support breaking out of
the loop.  Inside a loop, if {a:: b | else:: c} d e would be
transformed to a call to gen1, where gen2 is defined as def gen2
{d e}, and gen1 is defined as def gen1 {a:: b gen2 | else::
c gen2}.  So for example do {a if {b:: Break} c} d e would be
transformed into next1, which is defined as def next1 {a gen1},
gen1 is defined as def gen1 {b:: break1 | else:: gen2},
gen2 is defined as def gen2 {c next1}, and break1 is defined as def
break1 {d e}.

The tricky part of all this is handling the arguments to these
generated procedures.  For each generated procedure, the input
parameters must be a superset of the variables used in the body of
the procedure, and must be a subset of the variables defined prior
to the generated call.  Similarly, the output parameters must be a
a subset of the variables defined in the generated procedure, and
must be superset of the variables that will be used following the
generated call.  Ideally, we would make these the *smallest* sets
satifying these constraints, but later compiler passes remove
- unnecessary parameters, so instead we go with the largest such
sets.  This is determined by the type/mode checker, which already
keeps track of variables known to be defined at each program point.

This code also eliminates other Wybe language features, such as
transforming SemiDet procs into Det procs with a Boolean output
param.  Following unbranching, code will be compiled to LPVM
form by the Clause module; this requires a much simplified input
AST form with the following requirements:
  * All procs, and all proc calls, are Det.
  * All statements but the last in a body are either ProcCalls
    or ForeignCalls or Nops.
  * The final statement in a body can be any of these same
    statement types, or a Cond whose condition is a single
    TestBool, and whose branches are bodies satisfying these
    same conditions.

## Unique <a id=Unique></a>

## UnivSet <a id=UnivSet></a>

## Util <a id=Util></a>

## wybemk <a id=wybemk></a>


# This Document

This document is assembled from the source code of the Wybe compiler
by the top-level Makefile with the command

```
    make src/README.md
```
This command should be rerun whenever new modules are added to the
compiler, or when the documentation is updated, and the resulting
src/README.md file should be pushed to github.

Haskell source files with extension `.hs` should contain a line beginning
with `-- Purpose :` followed by a one-line description.

In Haskell source files, any text between marker lines of the form:
```
-- BEGIN MAJOR DOC
```
and
```
-- END MAJOR DOC
```
will be included in this `README.md` file.  One or more spaces
may separate the `--` from the `BEGIN` or `END` text.

The documentation should be written in markdown notation. Of
course, `--` comment markers at the beginnings of lines, and up to two following
spaces, will be stripped before being interpreted as markdown.
