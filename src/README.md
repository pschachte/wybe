# Wybe compiler

The architecture of the Wybe compiler has the following structure:

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

| File                         | Purpose                                                  |
| ---------------------------- | -------------------------------------------------------- |
| [AST.hs](#AST)               | Wybe Abstract Syntax Tree and LPVM representation |
| [ASTShow.hs](#ASTShow)       | Show Wybe intermediate representation |
| [AliasAnalysis.hs](#AliasAnalysis)| Alias analysis for a single module |
| [Analysis.hs](#Analysis)     | Entry point of all kinds of analysis for a single module |
| [BinaryFactory.hs](#BinaryFactory)| Deriving AST Types to be Binary instances |
| [Blocks.hs](#Blocks)         | Transform a clausal form (LPVM) module to LLVM |
| [BodyBuilder.hs](#BodyBuilder)| A monad to build up a procedure Body, with copy propagation |
| [Builder.hs](#Builder)       | Handles compilation at the module level. |
| [Callers.hs](#Callers)       | Find all callers for each proc and count static calls per caller |
| [Clause.hs](#Clause)         | Convert Wybe code to clausal (LPVM) form |
| [Codegen.hs](#Codegen)       | Generate and emit LLVM from basic blocks of a module |
| [Config.hs](#Config)         | Configuration for wybe compiler |
| [Emit.hs](#Emit)             | Emit LLVM code |
| [Expansion.hs](#Expansion)   | Replace certain procedure calls with others |
| [Flatten.hs](#Flatten)       | Flatten function calls (expressions) into procedure calls |
| [Macho.hs](#Macho)           | Extended version of parser for Mach-O object format files  |
| [NewParser.hs](#NewParser)   | Parser for the Wybe language using Parsec. |
| [Normalise.hs](#Normalise)   | Convert parse tree into an AST |
| [ObjectInterface.hs](#ObjectInterface)| Parse and edit a object file. |
| [Optimise.hs](#Optimise)     | Framework to optimise a single module |
| [Options.hs](#Options)       | Handle compiler options/switches |
| [Resources.hs](#Resources)   | Resource checker for Wybe |
| [Scanner.hs](#Scanner)       | Lexical scanner for the Wybe language |
| [Snippets.hs](#Snippets)     | Convenience functions for generation of Wybe AST |
| [Transform.hs](#Transform)   | Transform LPVM after alias analysis |
| [Types.hs](#Types)           | Type checker/inferencer for Wybe |
| [Unbranch.hs](#Unbranch)     | Turn loops and conditionals into separate procedures |
| [Util.hs](#Util)             | Various small utility functions |
| [wybemk.hs](#wybemk)         | Wybe compiler/builder main code |


# Modules in more detail


## AST

**Purpose**: Wybe Abstract Syntax Tree and LPVM representation


## ASTShow

**Purpose**: Show Wybe intermediate representation


## AliasAnalysis

**Purpose**: Alias analysis for a single module


## Analysis

**Purpose**: Entry point of all kinds of analysis for a single module


## BinaryFactory

**Purpose**: Deriving AST Types to be Binary instances


## Blocks

**Purpose**: Transform a clausal form (LPVM) module to LLVM


## BodyBuilder

**Purpose**: A monad to build up a procedure Body, with copy propagation


## Builder

**Purpose**: Handles compilation at the module level.

The wybe compiler handles module dependencies, and builds
executables by itself, without the need for build tools like
make.  The function buildTarget is responsible for determining
what source files need to be compiled, and for building the
final outputs (whether executable, object file, archive, etc.).

To keep compile times manageable while supporting optimisation,
we compile modules bottom-up, ensuring that all a module's
imports are compiled before compling the module itself. In the
case of circular module dependencies, each strongly-connected
component in the module dependency graph is compiled as a unit.
This is handled by the compileModule function, which includes
the functionality for finding the SCCs in the module dependency
graph. The monadic functions enterModule and exitModule,
imported from the AST module, implement the SCC functionality,
with exitModule returning a list of modules that form an SCC.
Between enterModule and exitModule, the Normalise.normalise
function is called to record the code of the module and to
record all its dependencies. Each SCC is compiled by the
compileModSCC function.

One shortcoming of the bottom-up approach is that some analyses
are best performed top-down.  For example, we can only eliminate
unneeded procedures when we've seen all the calls to all
procedures in the module.  By compiling bottom-up, we do not have
access to this information.  Our solution to this problem is to
perform the top-down analysis after the bottom-up compilation,
generating results that we can use for the next compilation.  If
the top-down analysis produces results that conflict with the
previous top-down analysis, so that the compilation produced
invalid results, then we must re-compile enough of the program to
fix the problem.  It is hoped that this will happen infrequently
enough that the time saved by not usually having to make separate
traversals for analysis and compilation will more than make up
for the few times we need to recompile.

Ensuring that all compiler phases happen in the right order is
subtle, particularly in the face of mutual module dependencies.
Following are the ordering dependencies.

* Types: the types a type depends on need to have been processed
before the type itself, so that sizes are known. In the case of
recursive or mutually recursive type dependencies, all types in
the recursion must be pointers. Types are transformed into
submodules, and constructors, deconstructors, accessors,
mutators, and auxiliary type procedures (equality tests, plus
eventually comparisons, printers, pretty printers, etc.) are all
generated as procedures within those submodules.  Therefore,
these must be handled as submodules are.

* Resources:  the resources a resource depends on must have been
processed before the resource itself.  (We currently don't
support defining resources in terms of others, but the plan is
to support that.)  The types in the module that defines a
resource, and all module dependencies, must have been processed
at least enough to know they have been defined to process the
resource declaration.

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

* Submodules: the submodules of a module, including the types,
must be processed as mutual dependencies of that module, which
they are. The nested submodules of a module (including types)
have access to all public and private members of the parent
module, and the parent has access to all public members of the
parent, so they are mutual dependencies.

This means only minimal processing can be done before module
dependencies are noted and read in.  So we handle all these
dependencies by initially reading a module to be compiled and
handling contents as follows:

* Types:  create and enter the submodule, note that parent
imports it, and process its constructors and other contents.

* Submodules:  create and enter the submodule, note that parent
imports it, and process its contents.

* Resources:  Record for later processing.

* Pragmas:  Record for later processing.

* Constructors: record for later type layout, code generation,
etc.

* Top level statements:  add statements to the special "" proc
in the module, creating it if necessary.

* Procs and functions:  record them for later normalisation,
analysis, optimisation, etc.

Once we reach the end of a module or submodule, we call
exitModule, which returns a list of modules that form an SCC in
the module dependency graph.  That list is passed to
compileModSCC, which does the following:

  1. Traverse all recorded type submodules in the module list
     finding all type dependencies; topologically sort them and
     identify SCCs. For each SCC:

       1. Determine the type representation for all
          constructors.

       2. Record the primitive representation of the type.

       3. Generate and record all constructor, accessor,
          mutator, and utility procs.

     This is handled in the Normalise module.

  2. Check all resource imports and exports. (Resources)

  3. Normalise all recorded procs in their modules, including
     generated constructors, etc. (Normalise)

  4. Validate the types of exported procs. (Types)

  5. Check proc argument types and modes are checked, and
     resolve called procs. (Types)

  6. Check proc resources and transform them to args.
    (Resources)

  7. Transform away branches, loops, and nondeterminism.
     (Unbranch)

  8. Topologically sort proc call graph and identify SCCs.  For
     each SCC, bottom-up, do the following:

       1. Compile procs to clausal form (Clause)

       2. Optimise procs (Optimise)


## Callers

**Purpose**: Find all callers for each proc and count static calls per caller


## Clause

**Purpose**: Convert Wybe code to clausal (LPVM) form


## Codegen

**Purpose**: Generate and emit LLVM from basic blocks of a module


## Config

**Purpose**: Configuration for wybe compiler


## Emit

**Purpose**: Emit LLVM code


## Expansion

**Purpose**: Replace certain procedure calls with others


## Flatten

**Purpose**: Flatten function calls (expressions) into procedure calls


## Macho

**Purpose**: Extended version of parser for Mach-O object format files 


## NewParser

**Purpose**: Parser for the Wybe language using Parsec.


## Normalise

**Purpose**: Convert parse tree into an AST


## ObjectInterface

**Purpose**: Parse and edit a object file.


## Optimise

**Purpose**: Framework to optimise a single module


## Options

**Purpose**: Handle compiler options/switches


## Resources

**Purpose**: Resource checker for Wybe


## Scanner

**Purpose**: Lexical scanner for the Wybe language


## Snippets

**Purpose**: Convenience functions for generation of Wybe AST


## Transform

**Purpose**: Transform LPVM after alias analysis


## Types

**Purpose**: Type checker/inferencer for Wybe


## Unbranch

**Purpose**: Turn loops and conditionals into separate procedures

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
the loop.  Inside a loop, if {a:: b | otherwise:: c} d e would be
transformed to a call to gen1, where gen2 is defined as def gen2
{d e}, and gen1 is defined as def gen1 {a:: b gen2 | otherwise::
c gen2}.  So for example do {a if {b:: Break} c} d e would be
transformed into next1, which is defined as def next1 {a gen1},
gen1 is defined as def gen1 {b:: break1 | otherwise:: gen2},
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

## Util

**Purpose**: Various small utility functions


## wybemk

**Purpose**: Wybe compiler/builder main code



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
