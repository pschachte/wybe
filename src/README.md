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
| [Normalise.hs](#Normalise)   | Convert parse tree into an AST |
| [ObjectInterface.hs](#ObjectInterface)| Parse and edit a object file. |
| [Optimise.hs](#Optimise)     | Framework to optimise a single module |
| [Options.hs](#Options)       | Handle compiler options/switches |
| [Parser.hs](#Parser)         | Parser for the Wybe language using Parsec. |
| [Resources.hs](#Resources)   | Resource checker for Wybe |
| [Scanner.hs](#Scanner)       | Lexical scanner for the Wybe language |
| [Snippets.hs](#Snippets)     | Convenience functions for generation of Wybe AST |
| [Transform.hs](#Transform)   | Transform LPVM after alias analysis |
| [Types.hs](#Types)           | Type checker/inferencer for Wybe |
| [Unbranch.hs](#Unbranch)     | Turn loops and conditionals into separate procedures |
| [Util.hs](#Util)             | Various small utility functions |
| [wybemk.hs](#wybemk)         | Wybe compiler/builder main code |


# Modules in more detail


## AST --  Wybe Abstract Syntax Tree and LPVM representation


## ASTShow --  Show Wybe intermediate representation


## AliasAnalysis --  Alias analysis for a single module


## Analysis --  Entry point of all kinds of analysis for a single module


## BinaryFactory --  Deriving AST Types to be Binary instances


## Blocks --  Transform a clausal form (LPVM) module to LLVM


## BodyBuilder --  A monad to build up a procedure Body, with copy propagation


## Builder --  Handles compilation at the module level.

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


## Callers --  Find all callers for each proc and count static calls per caller


## Clause --  Convert Wybe code to clausal (LPVM) form


## Codegen --  Generate and emit LLVM from basic blocks of a module


## Config --  Configuration for wybe compiler


## Emit --  Emit LLVM code


## Expansion --  Replace certain procedure calls with others


## Flatten --  Flatten function calls (expressions) into procedure calls

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

## Macho --  Extended version of parser for Mach-O object format files 


## Normalise --  Convert parse tree into an AST


## ObjectInterface --  Parse and edit a object file.


## Optimise --  Framework to optimise a single module


## Options --  Handle compiler options/switches


## Parser --  Parser for the Wybe language using Parsec.


## Resources --  Resource checker for Wybe


## Scanner --  Lexical scanner for the Wybe language


## Snippets --  Convenience functions for generation of Wybe AST


## Transform --  Transform LPVM after alias analysis


## Types --  Type checker/inferencer for Wybe

###                 Type Checking Module SCCs

Our type inference is flow sensitive, that is, types flow from callees to
callers, but not vice versa.  Therefore, types must be uniquely determined by
proc definitions.

Because submodules automatically have access to all items (even private ones)
in their supermodule, submodules are considered to depend on their
supermodules.  Likewise, supermodules automatically import everything
exported by their submodules, so supermodules depend on their submodules.
This means a module is always in the same module dependency SCC as all its
submodules.

Type checking is responsible for overloading resolution, therefore during
type checking, there may be multiple possible procs that could be referenced
by an individual call.  To support this, we use a type RoughProcSpec which
represents a proc as best we are able to identify it.  This is only used
during type checking to determine potential call graph SCCs.  Type
checking/inference is then performed bottom-up by potential call graph SCC.

## Unbranch --  Turn loops and conditionals into separate procedures

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

## Util --  Various small utility functions


## wybemk --  Wybe compiler/builder main code



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
