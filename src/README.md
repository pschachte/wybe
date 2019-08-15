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
| [DefUse.hs](#DefUse)         | Compute defined and used variables for statements and exprs |
| [Emit.hs](#Emit)             | Emit LLVM code |
| [Expansion.hs](#Expansion)   | Replace certain procedure calls with others |
| [Flatten.hs](#Flatten)       | Flatten function calls (expressions) into procedure calls |
| [Macho.hs](#Macho)           | Extended version of parser for Mach-O object format files  |
| [NewParser.hs](#NewParser)   | Re-write of the Wybe parser using Parsec. |
| [Normalise.hs](#Normalise)   | Convert parse tree into AST |
| [ObjectInterface.hs](#ObjectInterface)| Parse and edit a object file. |
| [Optimise.hs](#Optimise)     | Framework to optimise a single module |
| [Options.hs](#Options)       | Handle compiler options/switches |
| [Resources.hs](#Resources)   | Resource checker for Wybe |
| [Scanner.hs](#Scanner)       | Scanner for the Wybe language |
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

Once the code and dependencies for all modules in an SCC are
read, flattened, and recorded in each of the modules, and all
dependent (but not mutually dependent) modules are fully
compiled, the build process makes these steps for each module
SCC:

  1.  The type dependencies are topologically sorted and SCCs
      identified, type representations are determined one SCC at a time,
      and code is generated for all constructors, accessors,
      mutators, and utilities (Types)
  2.  Resource imports and exports are checked (Resources)
  3.  The types of exported procs are validated (Types)
  4.  Proc argument types and modes are checked, and called
      procs are resolved (Types)
  5.  Proc resources are checked and transformed to args (Resources)
  6.  Branches, loops, and nondeterminism are transformed away (Unbranch)
  7.  Call graph SCCs are identified and topologically sorted.
      The following steps are performed on call graph SCC at a
      time, buttom up.
  8   Procs are compiled to clausal form (Clause)
  9.  Procs are optimised (Optimise)


## Callers

**Purpose**: Find all callers for each proc and count static calls per caller


## Clause

**Purpose**: Convert Wybe code to clausal (LPVM) form


## Codegen

**Purpose**: Generate and emit LLVM from basic blocks of a module


## Config

**Purpose**: Configuration for wybe compiler


## DefUse

**Purpose**: Compute defined and used variables for statements and exprs


## Emit

**Purpose**: Emit LLVM code


## Expansion

**Purpose**: Replace certain procedure calls with others


## Flatten

**Purpose**: Flatten function calls (expressions) into procedure calls


## Macho

**Purpose**: Extended version of parser for Mach-O object format files 


## NewParser

**Purpose**: Re-write of the Wybe parser using Parsec.


## Normalise

**Purpose**: Convert parse tree into AST


## ObjectInterface

**Purpose**: Parse and edit a object file.


## Optimise

**Purpose**: Framework to optimise a single module


## Options

**Purpose**: Handle compiler options/switches


## Resources

**Purpose**: Resource checker for Wybe


## Scanner

**Purpose**: Scanner for the Wybe language


## Snippets

**Purpose**: Convenience functions for generation of Wybe AST


## Transform

**Purpose**: Transform LPVM after alias analysis


## Types

**Purpose**: Type checker/inferencer for Wybe


## Unbranch

**Purpose**: Turn loops and conditionals into separate procedures


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
