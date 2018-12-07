% The Wybe Compiler
% The Wybe Team
% Fri Dec 7 16:13:46 2018 +1100


To build the compiler, do

    make

This will produce an executable file `wybemk`.

To run the test suite, do

    make test

This will print a `.` for each passed test, and an `X` for each failed test.
Any test that hasn't yet had its expected output specified will print `?`.

The script `update-exp` in this directory goes through all the test cases
whose output is different than the expected output, show the differences,
and prompts whether or not to except the new actual output as correct.
For each test case with no expected output recorded, it also shows the
actual output and prompts whether to accept this as correct.


Subdirectories
--------------

Subdirectories have the following purposes:

+---------------------+-------------------------------------------------+
| documentation       | Documentation of the Wybe language |
+---------------------+-------------------------------------------------+
| wybelibs            | The Wybe standard library |
+---------------------+-------------------------------------------------+



Tour of the compiler
--------------------

The source files in this directory and their purposes are:

+---------------------+-------------------------------------------------+
| AST.hs              | Abstract Syntax Tree for Wybe language |
+---------------------+-------------------------------------------------+
| BinaryFactory.hs    | Deriving AST Types to be Binary instances |
+---------------------+-------------------------------------------------+
| Blocks.hs           | Transform a clausal form (LPVM) module to LLVM |
+---------------------+-------------------------------------------------+
| BodyBuilder.hs      | A monad to build up a procedure Body, with copy propagation |
+---------------------+-------------------------------------------------+
| Builder.hs          | Handles compilation at the module level. |
+---------------------+-------------------------------------------------+
| Callers.hs          | Find all callers for each proc and count static calls per caller |
+---------------------+-------------------------------------------------+
| Clause.hs           | Convert Wybe code to clausal (LPVM) form |
+---------------------+-------------------------------------------------+
| Codegen.hs          | Generate and emit LLVM from basic blocks of a module |
+---------------------+-------------------------------------------------+
| Config.hs           | Configuration for wybe compiler |
+---------------------+-------------------------------------------------+
| DefUse.hs           | Compute defined and used variables for statements and exprs |
+---------------------+-------------------------------------------------+
| Emit.hs             | Emit LLVM code |
+---------------------+-------------------------------------------------+
| Expansion.hs        | Replace certain procedure calls with others |
+---------------------+-------------------------------------------------+
| Flatten.hs          | Flatten function calls (expressions) into procedure calls |
+---------------------+-------------------------------------------------+
| Macho.hs            | Extended version of parser for Mach-O object format files  |
+---------------------+-------------------------------------------------+
| NewParser.hs        | Re-write of the Wybe parser using Parsec. |
+---------------------+-------------------------------------------------+
| Normalise.hs        | Convert parse tree into AST |
+---------------------+-------------------------------------------------+
| ObjectInterface.hs  | Parse and edit a object file. |
+---------------------+-------------------------------------------------+
| Optimise.hs         | Framework to optimise a single module |
+---------------------+-------------------------------------------------+
| Options.hs          | Handle compiler options/switches |
+---------------------+-------------------------------------------------+
| Resources.hs        | Resource checker for Wybe |
+---------------------+-------------------------------------------------+
| Scanner.hs          | Scanner for the Wybe language |
+---------------------+-------------------------------------------------+
| Snippets.hs         | Convenience functions for generation of Wybe AST |
+---------------------+-------------------------------------------------+
| Test.hs             | Test code for NewParser.hs parser |
+---------------------+-------------------------------------------------+
| Types.hs            | Type checker/inferencer for Wybe |
+---------------------+-------------------------------------------------+
| Unbranch.hs         | Turn loops and conditionals into separate procedures |
+---------------------+-------------------------------------------------+
| Util.hs             | Various small utility functions |
+---------------------+-------------------------------------------------+
| wybemk.hs           | Wybe compiler/builder main code |
+---------------------+-------------------------------------------------+



AST.hs
------

**Purpose**: Abstract Syntax Tree for Wybe language


BinaryFactory.hs
----------------

**Purpose**: Deriving AST Types to be Binary instances


Blocks.hs
---------

**Purpose**: Transform a clausal form (LPVM) module to LLVM


BodyBuilder.hs
--------------

**Purpose**: A monad to build up a procedure Body, with copy propagation


Builder.hs
----------

**Purpose**: Handles compilation at the module level.

The wybe compiler handles module dependencies, and builds
executables by itself, without the need for build tools like
make.  To keep compile times manageable while supporting
optimisation, we build bottom-up, ensuring that all a module's
imports are compiled before compling the module itself.  In the
case of circular module dependencies, each strongly-connected
component in the module dependency graph is compiled as a unit.

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

The build process makes these steps for each SCC in the module
dependency graph (with responsible modules):

  1.  The code is read and flattened (happens before this module is invoked)
  2.  Imported modules are loaded, building them if needed (this module)
  3.  The types of exported procs are validated (Types)
  4.  Resource imports and exports are checked (Resources)
  5.  Proc argument types and modes are checked (Types)
  6.  Proc resources are checked and transformed to args (Resources)
  7.  Branches, loops, and nondeterminism are transformed away (Unbranch)
  8.  Procs are compiled to clausal form (Clause)
  9.  Procs are optimised (Optimise)

This is the responsibility of the compileModSCC function.

Callers.hs
----------

**Purpose**: Find all callers for each proc and count static calls per caller


Clause.hs
---------

**Purpose**: Convert Wybe code to clausal (LPVM) form


Codegen.hs
----------

**Purpose**: Generate and emit LLVM from basic blocks of a module


Config.hs
---------

**Purpose**: Configuration for wybe compiler


DefUse.hs
---------

**Purpose**: Compute defined and used variables for statements and exprs


Emit.hs
-------

**Purpose**: Emit LLVM code


Expansion.hs
------------

**Purpose**: Replace certain procedure calls with others


Flatten.hs
----------

**Purpose**: Flatten function calls (expressions) into procedure calls


Macho.hs
--------

**Purpose**: Extended version of parser for Mach-O object format files 


NewParser.hs
------------

**Purpose**: Re-write of the Wybe parser using Parsec.


Normalise.hs
------------

**Purpose**: Convert parse tree into AST


ObjectInterface.hs
------------------

**Purpose**: Parse and edit a object file.


Optimise.hs
-----------

**Purpose**: Framework to optimise a single module


Options.hs
----------

**Purpose**: Handle compiler options/switches


Resources.hs
------------

**Purpose**: Resource checker for Wybe


Scanner.hs
----------

**Purpose**: Scanner for the Wybe language


Snippets.hs
-----------

**Purpose**: Convenience functions for generation of Wybe AST


Test.hs
-------

**Purpose**: Test code for NewParser.hs parser


Types.hs
--------

**Purpose**: Type checker/inferencer for Wybe


Unbranch.hs
-----------

**Purpose**: Turn loops and conditionals into separate procedures


Util.hs
-------

**Purpose**: Various small utility functions


wybemk.hs
---------

**Purpose**: Wybe compiler/builder main code



This Document
-------------

This document is assembled from the source code of the Wybe compiler.
Directories are documented if they contain a file named `README`;
this file should contain a single line describing the purpose of the
directory.

Haskell source files with extension `.hs` should contain a line beginning
with `-- Purpose :` followed by a one-line description.

In Haskell source files, any text between markers of the form:
```
-- BEGIN MAJOR DOC
```
and
```
-- END MAJOR DOC
```
will be included in this `README.md` file.  The documentation should be
written in markdown notation (as understood by pandoc, with the
`grid_tables` option enabled, so tables can be used).  Of course,
`--` comment markers at the beginnings of lines, and one or two
following spaces, will be stripped before being interpreted as
markdown.