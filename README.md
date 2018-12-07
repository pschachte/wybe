Compiler for the Wybe language
==============================

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


