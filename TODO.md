# TODO list for the Wybe project

## Fix bugs:
* Rework mode checking to treat any argument with any outputs as an
  output, and to handle any inputs that are part of an output argument
  by producing the output and then testing for equality with the input.
* Fix regression:  unused input argument testing not working

## Complete the implementation:
* Optimise each module dependency SCC by finding call graph SCCs *across*
  the whole module SCC.  This ensures non-mutually-recursive procs are
  optimised before callers, even across mutually-dependent modules.
* Generate print and comparison methods for user defined types
* Generate string function for user defined types, once we have decent strings
* Support many non-constant constructors
* Ensure a variable both assigned and used in a statement has the assignment
  happen first, wherever it appears in the statement
* Support versioning for libraries
* Support auto-download for libraries (with sandboxing and caching)
* Generate multi-way switches (computed gotos) for cascading if-then-else
  testing equality on the same variable
* Pull procs only called from one proc into the definition of the caller proc,
  making them blocks in the caller


## Error checking:
* Error if foreign call has no outputs; suggest use !I/O.
* Ensure no statement binds the same variable multiple times


## Improve error handling:
* Error message for foreign call with no output (need to thread something)
* Give meaningful message for errors detected in generated procs
* Detect and report use of uninitialised variables, including update
   of uninitialised variables
* May want to delay determinism checking until we do inlining


## Complete the language:
* Support higher order procs and functions
* Support laziness declaration for func/proc arguments
    * Pass a closure
    * Lazy arguments are evaluated before passing to any other func/proc except
      as a lazy input argument
* Fix the syntax!
    * At expression level, support infix ops, where the ops are sequences of
      operator characters
    * At statement level, allow unary procs to omit parentheses;
      eg `print foo` instead of `print(foo)`
    * At statement level, support brace-enclosed statement sequence as
      statement; then revise proc body to be single statement
    * Support curley braces to specify sets and maps
    * Interpolation (in strings, arrays, sets, and maps)
        * "...@foo..." means "..." ++ foo ++ "..."
	* "...@(foo(bar,baz))..." means "..." ++ foo(bar,baz) ++ "..."
	* [foo,@bar(baz),zip] means [foo] ++ bar(baz) ++ [zip]
	* if ++ can run backwards, then [?foo,@?bar] and [@?foo,bar] can be patterns
    	* with this, do we need [ ... | ...] syntax?
* Support automatic type conversion?
    * Consider a function *t* whose output is of type *t* to coerce to type *t*
    * The function must be total (det)
    * The function is required to be an injection
    * The function is required not to "lose information"
* Design/implement interface to call wybe from C
* Provide switch-on-constructor syntax and implementation
* Support subtypes
* Support "commutative" resources, which don't need to be threaded everywhere
* Support unicode
* Support relations in place of object identity
    * Allow identities to be created
    * Allow attributes to be associated with identities
    * Allow identities to be related to one another
    * Allow the database to be searched in flexible ways
    * Generate code that:
        * represents rows as data structures;
        * updates the database by destructively updating the structure when
          possible;
        * allows flexible navigation among related objects, flexible search, and
          flexible update
* Support special resources the language automatically assigns:
    * sourcefile:  a string naming the file a call appears in
    * sourceline:  the line a call appears in
    * sourcedate:  the file modifcation date of the source file
    * wybeversion:  the version of the wybe compiler that compiled the module
* Investigate situation calculus
    * Should resources be called "fluents"?
    * Does S.C. suggest how resources should be split up and sewn back together?


## Library:
* Implement decent string type
* Map and set types
* Library of I/O operations using resources for streams
* Command line argument handling using resources
* Expandable array type


## Tooling:
* `wybedoc` utility with *markdown* support
* Wybe code reformatter/beautifier
* Tool to generate .wybe foreign interface file from C `.h` file
* Parser and scanner generators


## Optimisation:
* Update caller counts when inlining proc calls, and don't generate code for
  uncalled private procs
* Generalise common subexpression handling to avoid repeated
  *equivalent* code, such as testing x/=y after already testing x=y.
* Extend read-after-write to support read with intervening write with different
  offset
* Keep track of bounds on tags to avoid unnecessary tests and allow tag switches
* Revise handling of inverse ops and other implied instructions to search for
  instruction variants instead of inserting them into table
* Move some argument threading into memory (global variables)
* Remove unneeded input and unchanged output arguments globally
* Inter-procedure common sub-expression elimination
* Code hoisting
* delay instructions until their outputs are needed
    * delay into one arm of a branch if only one arm needs the outputs
* Remove redundant mutate prim that will be overwritten by following mutates
  e.g. in person1.wybe, the first mutate of lastname could be removed in final LPVM


## Build System:
* Record procs before inlining to allow rebuild when dependencies change


## Porting:
* to Windows
* Rewrite compiler in Wybe
