# TODO list for the Wybe project

## Fix bugs:
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


## Complete the language:
* Support laziness declaration for func/proc arguments
    * Pass a closure
    * Lazy arguments are evaluated before passing to any other func/proc except
      as a lazy input argument
* Fix the syntax!
    * Support curley braces to specify sets and maps
    * Interpolation (in strings, arrays, sets, and maps)
        * "...@foo..." means "..." `,,` foo `,,` "..."
	* "...@(foo(bar,baz))..." means "..." `,,` foo(bar,baz) `,,` "..."
	* [foo,@bar(baz),zip] means [foo] `,,` bar(baz) `,,` [zip]
	* if `,,` can run backwards, then [?foo,@?bar] and [@?foo,bar] can be patterns
    	* with this, do we need `[ ... | ...]` syntax?
* Support "commutative" resources, which don't need to be threaded everywhere
* Support unicode
* Investigate situation calculus
    * Should resources be called "fluents"?
    * Does S.C. suggest how resources should be split up and sewn back together?


## Library:
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
* Extend read-after-write to support read with intervening write with different
  offset
* Keep track of bounds on tags to avoid unnecessary tests and allow tag switches
* Revise handling of inverse ops and other implied instructions to search for
  instruction variants instead of inserting them into table
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
