# TODO list for the Wybe project

## Fix bugs:
* `test-cases/stmt_if.wybe`
* `test-cases/tests.wybe`
* Have wybemk build executable without -f flag when .o file exists
* Rework mode checking to treat any argument with any outputs as an
  output, and to handle any inputs that are part of an output argument
  by producing the output and then testing for equality with the input.


## Documentation:
* Write Wybe intro
* Write setup/build/install document


## Complete the implementation:
* Optimise each module dependency SCC by finding call graph SCCs *across*
  the whole module SCC.  This ensures non-mutually-recursive procs are
  optimised before callers, even across mutually-dependent modules.
* Infer when test calls are certain to succeed and consider them Det
* Generate print and comparison methods for user defined types
* Generate string function for user defined types, once we have decent strings
* Support many non-constant constructors
* Handle building `.o` files for foreign code using `make` or alternatives
* Ensure a variable both assigned and used in a statement has the assignment
  happen first, wherever it appears in the statement
* Support versioning for libraries
* Support auto-download for libraries (with sandboxing and caching)
* Correctly handle top-level resources, making them initialised variables in the
  generated main function.
    * commandline resource initialised from argc and argv command line
    * exitstatus resource initialised to 0, can be set, determines main exit
      status
* Generate multi-way switches (computed gotos) for cascading if-then-else
  testing equality on the same variable
* Pull procs only called from one proc into the definition of the caller proc,
  making them blocks in the caller


## Error checking:
* `test-cases/escape_recursion1.wybe` should report compiler error if not all branches bind all outputs
* Error if foreign call has no outputs; suggest use !I/O.
* Ensure no statement binds the same variable multiple times


## Improve error handling:
* Error message for foreign call with no output (need to thread something)
* Give meaningful message for errors detected in generated procs
* Detect and report use of uninitialised variables, including update
   of uninitialised variables
* Type and mode check foreign call arguments for llvm and lpvm calls;
  don't abort compiler on errors.
* May want to delay determinism checking until we do inlining, so


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
* Provide way to specify top-level initial value for resources with code
* Support automatic type conversion?
    * Consider a function *t* whose output is of type *t* to coerce to type *t*
    * The function must be total (det)
    * The function is required to be an injection
    * The function is required not to "lose information"
* Design/implement interface to call wybe from C
* Support polymorphism
* Provide switch-on-constructor syntax and implementation
* Support subtypes
* Support generators (nondet procs/lazy lists)
* Support optional and named arguments
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
* Support argument annotation demanding that value not be cloned (it can
  be shared and not mutated, or mutated and not shared)


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
* Multiple specialisation
* Inter-procedure common sub-expression elimination
* Code hoisting
* Destructive update transformation (CTGC)
* Last call modulo construction optimisation (transform proc output
  into input of the address to store the output in, and then construct
  the output with uninitialised field(s), and pass the address(es)
  as argument(s) in the recursive call)
* delay instructions until their outputs are needed
    * delay into one arm of a branch if only one arm needs the outputs


## Build System:
* Record procs before inlining to allow rebuild when dependencies change


## Blocks:
* add Procedure id for global module level procedures
* Insert target triple into the definition of LLVMAST.Module during
  creation.


## Emit:
* Improve Logging


## Make:
* Add creation of cabal sandbox and dependency install


## Porting:
* to Linux
* to Windows
* Rewrite compiler in Wybe
