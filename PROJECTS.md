# Potential programming projects for Wybe

Here are some programming and research projects that would extend or
improve the Wybe language.

## Secure package and build system

This project will provide a way for the Wybe compiler to download and
compile a module from an external source, such as github or an ftp site.
This, of course, raises significant security concerns, which this
project must also address, by providing a permission system, so that
external packages must request access to any capabilities that have
security implications, such as file system or operating system access.
Other considerations include supporting package versions, and
downloading the right version of each package, and supporting both local
and system-wide download of packages.


## GC-free automatic memory management

This project will replace the garbage collector in the Wybe system with
compiler-mediated direct allocation and deallocation. The details are to be
determined, but there are a number of different strategies that can be employed.
Structures can be allocated on the stack if they won't escape the creating
procedure, and couldn't be deallocated much sooner than procedure exit. They can
be allocated on the heap and deallocated after the last use, malloc/free style.
When fixed number of structures will last be used about the same time, they can
be allocated and freed in a single block allocation.  When a variable number of
structures will last be used around the same time, they can be allocated from a
chain of buffers would be passed from procedure to procedure as an extra
argument.  Where the analysis cannot determine how many structures maintain
pointers to a structure, the compiler can generate code to maintain a reference
count at runtime, and free the structure when the count goes to 0.

The basis of all this would be a very precise pointer analysis.  One
advantage of Wybe in this is that aliasing is not relevant semantically, so the
compiler can choose to copy structures rather than sharing them, if that makes
memory management easier.

This is probably a PhD-scale project.

## Generators

Tests in Wybe are akin to the Maybe monad in Haskell, or Prolog predicates that
can fail (sometimes called *semidet*).  *Generators* are a planned feature like
the list Monad in Haskell or Prolog predicates that can have more than one
solution(*nondet*).  This would work in Wybe by providing a `|` operator that
indicates that both what comes before and what comes after are results.  This
can be used in an expression, so the expression has multiple values, or as a
statement, so the outputs of both statement sequences are valid outputs.
Generators can then be used in a `for` loop to iterate over the results of the
generator.
