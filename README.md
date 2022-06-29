![Wybe logo](assets/blue.svg)

# The Wybe Programming Language

Wybe is a programming language intended to combine the best features of
declarative and imperative programming.  It is at an early stage of
development, and is not yet suitable for serious use.

The leading principle in the design of the language is
*interface integrity*, which means that all the information flowing into and out of a procedure or function flows through its interface.
This ensures that there are no hidden effects of a call &mdash;
you can always tell what effects a call could possibly have without needing to
look at its implementation.

The language is documented in the Wybe [user guide](WYBE.md) file.
Start there to get a feeling for the language.

To use it, you will need to build the compiler.
This requires a recent [Haskell compiler](https://www.haskell.org/)
and many of its libraries,
as well as the [LLVM compiler infrastructure](https://llvm.org/).
Currently, the compiler supports recent versions of macOS and Linux (Ubuntu).
All this is documented in the
[installation instructions](INSTALL.md).

See the [SUBDIRECTORIES.md](SUBDIRECTORIES.md) file for
a tour of all the directories making up the Wybe project.
In particular, the source code of the compiler is in the `src` subdirectory.
The file [src/README.md](src/README.md), which is (re-)built by the Makefile,
describes the architecture of the compiler and gives more detail about the
files comprising the compiler.

There is a (growing) [list of programming and research projects](https://github.com/pschachte/wybe/issues?q=is%3Aopen+label%3A%22research+project%22+-label%3A%22in+progress%22)
to further develop the Wybe language.

We are indebted to the several [contributors](CONTRIBUTORS.md)
to the Wybe project, and welcome pull requests through
[GitHub](https://github.com/pschachte/wybe/pulls) if you
would like to contribute to the project.
