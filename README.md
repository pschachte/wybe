# The Wybe Programming Language

Wybe is a programming language intended to combine the best features of
declarative and imperative programming.  It is in an early state of
development.


## Building Wybe
<details>
<summary>Click to expand installation instructions</summary>

Note that Wybe has only been ported to Mac OS X so far.

### Installing prerequisites

1.  Ensure XCode is installed:

      `xcode-select --install`

    This needs to be redone after each OS upgrade.

2.  Install [Homebrew](https://brew.sh/).

3.  Install
[The Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/).

```
    brew install haskell-stack
```

4.  Install the Boehm Garbage Collector development tools:

```
    brew install bdw-gc
```

5.  Install LLVM version 6

```
    brew install llvm-hs/llvm/llvm-6.0
```

6.  Install dwdiff (for testing)

```
    brew install llvm-hs/llvm/llvm-6.0
```

7.  LaTeX is needed for building the documentation.  We recommend
[MacTeX](https://www.tug.org/mactex/).


### Building

1.  Just do:
```
    make
```


### Testing

1.  Just do:
```
    make test
```

This will show a . for each passed test, an X for each failed test, and a ?
for each new test (which hasn't had expected output specified yet).
Currently, some tests fail.

The script `update-exp` in this directory goes through all the test cases
whose output is different than the expected output, show the differences,
and prompts whether or not to except the new actual output as correct.
For each test case with no expected output recorded, it also shows the
actual output and prompts whether to accept this as correct.
</details>


## Subdirectories
<details>
<summary>Click to expand documentation of subdirectories</summary>

Subdirectories have the following purposes:


| subdirectory        | Purpose                             |
|---------------------|------------------------------------ |
| src                 | Compiler source code                |
| documentation       | Documentation of the Wybe language  |
| test-cases          | The current test suite              |
| wybelibs            | The Wybe standard library           |
| publications        | Papers and presentations about wybe |
| legacy              | Old, obsolete stuff                 |
| speculative         | Some musings about the language     |

</details>

## The Wybe Language

The Wybe language is intended to be easy to learn and easy to use, but
powerful and efficient enough for for practical use.  It is intended to
support best programming practice, but not necessarily *common* practice.

Wybe combines the best features of declarative and imperative languages,
in particular borrowing features from functional, logic, imperative, and
object oriented languages, but does not neatly fit into any of these
paradigms.  Its main organising principle is that *values* are
immutable, but *variables* may be reassigned.  This means that values
may be passed around a will without worrying that they may be modified.

### Hello, World!

Code appearing at the top level of a file is executed when the program
is run, so Hello, World! in Wybe is quite simple:
```
    # Print a friendly greeting
    !println("Hello, World!")
```

Wybe comments begin with a hash (`#`) character and continue to the end
of the line.

The need for the opening exclamation point will be explained in Section
[Resources](#resources).


### Building

Use `wybemk` to build object and executable files.  If the above program
is put in a file named `hello.wybe`, then an executable program can be
built with the command:

```
    wybemk hello
```

Note that `wybemk` is like `make` in that you give it the name of the
file you want it to build, and it figures out what files it needs
to compile.


### Types

Wybe has the usual complement of primitive types:

| Type     | Meaning                                  |
| -------- | ---------------------------------------- |
| `int`    | Fixed precision integer (32 or 64 bits)  |
| `float`  | Double precision floating point number   |
| `bool`   | Boolean; either `true` or `false`        |
| `string`   | Character string (double quotes)   |
| `char`   | Individual ascii character (single quotes) |


### Variables
Variable names begin with a letter (upper or lower case) and follow with
any number of letters, digits, and underscores.

A variable mention may *use* or *assign* its value.  If the variable
name is preceded by a question mark (`?`), the mention assigns the
variable a (new) value; without the question mark prefix, the mention
uses the variable's current value.  It does not matter which side of an
equal sign the variable appears; only its prefix determines whether the
variable is assigned or used.

```
    ?x = 42              # gives x the value 42
    42 = ?x              # also gives x the value 42
    some_proc(x, ?y, ?z) # uses x, assigns y and z
```

A variable mention may *both* use and assign its value if it is preceded
with an exclamation mark (`!`).

```
    incr(!x)   # increment x (both uses and reassigns x)
```

### Functions
### Procedures
### Functions *are* procedures
### Resources
### Modes
### Tests
### Selection and iteration
### Modules
### User defined types
### Foreign interface
