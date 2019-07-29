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

2.  Install the Boehm Garbage Collector development tools:

      `brew install bdw-gc`

3.  Install LLVM version 6

      `brew install llvm-hs/llvm/llvm-6.0`

4.  Install dwdiff

      `brew install llvm-hs/llvm/llvm-6.0`

### Building

1.  Just do:
      `make`


### Testing

1.  Just do:
      `make test`

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
powerful enough for for practical use.  It is intended to support best
programming practice, but not necessarily *common* practice.

Wybe combines the best features of declarative and imperative languages,
in particular borrowing features from functional, logic, imperative, and
object oriented languages, but does not neatly fit in any of these
paradigms.
