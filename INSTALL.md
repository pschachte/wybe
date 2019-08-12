# Building Wybe

Note that Wybe has only been ported to Mac OS X so far.

## Installing prerequisites

1.  Ensure XCode is installed:
```
    xcode-select --install
```

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
    brew install dwdiff
```

7.  LaTeX is needed for building the documentation.  We recommend
[MacTeX](https://www.tug.org/mactex/).


## Building

1.  Just do:
```
    make
```


## Testing

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
