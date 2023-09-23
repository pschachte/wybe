# Building Wybe

Note that Wybe has been ported to macOS and Linux (Ubuntu) so far.

## Installing prerequisites

### macOS

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

4.  Install the Boehm Garbage Collector development tools

```
    brew install bdw-gc
```

5.  Install LLVM version 9

```
    brew install llvm-hs/llvm/llvm-9
```

6.  Install dwdiff & gtimeout (for testing)

```
    brew install dwdiff coreutils
```

7.  LaTeX is needed for building the documentation.  We recommend
[MacTeX](https://www.tug.org/mactex/).

8.  You may find you have a dependency on libffi.7.dylib, when what you have
    installed is libffi.8.dylib, causing an error like
```
dyld[40396]: Library not loaded: /usr/local/opt/libffi/lib/libffi.7.dylib
```
    If this happens, you can work around it by creating a link to
    `libffi.7.dylib`:
```
    cd /usr/local/opt/libffi/lib
    sudo ln -s libffi.8.dylib libffi.7.dylib
```


### Linux (Ubuntu)

Note that this is an experimental support and only has been tested on Ubuntu 18.04 and 20.04 LTS.

1.  Install Clang

```
    sudo apt-get install clang
```

2.  Install
[The Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/).

```
    wget -qO- https://get.haskellstack.org/ | sh
``` 

3.  Install the Boehm Garbage Collector development tools

```
     sudo apt-get install libgc-dev
```

4.  Install LLVM version 9

```
    sudo apt-get install llvm-9-dev
```

5.  Install libtinfo-dev

```
    sudo apt-get install libtinfo-dev
```

6.  Install dwdiff (for testing)

```
    sudo apt-get install dwdiff
```

### Windows

For Windows, please build under
[Windows Subsystem for Linux](https://learn.microsoft.com/en-us/windows/wsl/) (WSL), following the Linux installation
instructions.

Note:  use the version of `git` under WSL to fetch the wybe
compiler source code from github, not any version of `git` running
under windows.

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

## Installing

1.  Decide on installation location.  The default location for the executable is
    `/usr/local/bin`, with libraries installed in `/usr/local/lib/wybe`.

2.  If the defaults are not what you want, edit the `Makefile` and change the
installation locations `INSTALLBIN` and `INSTALLLIB` to suit.

3.  Do either:
```
    make install
```
(if you have write access to your chosen installation locations), or:
```
    sudo make install
```
(if not).
