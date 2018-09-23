% The Wybe Programming Language
% Peter Schachte
% 31 August 2018

Wybe is a new programming language intended to combine the best features of
declarative and imperative programming.  It is rather simple, but quite
safe and powerful.

## Hello, World

To produce a Wybe program, create a file whose name ends in `.wybe`.
Ordinary Wybe statements at the top level of the file (i.e., not within a
function or procedure definition) are executed when the file is compiled
and run.  For example, a Wybe program to print "Hello, World" would be
written like this:


    !println("Hello, world!")

The `println` procedure prints out a string followed by a newline
character.  The exclamation point at the beginning of the line tells Wybe
that the statement performs input/output.  This will be explained in
greater depth in the section on [Resources](#Resources).

Multiple statements may be written, and they will be executed in order.
Comments begin with a hash (#) character and extend to the end of the line.

    !print("Hello, ")     # print the first word
    !println("world!")    # print the rest and end the line

## <a name="Compiling"></a>Compiling a Wybe program

To compile a Wybe program from a command line, use the program `wybemk` and
specify the *output* file you wish to produce.  For example, if either of
the above programs is put into a file named `hello.wybe`, it can be
compiled using the command

    % wybemk hello

to produce an executable file named `hello`.  This works regardless of the
number of files and libraries used in the project.

Ordinarily, `wybemk` will simply do its job without printing anything. If
it cannot produce the requested output, it will print error messages
describing the problem. If all goes to plan, this file can then be executed
at the command line:

    % ./hello
    Hello, world!

The compiler can also be used to produce an object (`.o`) file rather than
an executable file by specifying that on the command line:

    % wybemk hello.o

## <a name="Variables"></a>Variables and assignment

Variables in Wybe begin with a letter (upper or lower case), and follow
with any number of letters, digits, and underscore (_) characters, like any
number of other programming languages. What is unlike other languages is
that a variable is only assigned by a statement if it is immediately
preceded by a question mark (?). A variable may also be both used and
assigned by a statement by preceding it with an exclamation point (!), as
we will see below. If not preceded by either of these, the expression only
uses the variable.

For example:

    ?msg = "Hello, world!"
    !println(msg)

The first statement assigns to the variable `msg` because it has a question
mark before it, _not_ because it appears to the left of the equal sign.
The second uses `msg` because it is not preceded by a question mark.
This code could equally well have been written as:

    "Hello, world!" = ?msg
    !println(msg)

Had the first statement omitted the question mark, it would instead have
tested if `msg` is equal to `"Hello, world!"`. But the first mention of a
variable _must_ assign it, so this would be an error, and would be reported
as an uninitialised variable by the Wybe compiler.

## <a name="Control"></a>Control statements
### <a name="Conditional"></a>Conditional statements
Wybe's conditional statement has the form:

>    `if {` *test* `::` *stmts*  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`|` *test* `::` *stmts*  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`|` *test* `::` *stmts*  
>    `}`

Each *stmts* parts can include as many statements as needed. You may have as
many *test* `::` *stmts* pairs as you like; Wybe will execute the *stmts*
following the first *test* that succeeds, and ignore all later tests and their
corresponding statements. If no *test* succeeds, the `if` statement will
complete without executing any *stmts*.

### <a name="Loops"></a>Looping statements

Wybe has only one looping construct:

>    `do {`  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;  *stmts*  
>    `}`

Within the *stmts* sequence, however, the following constructs can be used:

`break`
:   immediately exits the loop

`continue`
:   immediately returns to the top of the loop and begins the next iteration

`while` *test*
:   immediately exits the loop unless *test* succeeds.
    Equivalent to `if {  not` *test* :: break `}`

`until` *test*
:   immediately exits the loop if *test* succeeds.
    Equivalent to `if {` *test* :: break `}`

`when` *test*
:   continues executing the loop body only if the *test* succeeds; otherwise
    it immediately returns to the top of the loop.
    Equivalent to `if {  not` *test* :: continue `}`

`unless` *test*
:   continues executing the loop body unless the *test* succeeds; otherwise
    it immediately returns to the top of the loop.
    Equivalent to `if {` *test* :: continue `}`

For example, a traditional `while` loop has the form:

>   `do { while ` *test*  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;  *stmts*  
>   }

and a traditional `do` ... `while` loop has the form:

>   `do {` *stmts*  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; `while ` *test*  
>   }

Alternatively, the `while` can be placed in the middle of the loop, in which
case, the code before the `while` will be executed one or more times, while the
code after the `while` will be executed zero or more times.  Also, `until` can
be used to invert the sense of the test.  For example:

>   `do { ` print prompt  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; read user input  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; `until` input is valid  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; print admonition about what input is valid  
>   }

will repeatedly print a prompt and read user input until valid input is
received, printing a message indicating that the input was invalid each time it
is invalid.

## <a name="Types"></a>Type declarations
## <a name="Procedures"></a>Defining procedures
## <a name="Functions"></a>Defining functions
## <a name="Tests"></a>Tests
## <a name="Resources"></a>Resources
## <a name="Foreign"></a>Interfacing to foreign code
## <a name="Library"></a>The Wybe library
