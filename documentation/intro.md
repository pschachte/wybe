% The Wybe Programming Language
% Peter Schachte
% 31 August 2018

Wybe is a new programming language intended to combine the best features of
declarative and imperative programming.  It is rather simple, but quite
powerful.

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

    % hello
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
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`|` *test* `::` *stmts*  
>    &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`|` *test* `::` *stmts*  
>    `}`

Each *stmts* parts can include as many statements as needed.

### <a name="Loops"></a>Looping statements
## <a name="Types"></a>Type declarations
## <a name="Procedures"></a>Defining procedures
## <a name="Functions"></a>Defining functions
## <a name="Tests"></a>Tests
## <a name="Resources"></a>Resources
## <a name="Foreign"></a>Interfacing to foreign code
## <a name="Library"></a>The Wybe library
