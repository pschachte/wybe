# The Wybe Programming Language

Wybe is a programming language intended to combine the best features of
declarative and imperative programming.  It is in an early state of
development.

To build the Wybe compiler, follow the instructions in the
[INSTALL.md file](INSTALL.md).
See the [SUBDIRECTORIES.md file](SUBDIRECTORIES.md) file for
a tour of the directories making up the Wybe project.
There is a (growing) [list of programming and research projects](PROJECTS.md)
to further develop the Wybe language.


## The Wybe Language

The Wybe language is intended to be easy to learn and easy to use, but
powerful and efficient enough for for practical use.  It is intended to
support best programming practice, but not necessarily *common* practice.

Wybe combines the best features of declarative and imperative languages,
in particular borrowing features from functional, logic, imperative, and
object oriented languages, but does not neatly fit into any of these
paradigms.  Its main organising principle is that *values* are
immutable, but *variables* may be reassigned.  This means that values
may be passed around at will without worrying that they may be modified.

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
    % wybemk hello
```

where '%' is your operating system prompt. This will print error messages if
there are errors in your code; otherwise it completes without printing anything,
and produces an executable program, which you can run as usual for your
operating system.

```
    % ./hello
    Hello, World!
```

Note that `wybemk` is like `make` in that you give it the name of the
file you want it to build, and it figures out what files it needs
to compile.


### Primitive types

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

So a variable mention without adornment is passed by value, with a `?` prefix it
is passed by result, and with a `!` prefix, it is passed by value-result.

### Functions

Functions are defined with the syntax:

> `def` *name*`(`*param*`:`*type*, ... *param*`:`*type*`):`*type* `=` *expr*

Here *name* is the function name, each *param* is a parameter name, the
corresponding *type* is its type, the final *type* is the function
result type, and *expr* is an expression giving the function value.
Each `:`*type* is optional; if omitted, the compiler will infer the
type.  If there are no parameters, the parentheses are also omitted.

This syntax declares a private (not exported) function.  To export the
function, the definition should be preceded by the `pub` keyword.
All types must be included in public function definitions.

For example:

```
pub def toCelsius(f:float):float = (f - 32.0) / 1.8
```


### Procedures

Procedures are defined with the syntax:

> `def` *name*`(`*dir* *param*`:`*type*, ... *dir* *param*`:`*type*`) {` *body* `}`

Again *name* is the procedure name, each *param* is a parameter name, the
corresponding *type* is its type, and *body* is a sequence of statements
making up the body of the procedure.  Each *dir* is a dataflow
direction annotation, either nothing to indicate an input, `?` for an
output, or `!` to indicate both an input and an output.
Procedures may have any number of input, output, and input/output
arguments in any order.
Again each `:`*type* is optional, with types inferred if omitted,
and parentheses omitted for niladic procedures.

The procedure is private unless preceded by the `pub` keyword.
All types must be included in public procedure definitions.

For example:

```
pub def incr(!x:int) { ?x = x + 1 }
```


### Functions *are* procedures

Wybe functions are the same as procedures with one extra output
argument, and in fact the compiler implements them that way.  Therefore,
the definition
```
pub def toCelsius(f:float):float = (f - 32.0) / 1.8
```
is exactly equivalent to
```
pub def toCelsius(f:float, ?result:float) { ?result = (f - 32.0) / 1.8 }
```

Likewise, every function call is transformed into a procedure call, so:
```
pub def example(f:float, ?c:float) {?c = toCelsius(f) }
```
is exactly equivalent to
```
pub def example(f:float, ?c:float) {toCelsius(f, ?c) }
```

This means that what you define as a procedure, you can still call as a
function, and what you define as a function, you can still call as a
procedure.


### Modes

It is permitted to define multiple procedures with the same name, as
long as all of them have the same number and types of arguments in the
same order, and different *modes*.  A mode is a combination of argument
directions.  This can be used to carry out computations in different
directions.  For example:

```
pub def add(x:int, y:int, ?xy:int) { ?xy = x + y }
pub def add(x:int, ?y:int, xy:int) { ?y = xy - x }
pub def add(?x:int, y:int, xy:int) { ?x = xy - y }
```

The compiler expects that these definitions are consistent, as they are
in this case.  That means, for example, that for any values of `a` and
`b`, after
```
add(a, b, ?ab)
add(?z, b, ab)
```
`z` would equal `a`.
The compiler is entitled to count on this equality holding, and would
actually replace the second statement with
```
?z = a
```

### Type declarations
### Resources
### Tests
### Selection and iteration
### Modules
### Foreign interface
