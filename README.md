# The Wybe Programming Language

Wybe is a programming language intended to combine the best features of
declarative and imperative programming.  It is at an early stage of
development.

To build the Wybe compiler, follow the instructions in the
[INSTALL.md file](INSTALL.md).
See the [SUBDIRECTORIES.md file](SUBDIRECTORIES.md) file for
a tour of the directories making up the Wybe project.
There is a (growing) [list of programming and research projects](PROJECTS.md)
to further develop the Wybe language.
We are indebted to the several [contributors](CONTRIBUTORS.md)
to the Wybe project.


## The Wybe Language

The Wybe language is intended to be easy to learn and easy to use, but
powerful and efficient enough for practical use.  It is intended to
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
function whose output is the final procedure argument, and what you
define as a function, you can still call as a procedure by giving it an
extra argument to stand for the function output.  Thus

```
?y = f(x)
```
is always equivalent to
```
f(x, ?y)
```


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

Like any procedures, all of these can be called as functions, so with
these definitions, all of the following are valid:
```
?z = add(x, 1)
z = add(?x, 1)
z = add(1, ?x)
```
That is, functions can be run "backwards", if defined to support this.
In fact, `+` and `-` are already defined this way.

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

### Tests

Some procedure and function calls are *tests*.  This means that instead
of returning whatever outputs they ordinarily produce, they can *fail*,
in which case they do not produce their usual output(s).  You can think
of a test function as a partial function, and a test procedure as one
that can throw a special *failure* exception.

Test procedures and functions must be explicitly declared by inserting
the keyword `test` after the `def` keyword.

Calls to test procedures and functions are only permitted in two
contexts:  in a conditional, or in the definition of a test procedure or
function.

Any procedure or function call can become a test if an input is provided
where an output argument is expected.  In this case, the call is made
producing the output, and then the output is compared for equality with
supplied input.  Equality `=` with two input arguments is a test, so
these two calls are equivalent tests:

```
add(x, y, xy)
xy = add(x, y)
```

### Resources

Resources provide an alternative argument passing mechanism,
based on name rather than argument position.
They are intended for values that are unique in the computation,
where there is only one value of that sort in each part of the computation,
yet the value is used widely in the program.
For example, the command line parameters of an application may used in many
parts of the code, but explicitly passing that throughout the application 
may be a nuisance.
An application may build up logging message throughout, but explicitly threading
the log through the entire application can become painful.
Resources are often useful where an imperative application would use a global or
static variable, or where an object oriented application would use a class
variable.

#### Declaring a resource

The benefit of resources is that they are lightweight,
because they do not need to be explicitly passed between procedures
and their type only needs to be specified once,
Where it is declared.
Passing a value as a resource
also ensures that it is named and used consistently
throughout the module that declares it, and any modules that import it.

A resource can be declared at the level of a module, as follows:

> `resource` *name*`:`*type*

[//]: # This doesn't work; see issue #7:

[//]: # (It may optionally specify an initial value, in which case the resource is)
[//]: # (defined throughout the execution of the program.)

[//]: # (> `resource` *name*`:`*type* `=` *expr*)

A resource may be exported, allowing it to be referred to in other modules, by
preceding the `resource` declaration with the `pub` keyword.

#### Defining a resourceful procedure

Any procedure may declare that it uses any number of resources,
providing the named resources are visible in the enclosing module
(i.e., defined in that module or any imported module),
by adding a `use` clause to the procedure declaration
between the procedure header and body:

> `def` *name*`(`*params*`)` `use` *dir* *resource<sub>1</sub>*, ... *dir* *resource<sub>n</sub>* `{` *body* `}`

Each *dir* indicates the direction of information flow for the indicated
resource; as for parameters, no flow prefix indicates that the resource is only
an input, a question mark (`?`) indicates only an output, and an exclamation
point (`!`) indicates that the resource is both input and output.
The order in which the resources is listed is not significant, and any number of
resources may be specified.
This allows the resource name to be used as a local variable in the procedure
body, just as if it were an ordinary parameter.

Importantly, resources available in a procedure become available in any
procedures it calls that also declare that they `use` that resource.

#### Calling a resourceful procedure

A procedure may only be called in a context in which all the resources it uses
are defined, and a call to a resourceful procedure must be preceded by an
exclamation point (`!`) to signify that it receives inputs or produces outputs
that do not appear in its argument list.
This exclamation point serves as a warning that some values not explicitly
listed among the arguments in the call are used or defined or both, and the
declaration of the procedure must be consulted to see which values they are.

Most commonly, a procedure that uses a resource is called in the
definition of another procedure that uses that resource.
However, it may also be called from a procedure where the resource name is used
as a local variable, or inside a scoped resource use (see [below](#scoping)).

#### <a name="scoping"></a>Scoping a resource use

A resource may have its value scoped to a number of statements and the
procedures called by those statements, and so on recursively.
This creates a scope in which the resource is defined;
on leaving that scope, the resource ceases to exist.

A scope introducing one or more resources may be specified with a statement of
the form:

> `use` *resource<sub>1</sub>*`,` ... *resource<sub>n</sub>* `in` `{` *body* `}`

In this case, at the start of the *body*, the resource will be undefined,
as it will at the completion of *body*.
If the resource is already defined outside the scope of the `use` statement,
the value at the start of *body* will be the same as the value before the `use`
statement, and the value at the completion of the *body* will again be the same
as the value before entering the `use` statement.
Thus a `use` statement will not alter the existence or the values of the
resources it names.

#### Predefined resources

Wybe uses predefined resources for a few key language features.
In particular, the `io` resource holds a representation of the state of the
world outside the computation being performed, including the file system.
Thus all procedures that perform input/output are declared to `use !io`,
the `!` being necessary because any procedure that does I/O changes the state of
the world outside the computation, either by outputting something, or by
changing the part of an input stream being read.
Therefore, any call to a procedure that performs I/O (or that calls a procedure
that performs I/O) must be preceded with an `!` to indicate that it modifies a
resource.

The `io` resource is implicitly defined at the top level of a Wybe program.
There is also a predefined `argc` and `argv` resource holding the number of
command line arguments and an array of the arguments themselves.
Finally, the `exit_code` resource is initialised to 0 at the start of execution,
and may be changed to any integer during the computation to set the exit
condition that will be returned to the operating system at the termination of
the program.

### Statements
#### Procedure calls
#### Selection
#### Iteration
### Expressions
#### Function calls
#### Selection
#### Iteration
### Modules
### Type declarations
### Selection and iteration
### Foreign interface
