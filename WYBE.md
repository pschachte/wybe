# The Wybe Programming Language

The Wybe programming language is intended to be easy to learn and easy to use,
but powerful and efficient enough for practical use.  It is intended to
support best programming practice, but not necessarily *common* practice.

Wybe combines the best features of declarative and imperative languages,
in particular borrowing features from functional, logic, imperative, and
object oriented languages, but does not neatly fit into any of these
paradigms.  Its main organising principle is that *values* are
immutable, but *variables* may be reassigned.  This means that values
may be passed around at will without worrying that they may be modified.


## Hello, World!

Code appearing at the top level of a file is executed when the program
is run, so Hello, World! in Wybe is quite simple:
```
# Print a friendly greeting
!println("Hello, World!")
```

Wybe comments begin with a hash (`#`) character and continue to the end
of the line.

The leading exclamation point is needed on statements that perform input/output,
and in a few other contexts that will be explained in Section
[Resources](#resources).


## Building

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


## Module items

Every Wybe source file is a module.
It may contain the following sorts of items:
statements,
function definitions,
procedure definitions,
type declarations,
resource declarations, and
module declarations.
Each of these will be described in due course.

These items are all private by default, meaning that even if the enclosing
module is imported, they will not be visible.
However, each of these sorts of items can be made public by preceding them with
the keyword `pub`, meaning that by importing the module that defines them,
you gain access to them.

To import a module into your own module, you need only include a declaration of
the form:

> `use` *module*`,` ... *module*

naming one or more modules to import.
If you precede the `use` keyword with `pub`, you automatically make any public
items in the named *module*s also visible to any module that imports the module
containing this declaration.
In effect, this re-exports everything imported from the named module(s).


## Primitive types

Wybe has the usual complement of primitive types:

| Type       | Meaning                                    |
| ---------- | ------------------------------------------ |
| `int`      | Fixed precision integer (32 or 64 bits)    |
| `float`    | Double precision floating point number     |
| `bool`     | Boolean; either `true` or `false`          |
| `string`   | Character string (double quotes)           |
| `char`     | Individual ascii character (single quotes) |


## Constants

Wybe also supports a conventional syntax for various constant types.

Integer constants begin with a digit character.
If the first two characters are `0x` or `0X`, then the integer is written in
hexadecimal notation (so in addition to digit characters, it may contain upper
or lower case letters `a`-`f`);
otherwise if the first character is `0`, then the integer is written in octal
notation (so it may only contain digits `0`-`7`);
otherwise it is written in decimal notation, made of any number of decimal
digits.
In any radix, underscore characters (`_`) are ignored; these may be used to
make numbers more readable, such as by grouping digits into thousands, millions,
and billions, or by grouping pairs of hexadecimal characters into bytes.

Floating point constants consist of 1 or more decimal digits followed
by a decimal point (`.`) character, followed by one or more decimal digits.
This may be followed by an `e` or `E` and one or more decimal digits specifying
a power of ten to multiply the earlier number by.
If the `e` or `E` is present, the decimal point (`.`) and fractional part may be
omitted.

The only Boolean constants are `true` and `false`.

String constants are written as any number of characters between double quote
(`"`) characters.

Character constants are written as a single character between single quote (`'`)
characters.
If the first character following the opening quote is a backslash (`\`), then
the following character is considered part of the character constant, and is
interpreted as follows:

| Character  | Meaning                                    |
| ---------- | ------------------------------------------ |
| `a`        | Alert or bell (ASCII code 0x07)            |
| `b`        | Backspace (ASCII code 0x08)                |
| `f`        | Formfeed (ASCII code 0x0c)                 |
| `n`        | Newline or Line feed (ASCII code 0x0a)     |
| `r`        | Carriage return (ASCII code 0x0d)          |
| `t`        | Horizontal tab (ASCII code 0x09)           |
| `v`        | Vertical tab (ASCII code 0x0b)             |

Any other character following a backslash is interpreted as itself.
In particular, `'\\'` specifies a backslash character and `'\''`
specifies a single quote character.


## Procedure calls

`!println("Hello, World!")` is a call the procedure `println` with the string
`Hello, World` as its only argument.
In general, procedure calls have the form:

> *name*`(`*arg*, ... *arg*`)`,

where *name* is the name of the procedure to call,
and each *arg* is an expression specifying an input or output
to that procedure.

A procedure call must be preceded by an exclamation point (`!`) if it uses any
resources, as described in the section on
[calling a resourceful procedure](calling resourceful).

A procedure whose name consists of any number of the operator characters
```
~ @ $ % ^ & * - + = \ < > /
```
may use the alternative infix syntax:

> *arg* *op* *arg*,

where *op* is the procedure name (there must be exactly two arguments).


## <a name="variables"></a>Variables
The simplest form of expression is a variable reference.
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

The compiler can usually infer the type of a variable based on how it is used,
but sometimes the uses of a variable are not sufficient to determine a single
type.  In such cases, the programmer must explicitly specify the type.  In other
cases an explicit type may serve as useful documentation.  A variable's type may
be specified by following the variable name by a colon (`:`) and the variable's
intended type where the variable is first assigned.  For example, the following
code reads a single character, storing it in the variable `ch`:
```
!read(?ch:char)
```


## Function calls

A second kind of expression is a function call.
In general, these have the syntax:

> *name*`(`*arg*, ... *arg*`)`,

(that is, the same as procedure calls).
Again, each *arg* is an expression.

A function whose name consists of any number of the operator characters
```
~ @ $ % ^ & * - + = \ < > /
```
may use the alternative infix syntax:

> *arg* *op* *arg*,

where *op* is the function name (there must be exactly two arguments).


## Function definitions

Functions are defined with the syntax:

> `def` *name*`(`*param*`:`*type*, ... *param*`:`*type*`):`*type* `=` *expr*

Here *name* is the function name, each *param* is a parameter name, the
corresponding *type* is its type, the final *type* is the function
result type, and *expr* is an expression giving the function value.
Each `:`*type* is optional; if omitted, the compiler will infer the
type.  If there are no parameters, the parentheses are also omitted.
If the function name comprises operator characters, it should be surrounded with
backquote characters (`` ` ``).

This syntax declares a private (not exported) function.  To export the
function, the definition should be preceded by the `pub` keyword.
All types must be included in public function definitions.

For example:

```
pub def toCelsius(f:float):float = (f - 32.0) / 1.8
```


## Procedure definitions

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
If the procedure name comprises operator characters, it should be surrounded
with backquote characters (`` ` ``).

The procedure is private unless preceded by the `pub` keyword.
All types must be included in public procedure definitions.

For example:

```
pub def incr(!x:int) { ?x = x + 1 }
```


## Functions *are* procedures

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


## Modes

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

## Tests and partial functions

Some procedure and function calls are *tests*.  This means that instead
of returning whatever outputs they ordinarily produce, they can *fail*,
in which case they do not produce their usual output(s).  Functions
that may fail to produce a result are also known as *partial* functions.

Test procedures and functions must be explicitly declared by inserting
the modifier `test`, enclosed within curley braces, after the `def` keyword.
You can also use the modifier `partial` in place of `test`.  For example:

```
def {test} even_number(num:int) { ... }
def {partial} lookup(key:int, table:map) = ...
```

Calls to test (partial) procedures and functions are only permitted in two
contexts:  in a conditional, described [below](#conditionals),
or in the definition of a test/partial procedure or function.

Any procedure or function call can also become a test if an input is provided
where an output argument is expected.  In this case, the call is made
producing the output, and then the output is compared for equality with
supplied input.  Equality (`=`) with two input arguments is a test, so
these two calls are equivalent tests (in fact, the former is transformed to the
latter):

```
add(x, y, xy)
xy = add(x, y)
```


## <a name="conditionals"></a>Conditional statements

Wybe's conditional construct has the form:

> `if` `{` *cases* `}`

where *cases* is one more more cases, separated by vertical bar characters (`|`).
Each case takes the form:

> *test* `::` *statements*

where *test* is a test statement and *statements* is one or more statements.
Execution proceeds by executing the first *test*, and if it succeeds, executing
the corresponding *statements*, thereby completing the `if` statement.
If the first *test* fails, its corresponding *statements* are skipped and
the second *test* is tried.
If this test succeeds, its corresponding *statements* are executed, and so on.
At most one *statements* sequence is executed, but if none of the specified
*test*s succeed, none of the *statements* are executed.
The predefined `otherwise` test always succeeds, so it may be used as the final
test to provide code to execute if none of the preceding tests succeeds.

For example:
```
if { x < 0     :: !println("negative")
   | x = 0     :: !println("zero")
   | otherwise :: !println("positive")
}
```



## `terminal` and `failing` procedures
A procedure is considered to be *terminal* if a call to it will never return (it
will neither succeed nor fail). For example, the `exit` and `error` procedures
are `terminal`, as is any infinite loop. A procedure can be declared to be
terminal by following the `def` keyword with `{terminal}` in its declaration. The
Wybe compiler will verify that procedures declared `terminal` will indeed not
return.

A procedure is considered to be *failing* if is guaranteed never to succeed.  It
may fail or never return.  Wybe has a single built-in failing proc, named
`fail`, with no parameters.


## Iteration statements

Iteration is specified with the `do` statement, of the form:
> `do` `{` *statements* `}`
This executes the enclosed *statements* repeatedly, until a termination
condition is reached.

The enclosed *statements* may include any ordinary Wybe statements, plus any of
the following:

> `while` *test*

If *test* fails, exit the loop immediately, otherwise continue

> `until` *test*

If *test* succeeds, exit the loop immediately, otherwise continue

> `when` *test*

If *test* fails, restart the loop immediately, otherwise continue

> `unless` *test*

If *test* succeeds, restart the loop immediately, otherwise continue

These special loop control statements may be used anywhere inside a `do`
statement.
For example:

```
do {!print(prompt)
    !read(?response)
    until valid_answer(response)
    !println("Invalid response; please try again.")
}
```

## (sub)modules

A Wybe module may contain submodules.
Each submodule of a module has access to everything in the containing module,
whether or not it is public.
However, the parent module can only access items declared `pub`lic in its
submodules.
The parent module need not explicitly import its submodules; this is done
automatically.

A submodule is declared as follows:

> `module` *name* `{` *items* `}`

where *name* is the module name and *items* are the contents of the submodule.


## Type declarations

Wybe provides an algebraic type system.
Types may be declared with the syntax:

> `type` *type* `{` *ctors* *defs* `}`

where *ctors* is one or more constructor declaration, separated by vertical bar
characters (`|`).
To make the declared *type* public, precede the `type` keyword with the keyword
`pub`.
If you wish for the constructors of the type public,
precede the first constructor declaration with the `pub` keyword
(this makes all the constructors public).

The *defs* part may be empty, but if specified, may include any number of
procedure and function declarations, which will have full access to the
constructors of the type, whether or not they are public.

Each constructor declaration takes the form of a function declaration (with no
function body):

> *ctor*`(`*member*`:`*memtype*, ... *member*`:`*memtype*`)`

Each *ctor* is a distinct constructor name specifying an alternative constructor
for the *type* being defined.
Any number of *member*`:`*memtype* pairs may be specified, specifying
information that must be supplied for that constructor.
If no members are specified, the parentheses are omitted.

Each constructor defined automatically becomes a function that may be used to
construct a value of the *type* being defined.
It also becomes a function that can be used backwards, extracting the
constructor
arguments as *outputs*, allowing a value to be deconstructed into its parts.
For example, given the definition
```
type coordinate { coordinate(x:int, y:int) }
```
the following statement may be used to construct a Cartesian coordinate with X
component 7 and Y component 4:
```
?pos = coordinate(7,4)
```
And this statement will unpack a coordinate `pos` into variables `x` and `y`:
```
coordinate(?x,?y) = pos
```

Additionally, two procedures are automatically generate for each *member*:
one to access the member, and one to mutate it.
The first has the prototype:

> *member*`(structure:`*type*`,` `?value:`*memtype*`)`

and the second has the form:

> *member*`(!structure:`*type*`,` `value:`*memtype*`)`

These are more conveniently used as functions, for example:
```
!print("X coordinate: ")
!println(x(pos))
x(!pos) = x(pos) + 1  # shift position to the right
```

It is important to note that "mutating" a value does not actually modify it in
place; it creates a fresh value of that type that is identical except for the
member being changed.
Wybe does not have the concept of
[object identity](https://en.wikipedia.org/wiki/Identity_(object-oriented_programming)),
nor the concepts of pointers or references.
You can safely have multiple variables refer to the same data without worrying
that modifying the data through one of them will change the values of the
others.
For example
```
?pos = coordinate(7,4)
!println(x(pos))
?oldpos = pos
x(!pos) = x(pos) + 1  # shift position to the right
!println(x(pos))
!println(x(oldpos))
```
will print
```
7
8
7
```

The Wybe compiler, however, will optimise mutations when it determines that it
can safely do so.
For example, the compiler will optimise this code
```
?pos = coordinate(7,4)
!println(x(pos))
x(!pos) = x(pos) + 1  # shift position to the right
!println(x(pos))
```
so that it does in fact mutate the coordinate object in place,
saving an unnecessary object creation.

Deconstructing a value of a type with multiple constructors,
or accessing or altering any of its members, is a test, since the
value may not have the intended constructor.
This ensures that it is not possible to mistake a value created with one
constructor for one made with a different constructor.
For example, if a tree type is defined as:
```
type tree { empty | node(left:tree, value:int, right:tree) }
```
then it may be used as follows:
```
def {test} member(elt:int, tree:tree) {
    if { node(?left, ?value, ?right) = tree ::
            if { elt = value:: succeed
               | elt < value:: member(elt, left)
               | otherwise  :: member(elt, right)
            }
       | otherwise:: fail
    }
}
```

Note that a type is just a special kind of module that is also taken as a valid
type name.
The constructors, deconstructors, accessors, and mutators of the type are merely
members of the type that are automatically generated by the Wybe compiler.
Any procedures or functions you define inside the type will be indistinguishable
from its constructors, deconstructors, accessors, and mutators.


## Resources

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

### Declaring a resource

The benefit of resources is that they are lightweight,
because they do not need to be explicitly passed between procedures
and their type only needs to be specified once,
Where it is declared.
Passing a value as a resource
also ensures that it is named and used consistently
throughout the module that declares it, and any modules that import it.

A resource can be declared at the level of a module, as follows:

> `resource` *name*`:`*type*

[//]: # (This does not work; see issue #7.)

[//]: # (It may optionally specify an initial value, in which case the resource is)
[//]: # (defined throughout the execution of the program.)

[//]: # (> `resource` *name*`:`*type* `=` *expr*)

A resource may be exported, allowing it to be referred to in other modules, by
preceding the `resource` declaration with the `pub` keyword.

### Defining a resourceful procedure

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

### <a name="calling resourceful"></a>Calling a resourceful procedure

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

### <a name="scoping"></a>Scoping a resource use

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

### Predefined resources

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

## Low-level features (foreign interface)

### Purity

Wybe code is mostly purely logical, and the Wybe compiler takes advantage of
this.  For example, if none of the outputs of a proc call are actually used, the compiler will eliminate the call.  A proc call may also be omitted if a proc call has previously been made with the same inputs, with the compiler assuming the output(s) will be identical.  The compiler may also reorder calls however it likes, as long as all the inputs to a proc are available when the proc is called.  As long as your code is purely logical, all of these optimisations and more are perfectly safe.

However, occasionally it is important that the compiler not perform such optimisations.  For example, the `exit` command has no outputs, it is only executed for its effect (terminating the program prematurely).  In some cases, purely logical Wybe procs can be written based on impure building blocks, particularly when interfacing to code written in conventional languages.

To support such cases, the Wybe compiler provides a *purity* system, allowing you to declare the purity of your procedures and functions, which tells the Wybe compiler (and other programmers) to treat them more carefully.

Wybe supports the following three levels of purity:

- *pure*  
the default purity level.  An ordinary call, subject to omission or reordering.

- *impure*  
an impure call that should not be reordered or omitted.  Impure procs must be declared to be so, and in general, a proc that calls an impure proc must itself be impure.

- *semipure*  
a proc that behaves as impure itself, and will not be reordered or omitted, however its impurity is not "contagious".  It may be called from an ordinary, pure proc without that proc becoming impure.

In the absence of any declaration of impurity, your procedures and functions will be assumed to be pure.  An ordinary pure proc can call a semipure proc, but if it calls an impure proc, the compiler will report an error.  You can specify that your proc is pure despite calling impure procs by explicitly promising that it is pure.

Purity is managed by including one of the following modifiers, between curly braces, in the proc declaration, between the `def` keyword and the procedure or function name:

- `pure`  
promise that the proc is pure, despite calling impure procs.

- `semipure`  
specify that the proc is effectively impure, meaning that calls to it are not subject to normal optimisations, but that its callers are not rendered impure by calling it.

- `impure`  
the proc is impure, so calls to it are not subject to normal optimisations, and its callers should also be considered impure unless explicitly promised to be pure with a `pure` modifier.

Any call to an `impure` or `semipure` proc must be preceded with the `!` annotation, as if it were a call to a proc that used resources.  This reminds the reader that the call is not pure, and that they must be careful when reading or modifying the code.  For example, to prematurely exit the program, you can insert the following proc call:

```
!exit(1)
```

If you wish to include other modifiers along with one of these, include them all between the braces, in any order, separated by commas.


### Inlining

The Wybe compiler optimises your code in some situations by replacing a proc call with its definition, while being careful not to change the meaning of the program.  The compiler uses heuristics to determine when to do this, and for the most part it is not something you need to think about.

If you wish to have finer control, you can do this by placing one of these two modifiers between curly braces between `def` and the procedure or function name:

- `inline`  
force inlining of calls to this proc

- `noinline`  
prevent inlining of calls to this proc

If you wish to include other modifiers along with one of these, include them all between the braces, in any order, separated by commas.

### Foreign interface


#### Foreign types

To be documented....


#### Calling C code

To call C code from Wybe, use the `foreign` construct.
This is a very low-level interface, and performs no sanity checking, so be careful to get the call right.

The form of a C function call is:

> `foreign c` *function*(*arg*, *arg*, ...)

Note that, like other Wybe calls, foreign calls are assumed to be pure.  If your foreign call is performing some kind of interaction with the outside world, it should use the `io` resource, to ensure that the call is performed correctly.  This is actually quite simple:  the `io` state is simply eliminated by the compiler when it is passed in a foreign call, so you can simply pass it into and out of a foreign call, and it will vanish as the call happens, and reappear on return from the call.  For example, the `print` proc for the `char` type in the standard library is defined this way:

```
pub def print(x:char) use !io { foreign c putchar(x, !io) }
```

To improve the safety of the interface, it is recommended to define a separate Wybe proc to make each foreign call, as shown above.  This will allow the Wybe type checker to ensure the type safety of your calls, as long as your foreign call is type correct.

If your foreign call is not for communication with the outside world, then you may wish to include a purity modifier to prevent the compiler from eliminating it.  For example, the `exit` proc in the standard library is implemented as follows:

```
pub def {terminal,semipure} exit(code:int) {
    foreign c {terminal,semipure} exit(code)
}
```

(`terminal` here means that `exit` will never return to the caller; this improves Wybe's analysis of code that calls `exit`.)

#### Using LLVM instructions

The lowest-level interface is to raw LLVM instructions.  These have a functional style, although you use the procedural style if you prefer.  For example, instead of

```
?x2 = foreign llvm add(x, 1)
```
you can write
```
foreign llvm add(x, 1, ?x2)
```

For more detail on the behaviour of these operations, please consult the [LLVM documentation](https://llvm.org/docs/).


##### Integer operations

In the following, all inputs and outputs listed as `int` can in fact be any integer type:  signed or unsigned, and any number of bits of precision.  However, all `int` inputs and outputs must be the same number of bits of precision.  All `bool` outputs may be any 1-bit integer type.


- foreign llvm add(arg1:int, arg2:int):int  
Integer addition
- foreign llvm sub(arg1:int, arg2:int):int  
Integer subtraction
- foreign llvm mul(arg1:int, arg2:int):int   
Integer multiplication
- foreign llvm udiv(arg1:int, arg2:int):int  
unsigned integer division
- foreign llvm sdiv(arg1:int, arg2:int):int  
Signed integer division
- foreign llvm urem(arg1:int, arg2:int):int  
unsigned integer remainder
- foreign llvm srem(arg1:int, arg2:int):int  
Signed integer remainder
- foreign llvm icmp_eq(arg1:int, arg2:int):bool  
Integer equality
- foreign llvm icmp_ne(arg1:int, arg2:int):bool  
Integer disequality
- foreign llvm icmp_ugt(arg1:int, arg2:int):bool  
Integer unsigned strictly greater
- foreign llvm icmp_uge(arg1:int, arg2:int):bool  
Integer unsigned greater or equal
- foreign llvm icmp_ult(arg1:int, arg2:int):bool  
Integer unsigned strictly less
- foreign llvm icmp_ule(arg1:int, arg2:int):bool  
Integer unsigned less or equal
- foreign llvm icmp_sgt(arg1:int, arg2:int):bool  
Integer unsigned strictly greater
- foreign llvm icmp_sge(arg1:int, arg2:int):bool  
Integer signed greater or equal
- foreign llvm icmp_slt(arg1:int, arg2:int):bool  
Integer signed strictly less
- foreign llvm icmp_sle(arg1:int, arg2:int):bool  
Integer signed less or equal
- foreign llvm shl(arg1:int, arg2:int):int  
Left shift
- foreign llvm lshr(arg1:int, arg2:int):int  
Logical right shift (shift zeros in at right)
- foreign llvm ashr(arg1:int, arg2:int):int  
Arithmetic right shift (copy sign bit at right)
- foreign llvm or(arg1:int, arg2:int):int  
Bitwise or
- foreign llvm and(arg1:int, arg2:int):int  
Bitwise and
- foreign llvm xor(arg1:int, arg2:int):int  
Bitwise exclusive or

##### Floating point operations

Similar to above, all inputs and outputs listed as `float` can be any legal LLVM floating point type:  16, 32, 64, or 128 bits.  Again, in a single instruction, all the `float` inputs and outputs must be the same bit width.

- foreign llvm fadd(arg1:float, arg2:float):float  
Floating point addition
- foreign llvm fsub(arg1:float, arg2:float):float  
Floating point subtraction
- foreign llvm fmul(arg1:float, arg2:float):float  
Floating point multiplication
- foreign llvm fdiv(arg1:float, arg2:float):float  
Floating point division
- foreign llvm frem(arg1:float, arg2:float):float  
Floating point remainder
- foreign llvm fcmp_eq(arg1:float, arg2:float):bool  
Floating point equality
- foreign llvm fcmp_ne(arg1:float, arg2:float):bool  
Floating point disequality
- foreign llvm fcmp_slt(arg1:float, arg2:float):bool  
Floating point (signed) strictly less
- foreign llvm fcmp_sle(arg1:float, arg2:float):bool  
Floating point (signed) less or equal
- foreign llvm fcmp_sgt(arg1:float, arg2:float):bool  
Floating point (signed) strictly greater
- foreign llvm fcmp_sge(arg1:float, arg2:float):bool  
Floating point (signed) greater or equal

##### Integer/floating point conversion

- foreign llvm uitofp(arg1:int):float  
Convert unsigned integer to float
- foreign llvm sitofp(arg1:int):float  
Convert signed integer to float
- foreign llvm fptoui(arg1:float):int  
Convert float to unsigned integer
- foreign llvm fptosi(arg1:float):int  
Convert float to signed integer


#### Wybe low-level memory management primitives

# LPVM Instructions #

The LPVM instructions are low-level memory manipulation instructions.  Note
these are foreign instructions specifying the `lpvm` (rather than `llvm`)
language.

- foreign lpvm alloc(size:int, ?struct:type)  
Allocate (at least) *size* bytes of memory and store the address in
*struct*, which has its specified wybe type.

- foreign lpvm access(struct:type, offset:int, size:int,
                        start_offset:int, ?member:type2)  
Access the field of type type2 at address struct + offset. The size of the
structure is size bytes. The intention of the start_offset is to handle tagged
pointers: a tagged pointer will appear to point start_offset bytes past the
start of the actual structure in memory; subtracting this will allow the start
of the structure to be found, so it can be copied.

* foreign lpvm mutate(struct:type, ?struct2:type,
                        offset:int, destructive:bool,
                        size:int, start_offset:int, member:type2)  

struct2 is the same as struct, except that it has member, with type type2, at
struct + offset. The start of the structure is actually start_offset bytes
before struct in memory, and the size of the structure is size bytes. The
intention of the start_offset is to handle tagged pointers: a tagged pointer
will appear to point start_offset bytes past the start of the actual structure
in memory; subtracting this will allow the start of the structure to be found,
so it can be copied. If destructive is `true`, then this instruction is
permitted to perform the operation destructively, making struct2 the same
address as struct.

* foreign lpvm cast(var1:type1, ?var2:type2)  
Move var1 to var2 converting its type from type1 to type2, without changing the
representation. This just allows getting around LLVM strong typing; it does not
actually require any instructions.
