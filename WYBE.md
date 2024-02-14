![Wybe logo](assets/logo/blue.svg)

# The Wybe Programming Language


The [Wybe](README.md) programming language is intended to be easy to learn and easy to use,
but powerful and efficient enough for practical use.  It is intended to
support best programming practice, but not necessarily *common* practice.

Wybe combines the best features of declarative and imperative languages,
in particular borrowing features from functional, logic, imperative, and
object-oriented languages, but does not neatly fit into any of these
paradigms.  Its main organising principle is **interface integrity**, which
indicates that all information that flows between a procedure or function and
its caller must be part of the interface (the signature) of that procedure or
function.
That is, Wybe does not have global or static variables, and all *values* are immutable (Wybe has
[*value semantics*](https://en.wikipedia.org/wiki/Value_semantics)), ensuring that data structures
may be passed around at will without worrying that they may be unexpectedly
modified.  In this way, Wybe is akin to a
[functional](https://en.wikipedia.org/wiki/Functional_programming) or
[logic](https://en.wikipedia.org/wiki/Logic_programming) programming language.

However, Wybe allows variables to be reassigned,
supports conventional looping constructs,
and allows procedures to be defined as sequential
computations.
In place of global variables, Wybe supports [*resources*](#resources), which
provide a syntactically lightweight way to pass information bidirectionally
between a procedure and its callers.
In these ways, Wybe is like an
[imperative](https://en.wikipedia.org/wiki/Imperative_programming) programming
language.

A Wybe type is a module containing functions and procedures that operate on
values of that type, and is thus an
[abstract data type](https://en.wikipedia.org/wiki/Abstract_data_type).
A Wybe type may specify any number of constructors,
and Wybe ensures that code can only access the members of a datum that were provided in the constructor used
to create that datum, and is therefore also an
[algebraic data type](https://en.wikipedia.org/wiki/Algebraic_data_type).

The Wybe compiler provides a few features to ensure high performance.
First, it is a native code compiler, bypassing the interpretation or virtual machine overhead of
some languages.
In some cases the compiler can arrange for values to be destructively
updated in place, as long as it can be sure that the original value of the
data structure will never be accessed again.
This still maintains interface integrity, while mitigating some of the
performance penalty of declarative languages.
The compiler employs *multiple specialisation*, automatically generating more efficient specialised versions
of procedures and functions for use in contexts where conditions allow.
The compiler also takes advantage of the language's interface integrity, such as
by avoiding repeating a previous computation or carrying out a computation whose
result is not needed.

## <a name="hello-world"></a>Hello, World!

Code appearing at the top level of a module (that is, not inside a procedure
or function definition) is executed when the program
is run, so "Hello, World!" in Wybe is quite simple:
```
# Print a friendly greeting
!println("Hello, World!")
```

Wybe comments begin with a hash (`#`) character and continue to the end of the
line.  Block comments are written beginning with `#|` and continuing until the
following `|#` sequence.

The leading exclamation point is needed on statements that perform input/output,
and in a few other contexts that will be explained in the
[Resources](#resource-declarations) section.


## Compiling Wybe code

Use `wybemk` to build object and executable files.  If the above program
is put in a file named `hello.wybe`, then an executable program can be
built with the command:

```
% wybemk hello
```

where `%` is your operating system prompt. This will print error messages if
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

### Compiler Options

`wybemk` supports various compiler options. A full listing of available flags
can be found with the following:

```
% wybemk --help
```

#### Optimisation Options

The `--llvm-opt-level` (`-O`) options specifies the level of optimisation used
within the LLVM compiler during the compilations stage of a Wybe module. By default, this is set to 3, yet supports the values 0, 1, 2, or 3. More information
can be found [here](https://llvm.org/docs/CommandGuide/llc.html#id1).


# Wybe Source files

Every Wybe source file is a module.
It may contain the following sorts of items:

  * [module imports](#importing),
  * [(top level) statements](#hello-world),
  * [function definitions](#function-definitions),
  * [procedure definitions](#procedure-definitions),
  * [constructor declarations](#constructor-declarations),
  * [type declarations](#type-declarations),
  * [resource declarations](#resource-declarations), and
  * [module declarations](#submodules).

Each of these will be described in due course.

Each module item should begin on a new line, or they should be separated by
semicolon (`;`) characters.  See the section on [code layout](#code-layout) for
more details on how newlines are treated.

These items are all private by default, meaning that even if the enclosing
module is imported, they will not be visible in any importing modules.
However, each of these sorts of items can be made public by preceding them with
the keyword `pub`, meaning that by importing the module that defines them,
you gain access to them.

### <a name="importing"></a>Importing modules
To import a module into your own module, you need only include a declaration of
the form:

> `use` *module*`,` ... *module*

naming one or more modules to import.
If you precede the `use` keyword with `pub`, you automatically make any public
items in the named *module*s also visible to any module that imports the module
containing this declaration.
In effect, this re-exports everything imported from the named module(s).


##  <a name="primitives"></a>Primitive types

Wybe has the usual complement of primitive types:

| Type       | Meaning                                          |
| ---------- | ------------------------------------------------ |
| `int`      | Fixed precision integer (32 or 64 bits)          |
| `float`    | Double precision floating point number           |
| `count`    | Fixed precision unsigned integer (32 or 64 bits) |
| `bool`     | Boolean; either `true` or `false`                |
| `string`   | Character string (double quotes)                 |
| `c_string` | C-style character string (double quotes)         |
| `char`     | Individual ASCII character (single quotes)       |

These are all defined in the `wybe` module, which is automatically imported into
every module, so there is no need to explicitly import them.


### <a name="higher-order-types"></a>Higher order types

A higher order type has one of the two following forms

> `(` *flow* *type*`,` ... `)`

> `{` *modifier*`,` ... `}` `(` *flow* *type*`,` ... `)`

Two higher order types are considered compatible if they share the same flows
and the type parameters are also compatible.

The list of modifiers specifies the modifiers of the higher order type. These modifiers
can be a purity modifier, a determinism modifier, or `resource`. The special
`resource` modifier states that this higher order term may use some resource.


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
(`"`) characters.  Character constants are written as a single character between
single quote (`'`) characters.

To denote a C-style (null-terminated) string, a `c` precedes the first `"`.
This is provided for interoperability with external libraries.

In both strings and character constants, the backslash (`\`) character is special,
altering the way the following character is interpreted.  The backslash and the
following character together are interpreted as a single character, according to
the following character:

| Character | Meaning                                 |
| --------- | --------------------------------------- |
| `0`       | The null character (ASCII code 0x00)    |
| `a`       | Alert or bell (ASCII code 0x07)         |
| `b`       | Backspace (ASCII code 0x08)             |
| `e`       | Escape (ASCII code 0x1b)                |
| `f`       | Form feed (ASCII code 0x0c)             |
| `n`       | Newline or Line feed (ASCII code 0x0a)  |
| `r`       | Carriage return (ASCII code 0x0d)       |
| `t`       | Horizontal tab (ASCII code 0x09)        |
| `v`       | Vertical tab (ASCII code 0x0b)          |
| `x`       | Introduce a hexadecimal character code  |

The two characters following `\x` (or `\X`) must be hexadecimal characters,
in which case the hexadecimal number
specifies the character code.  For example `'\x20'` specifies character code 32,
which is the space character.
Additionally, within strings, the dollar sign (`$`) character is special;
see the discussion of [string interpolation](#string-interpolation) below.

Any other character following a backslash is interpreted as itself. In
particular, `\'` specifies a single quote character, `\"`
specifies one double-quote character, `\$` specifies a dollar sign character,
and `\\` specifies a single backslash character.


## <a name="string-interpolation">String interpolation

Values of variables and expressions can be included within a string through
*string interpolation*.  To include the value of a variable within a string,
place the variable name within the string preceded by a dollar sign (`$`)
character.  For example, if the variable `name` holds the string `"Wybe"`,
then

> `"Hello, $name!"`

denotes the string `"Hello, Wybe!"`, and if the variable `number` holds the value 42, then

> `"$number is the answer"`

denotes `"42 is the answer"`

More generally, the values of Wybe expressions can be included in strings by
placing them within parentheses immediately preceded by a dollar sign.  For
example, if `base` is 2 and `bits` is 63, then

> `"maxint is $(base**bits-1) and minint is $(base**bits)"`

denotes the string
`"maxint is 9223372036854775807 and minint is -9223372036854775808"`

Interpolated expressions can be arbitrarily complex, involving nested
subexpressions, nested parentheses, and even nested quotes.

Variables and expressions used in string interpolations are converted to
strings using the `fmt` function, which is defined for all primitive types,
and can be defined for user types to allow them to be interpolated.  Note
that `fmt` applied to strings returns the strings as is, without surrounding
them with quotation marks.  Then
string concatenation (`,,`) is used to assemble the string from its fixed
parts and the results of the call(s) to `fmt`.

## Procedure calls

`!println("Hello, World!")` is a call to the procedure `println` with the string
`Hello, World` as its only argument.
In general, procedure calls have the form:

> *name*`(`*arg*, ... *arg*`)`,

where *name* is the name of the procedure to call,
and each *arg* is an expression specifying an input or output
to that procedure. If there is a variable bound with the name *name* that has
a [higher order type](#higher-order-types) then this is a call to the higher order term.

Sometimes you may wish to specify which module the procedure *name* exists in.
You can further specify which module the procedure *name* is from by preceding
*name* with a `.` separated module specification, such as *parent*`.`*mod*`.`*name*.

As a convenience, if the first module name in a module specification is `_`, the
`_` is equivalent to the current module. For example in a module named `foo`,
`_.`*name* is equivalent to `foo.`*name*

A procedure call must be preceded by an exclamation point (`!`) if it uses any
resources, as described in the section on
[calling a resourceful procedure](#calling-resourceful).


## <a name="variables"></a>Variables
The simplest form of expression is a variable reference.
Variable names begin with a letter (upper or lower case) and follow with
any number of letters, digits, and underscores.

A variable mention may *use* or *assign* its value.  If the variable
name is preceded by a question mark (`?`), the mention assigns the
variable a (new) value; without the question mark prefix, the mention
uses the variable's current value.  It does not matter on which side of an
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


## <a name="function-calls"></a>Function calls

A second kind of expression is a function call.
In general, these have the syntax:

> *name*`(`*arg*, ... *arg*`)`,

(that is, the same as procedure calls).
Again, each *arg* is an expression.

A function name may consist of any number of upper and lower case letters,
digits, and underscore (`_`) characters, as long as it does not begin with a
digit.  Also see the [operator syntax](#operator-syntax) section for special
infix and prefix operator syntax.

Function calls may have one of the following forms:
  - A call with all arguments inputs.  This is the conventional form, where all
    arguments are evaluated, and then the function is called, producing the
    function value.  This form of expression is considered to be an input to
    whatever statement or expression it occurs in.

  - A call where one or more arguments are outputs (prefixed with `?`), and all
    others, if any, are inputs.  This form of expression is considered to be an
    output.  In this case, the function is run "backwards", working from the
    result to determine the output arguments.  So the value of the function must
    be supplied by the context in which it is called, and then the function is
    called to produce the values for the outputs.  One common use of this form
    is for [*pattern matching*](#pattern-matching) (accessing the members of a data structure).

  - A call where one or more arguments are input/outputs (prefixed with `!`),
    and all others, if any, are inputs.  This form of expression is itself
    considered to be an input/output.  In this form, the expression is first
    treated as an input, producing the initial value of the expression, then the
    enclosing operation is performed to update the expression value, and finally
    the expression is treated as an update operation.

Expressions containing both output and input/output arguments are not permitted.


## <a name="partial-application"></a>Partial application

If a function call is made with *fewer* arguments than is dictated by the
definition of procedure/function, the procedure is considered a partial
application. The mode of all arguments must be inputs (as the procedure is
not called where used to produce any outputs).

This binds the output name to a "partial application" of the procedure. The type
of the output variable is a higher order type containing the types and flows of
the missing arguments. The higher order type's modifiers are dictated by the
modifiers of the partially applied procedure.

The `resource` modifier is applied if the procedure may use some resource. In this
special case, the number of arguments may be no greater than the expected number
of arguments, plus one for the partially applied output.

Examples of partial applications, with accompanying type annotations, are as follows:

```
?f:(int, ?int) = `+`(1)
# equivalent to `+`(1, ?f:(int, ?int))
f(2, ?three)

?printer = print:{resource}(int)
!printer(1)
```


## <a name="type constraints"></a>Type constraints

In most cases, the compiler can determine the types of expressions used in your
code.  However, occasionally the compiler needs some help in resolving
overloading.  For example, a procedure `read(?value)` may be overloaded such
that it can read various forms of input, such as integers, floating point
numbers, and strings.  If a later operation uniquely determines the
expression's type, the compiler will work this out.  However, if other
references to the variables do not uniquely determine a type, you will need to
explicitly specify the expression type.  This is done by following the expression 
with its type, separated by a colon, similar to the way parameter types are specified:

> *expr* `:` *type*

For example,

```
read(?value:int)
```

## <a name="code-layout"></a>Code layout

In general, declarations in a module and statements in a procedure body must be
separated by semicolon (`;`)
characters.  However, as a convenience, and to improve the appearance of the
code, the semicolons can be omitted when declarations or statements are on
separate lines.  It is generally recommended to lay your code out this way.

The Wybe compiler tries to distinguish line breaks that appear in the middle of
a statement from ones that separate statements by considering adjacent
characters.  If what preceded the line break was an operator symbol, a comma,
semicolon, left parenthesis, bracket, or brace, or one of the keywords 
`in`, `is`, `where`, `pub`, `def`, `type`, `constructor`, or `constructors`,
then the line break is not considered to be a separator.  Likewise, if what
follows is an operator symbol other than `?`, `!`, or `~`, a comma, semicolon, a
right parenthesis, bracket, brace, or one of the keywords
`in`, `is`, or `where`, then the line break is not considered to be a separator.
Otherwise, the line break is treated as a separator, as if you had written an
explicit semicolon.



## <a name="function-definitions"></a>Function definitions

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


## <a name="procedure-definitions"></a>Procedure definitions

Procedures are defined with the syntax:

> `def` *name*`(`*dir* *param*`:`*type*, ... *dir* *param*`:`*type*`) {` *body* `}`

Again *name* is the procedure name, each *param* is a parameter name, the
corresponding *type* is its type, and *body* is a sequence of statements making
up the body of the procedure.  The statements in *body* should be placed on
separate lines, or should be separated with semicolon (`;`) characters.  Each
*dir* is a data flow
direction annotation, either nothing to indicate an input, `?` for an
output, or `!` to indicate both an input and an output.
Procedures may have any number of input, output, and input/output
arguments in any order.
Again each `:`*type* is optional, with types inferred if omitted,
and parentheses omitted for niladic procedures.

The procedure is private unless preceded by the `pub` keyword.
All argument types must be included in public procedure definitions.

For example:

```
pub def incr(!x:int) { ?x = x + 1 }
```

## <a name="functions-are-procedures"></a> Functions *are* procedures

Wybe functions are the same as procedures with one extra output
argument, and in fact the compiler implements them that way.  Therefore,
the definition
```
pub def toCelsius(f:float):float = (f - 32.0) / 1.8
```
is exactly equivalent to
```
pub def toCelsius(f:float, ?result:float) {
    ?result = (f - 32.0) / 1.8
}
```

Likewise, every function call is transformed into a procedure call, so:
```
pub def example(f:float, ?c:float) { ?c = toCelsius(f) }
```
is exactly equivalent to
```
pub def example(f:float, ?c:float) { toCelsius(f, ?c) }
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

Alternatively, a function can be called as a statement to update one of the
function's arguments by preceding that argument with an exclamation point (!).
Of course, the type of the input to be updated must be the same as that of the
function's output.  In the above example, if the input and output of `f` are
the same type,
```
f(!x)
```
applies `f` to `x`, storing the result in `x`.  For example,
```
!x * 2
```
or
```
2 * !X
```
would double the value of `x`, and
```
1 / !x
```
would take the reciprocal of `x`.


## Anonymous procedures

Anonymous procedures are procedure definitions that appear inline, lacking a
declaration (and hence a name) given to a regular procedure definition.

Anonymous procedures take the following forms:

> `{` *stmts* `}`

> `{` *modifier*`,` ... `}` `{` *stmts* `}`

The parameters to an anonymous procedure take one of the following two forms:
numbered and unnumbered. When either form is used, all parameters to the
anonymous procedure must have the same form.

> `@` *number*

> `@`

If parameters are unnumbered, then they are exactly equivalent to as if one had
numbered the parameters from 1, following a left-to-right-top-to-bottom order
of the source code. The number of a parameter specifies the parameter's position of the procedure.

The types of parameters are inferred via their usage and can be annotated if necessary.
The [mode](#modes) of a parameter is specified by the modes associated with it in the
contained statements-- if references to the parameter are either all inputs or
all outputs, then the parameter is as referenced, else it is in in/out mode.
If using numbered parameters and some number is skipped, this parameter is considered
an input.

The modifiers here are exactly those found in a [higher order type](#higher-order-types).
These modifiers act like the modifiers of a procedure or function declaration, stating the
purity and determinism of the anonymous procedure. The special `resource` modifier allows all in-scope [resources](#resources) to be used within this anonymous
procedure.

Some example anonymous procedures are as follows, with examples as to their use:

```
?f = { @1 + @2 = ?@3:int }
f(1, 2, ?three)

?g = {resource}{ !print(@); !print(", "); !println(@) }
# the same as `{resource}{ !print(@1); !print(", "); !println(@2) }`
!g(1, 2)
```

Anonymous procedures can also close over in-scope variables. By referring to an
in-scope variable by name, the variable is considered closed. Re-assignments of
closed variables inside the body of an anonymous procedure is *not* reflected
outside the call, nor in successive calls.

```
?i = 1
?f = { @ + i = ?@; ?i = 10 }

f(2, ?j) # j = 3; i = 1

?i = 2

f(3, ?j) # j = 4; i = 2
```

### Anonymous functions

Anonymous functions are also supported with the following syntax:

> `@(` *exp* `)`

Where *exp* is an expression that may contain a number of `@` holes as
per the parameter syntax of anonymous procedures. These parameters must all
have an input mode, and the expression may only contain input-mode variables.

This syntax is a syntactic sugar for an anonymous procedure, that is equivalent to the following:

> `{ foreign llvm move(` *exp*`, ?@) }`

with the output `@` with an appropriate numbering. 

For example, the following pairs are equivalent:

```
@( @ + 1 )
{ ?@2 = @1 + 1 }

@( @2 ^ @1 )
{ @2 ^ @1 = ?@3 }
```


##  <a name="operator-syntax"></a>Operator syntax

A procedure, function, or constructor whose name entirely consists of one or
more of the operator characters
```
    @ $ % ^ ~ & | + - * / = < > \ , ; . :
```
as well as the special operator name `in`, may use the alternative infix syntax:

> *arg1* *op* *arg2*,

where *op* is the procedure or function name (there must be exactly two
arguments).  This is *exactly* equivalent to `` `op`(``*arg1*,*arg2*`)`.

There is no need to explicitly declare operators.  Aside from the
few reserved operator symbols documented in the
[reserved words](#reserved-words) section, every sequence of operator characters
is a valid infix operator name.

The precedence and associativity of infix operator symbols is determined by the
last character in the operator, as follows:

| Last character | Precedence    | Associativity   |
| -------------- | ------------- | --------------- |
| `^`            | 10 (Highest)  | Left            |
| `* / %`        | 9             | Left            |
| `+ -`          | 8             | Left            |
| `, .`          | 7             | Right           |
| `< >`          | 6             | Not associative |
| `;`            | 5             | Right           |
| `: =`          | 5             | Not associative |
| `~`            | 5             | Left            |
| `&`            | 4             | Right           |
| `\|`           | 3 (Lowest)    | Right           |

Additionally, `in` is a non-associative infix operator of precedence 5.

Wybe also has two prefix operators:  `-` and `~`.  These have precedence 11, so
they bind tighter than any infix operator.

Wybe has no postfix operators, however it does support following an expression
with a sequence of zero or more expressions enclosed within square brackets, the
conventional syntax for array indexing.  This has precedence 12, so it binds
tighter than any infix or prefix operator.

As in most programming languages, parentheses may be used to override operator
precedence and associativity.

Wybe also supports an alternative syntax for invoking procedures, functions, or
constructors that puts the (first) argument first, and the procedure, function,
or constructor name, with its other arguments, if any, second:

> *arg*`^`*operation*(*other args*)

and in the special case of operations taking only one argument:

> *arg*`^`*operation*

This syntax is akin to the common object-oriented *object.method* syntax.  There
is no semantic difference between this syntax and the standard
*operation*`(`*arg*,*other args*`)` or *operation*`(`*arg*`)` syntax.
Because the `^` associates to the left, this syntax can be chained to apply a
"pipeline" of operations to an initial input, so the expression:

```
    ob^foo^bar^baz
```

is equivalent to

```
    baz(bar(foo(ob)))
```

Finally, as a convenience, for procedures (but not functions) with only one
argument, Wybe allows the parentheses surrounding the argument to be omitted.
For example, Wybe allows you to write
```
    !print 3+4
```

as an alternative to

```
    !print(3+4)
```

Wybe supports a special syntax for lists.  For example, a list of the first 3
counting numbers would be written `[1,2,3]`.  The syntax `[h|t]` denotes a list
whose head is `h` and whose tail is `t`, and `[e1,e2|es]` is a list whose first
two elements are `e1` and `e2`, and the rest of which is `es`.  Note that what
appears before the `|` symbol are individual list elements, separated by commas,
and what appears after it is another list.  The empty list is denoted `[]`. The
list constructor is named `[|]`, so the list `[e1,e2|es]` can also be written ``
`[|]`(e1,`[|]`(e2,es))`` and the list `[1,2,3]` can be written
`` `[|]`(1,`[|]`(2,`[|]`(3,[])))``.

## Declaring operator functions and procedures

Procedures and functions whose names are operators should be declared using
their operator syntax, but with the function name and arguments enclosed in
parentheses.  For example, the `+` function should be declared using the
following syntax:

```
def (a:int + b:int):int = ...
```

Alternatively, the "operatorness" of a name can be overridden, making the
compiler treat it as an ordinary identifier, by surrounding it with backquote
characters (`` ` ``).  So the `+` function could also be defined with the
syntax:
```
def `+`(a:int, b:int):int = ...
```
These two definitions are equivalent:  whichever is used, the `+` function name
can be used as an infix operator.

Backquotes can also be used in function calls, so `` `+`(3,4)`` is semantically
identical to `3 + 4`, regardless of which syntax was used to define the `+`
function.

Backquotes can also be used to make almost any sequence of characters act as a
symbol.  The only characters that cannot appear between backquotes are newlines,
other control characters (such as tabs and escape characters), the hash (#)
character, and the backquote character itself.


##  <a name="reserved-words"></a>Reserved operators

The following special operators are predefined by the Wybe language. These may
not be defined as procedure, function, or constructor names.  Except where
otherwise indicated, they are infix operators.

| Reserved names | Meaning
| ----------- | --------------------------------------------------------------- |
| `,`         | Function, procedure, and list argument separator                |
| `.`         | Module prefix separator                                         |
| `^`         | Procedure/function pipeline application                         |
| `;`         | Statement separator                                             |
| `:`         | Type specification                                              |
| `:!`        | Type cast specification (in [foreign code](#foreign-interface)) |
| `::`        | Condition/case separator                                        |
| `\|`        | Disjunction                                                     |
| `&`         | Conjunction                                                     |
| `?`         | Output variable annotation (prefix)                             |
| `!`         | Input/Output variable annotation (prefix)                       |
| `if`        | If statement/expression (`if {` ... `::` ... `}`)               |
| `case`      | Case statement/expression (`case expr in {` ... `::` ... `}`)   |
| `else`      | Final default case in `if` and `case` statements/expressions    |
| `let`       | Local variable definition (`let` ... `in` ...)                  |
| `where`     | Local variable definition (... `where` ... )                    |
| `use`       | Local resource binding (`use {`...`} in {`...`}`)               |



## <a name="modes"></a>Modes

It is permitted to define multiple procedures with the same name, as
long as each of them have different parameter *types*
or *modes*, or different arities.  A mode is a combination of argument
directions.  This can be used to carry out computations in different
directions.  For example:

```
pub def add(x:int, y:int, ?xy:int) { ?xy = x + y }
pub def add(x:int, ?y:int, xy:int) { ?y = xy - x }
pub def add(?x:int, y:int, xy:int) { ?x = xy - y }
```

Like any procedures, all of these can be called as functions, so with
these definitions, all the following are valid:
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


## <a name="tests"></a>Tests and partial functions

Some procedure or function calls are *tests*.  This means that they can return
whatever output(s) they are meant to produce, assigning or reassigning variables
as specified, or instead they can *fail*, in which case they do not produce
their usual output(s), leaving all variables and resources as they were before
the test began.
Functions that may fail to produce a result for some inputs are also known as
*partial* functions.

Test procedures and functions must be explicitly declared by inserting
the modifier `test`, enclosed within curly braces, after the `def` keyword.
You can instead use the modifier `partial` in place of `test`.  For example:

```
def {test} even_number(num:int) { num % 2 = 0 }
def {partial} lookup(key:int, table:map) = ...
```

Calls to test (partial) procedures and functions are only permitted in three
contexts:  in a [conditional](#conditionals), in the definition
of a test/partial procedure or function, or in a
[reified expression](reification).

Tests can take several forms:
  *  A call to a test procedure is a test.
  *  Any procedure call containing one or more partial function calls is also a
     test; it succeeds only if all the partial function calls succeed, and when
     any call fails the test fails immediately.
  * A sequence of statements including one or more tests is a test; it
    succeeds if and only if all the tests succeed, and fails immediately if
    any test fails.
  * Any procedure or function call is a test if an input is provided
    where an output argument is expected.  In this case, the call is made
    producing the output, and then the output is compared for equality with
    supplied input.  Equality (`=`) with two input arguments is a test, so
    these two calls are equivalent tests (in fact, the former is transformed to the
    latter):

    ```
    add(x, y, xy)
    xy = add(x, y)
    ```
  * A foreign language call can be a test; see the [foreign language
    interface](#foreign-language-interface) section for details. 
  * Finally, a Boolean value by itself can also be used as a test, in which case
    `true` succeeds and `false` fails.  This applies both to Boolean variables
    and Boolean-valued functions.  However, tests are a more general facility
    than Boolean-valued functions, because they can produce other outputs aside
    from success or failure.  

This flexibility makes Wybe tests more general than Boolean-valued functions.
Because nested partial function calls and compound statements involving tests
are considered to be tests, one can carry out a computation in which any of
several steps may fail, and handle all possible failures together.  For example,
taking the head of a list is a partial function, as is looking up a value in a
table, so `lookup(head(list), table)` will immediately fail if `list` is empty,
and if not, will fail if the head of the list is not present in the table.

Because deconstructors are tests for types with multiple constructors, Wybe also
naturally provides [pattern matching](#pattern-matching).  For example,

```
xs = [0 | ?rest]
```

would succeed if `xs` is currently a list whose head is `0`, and would assign
`rest` to the tail.  It would fail if `xs` does not match that pattern, either
because it is an empty list or because its head is not `0`.

Note that all effects of a test are reverted if the test fails, including
reassignments of variables or modifications of resources.  However, some
effects, such as performing input/output, cannot be reverted, and therefore
these effects cannot be performed within a test.  The compiler will issue an
error message in such cases.


## <a name="reification"></a>Reification of tests

Wybe allows a call to a test procedure to be reified into a Boolean value, as
long as the call does not produce any outputs.  This allows you to save the
success or otherwise of a test in a Boolean variable for later use.  For
example, with the definition of `even_number` shown in the
[Tests and partial functions](#tests) section, the following code will save
whether or not a number is even in a variable for later use as a test.

```
?is_even = even_number(n)
```

Combined with the fact that Boolean values can be used as test, this makes test
procedures with no outputs effectively interchangeable with Boolean valued
functions.


## <a name="disjunction"></a>Disjunction

Statements and sequences of statements can be disjoined using the `|` operator.
For example,

>   *statement1* `;` *statement2* `|` *statement3* `;` *statement4*

Note that `|` binds looser than `;` (or newline), so in this example,
*statement1* `;` *statement2* is the first disjunct, and  *statement3* `;`
*statement4* is the second.  Each disjunct can have one or more statements, and
there can be more than two disjuncts by repeating the `|` operator.
You can enclose a disjunction within `{` braces `}` to limit the scope of
a disjunction. 

If the first disjunct completes without a failure, the second and subsequent
disjuncts are ignored.  However, if any [test or partial function call](#tests)
in the first disjunct fails, Wybe will begin executing the first statement of
the next disjunct, as if the first disjunct were never executed.  This means
that any assignments that were made by that disjunct will not be available as
execution of the next disjunct begins.  In general, if any disjunct fails, the
next disjunct is attempted, and if one disjunct completes without failing, all
following disjuncts are ignored.  If all disjuncts fail, then the whole
disjunction fails.

Braces may be used for grouping, so that code before or after the disjunction
will always be executed, regardless of which disjunct succeeds.  Variables bound
before the start of the disjunction will be available at the start of every
disjunct, and variables that are bound by *every* disjunct will be available in
following code, and are considered to be bound by the enclosing procedure.

Disjunction can be used in a test procedure, in which case the test succeeds if
any disjunct succeeds.  It can also be used in an ordinary (deterministic)
procedure, in which case the final disjunct must not be a test, to ensure that
the disjunction always succeeds.

Disjunction can also be used in expressions using a similar syntax:

> `(` *expression1* `|` *expression2* `)`

where each expression can involve partial function calls.  Note that the
parentheses are required because of the precedence of the `|` operator.  The
value of this expression will be the value of *expression1* if no failure occurs
during its evaluation, or *expression2* otherwise.  Each expression can involve
any number of partial function calls, and will be considered to succeed if and
only if all the partial function calls succeed.  As with disjunctive
statements, a disjunctive expression can have two or more disjuncts, and is
partial (a test) if and only if the last disjunct is partial.  For example, we
can define a function to return the tail of a list, or return the empty list if
the input list is empty:

```
pub def saturating_tail(lst:list(T)):list(T) = (tail(lst) | [])
```


## <a name="pattern-matching"></a>Pattern matching

Like procedures, some Wybe functions can be "run backwards", where the function
result is supplied as input and some or all of its arguments are produced as
outputs.  You can explicitly define such a "reverse mode" of a function, by
preceding output arguments with a `?`, and by making the value of the function
an expression of the form

> `?`*var* `where {` *body* `}`

and defining *body* to compute the values of the output arguments treating *var*
as an input.

This can serve the role filled by *pattern matching* in other programming
languages.  Indeed, when constructors are defined in Wybe (see the section on
[constructor declarations](#constructor-declarations)), the compiler
automatically generates a backward mode function for each constructor function.
For example, if you define a type `position` with a constructor `position(x:int,
y:int)`, the compiler automatically generates a backward mode function
`position(?x:int,?y:int)`.  Thus, a new position can be created with the
statement
```
?pos = position(x, y)
```
and an existing position can be deconstructed to extract its `x` and `y`
components with the statement
```
pos = position(?x, ?y)
```

For types with multiple constructors, backwards construction can fail.  For
example, if the type `position` is defined with two constructors
```
constructors cartesian(x:float, y:float) | polar(r:float, theta:float)
```
then exactly one of the statements
```
pos = cartesian(?x, ?y)
```
or
```
pos = polar(?r, ?theta)
```
will succeed, and the other will fail.  Therefore, these statements are tests,
and can only appear where test statements are allowed, such as in a [conditional
statement](#conditionals).  Note that variables assigned by such a test cannot
be used outside the context in which that test has succeeded.

Patterns can also be nested.  For example, with the type `region` defined by:
```
constructor region(bottom_left:position, top_right:position)
```
the statement
```
region(cartesian(?x1,?y1),cartesian(?x2,?y2)) = reg
```
will deconstruct a region `reg` expressed as two Cartesian coordinates.

It is also possible to include input values where outputs are expected, as long
as the type supports an equality test.  This is equivalent to providing an
output variable, and then comparing the value produced for that output to the
specified value.  This is called an *implied mode* for that argument.

As a convenience, you can specify the special "don't care" value `_` as an
output.  This matches any value that may be produced.

For
example, you could define a test that the lower left corner of a region sits at
the origin as follows:
```
def {test} at_origin(reg:region) {
    reg = region(cartesian(0.0,0.0), _) | reg = region(polar(0.0,_),_)
}
```
Equivalently, it could be written:
```
def {test} at_origin(reg:region) {
    reg^bottom_left = cartesian(0.0,0.0) | reg^bottom_left^r = 0.0
}
```


## <a name="structure-update"></a>Structure update

Wybe semantics does not allow data structures to be destructively modified.

However, variables can be reassigned, and new data structures can be created
that differ from existing ones only in one field, and Wybe provides a convenient
way to combine these two things to support data structure update.  For example,
if you define a type `position` with a constructor `position(x:int, y:int)`, the
compiler not only generates a constructor and deconstructor function, and
accessor functions for the fields `x` and `y` that map from a `position` to an `int`, 
it also generates backward mode structure update functions `x` and `y`.  
Using the convenient infix `^` [operator syntax](#operator-syntax), a statement
```
!pos^x = 0
```
would set `pos` to a position with the same `y` component as the previous
version of `pos`, but with 0 for the `x` component.  Effectively, this just sets
the `x` component of `pos` to 0 without changing its `y` component.  However,
this does not affect any variable other than `pos`.  Similarly,
```
incr(!pos^y)
```
would increment the `y` component of `pos`.

If a field is shared by multiple constructors for a type, then a single accessor 
and updater function will be generated, which can be used to access or update 
said field across all such constructors. 

For types with multiple constructors where a field is not shared by all constructors,
structure updates for said fields become tests, and therefore can only be used in 
test contexts.  For example,
```
!lst^head = 42
```
might appear in a [conditional statement](#conditionals), which would also
specify what to do if `lst` is empty.  These can all be combined to replace the
`y` component of the second element of `lst` with 0:
```
!lst^tail^head^y = 0
```
This will fail if either the list is empty or its tail is empty, therefore,
again, this must appear in a test context, such as a conditional.


## <a name="conditionals"></a>Conditional statements

Wybe's main conditional construct has the form:

> `if` `{` *cases* `}`

where *cases* is one or more cases, separated by vertical bar characters
(`|`). Each case takes the form:

> *test* `::` *statements*

where *test* is a test statement and *statements* is one or more statements
separated by semicolons (`;`) or newlines.
Execution proceeds by executing the first *test*, and if it succeeds, executing
the corresponding *statements*, thereby completing the `if` statement.
If the first *test* fails, its corresponding *statements* are skipped and
the second *test* is tried.
If this test succeeds, its corresponding *statements* are executed, and so on.
At most one *statements* sequence is executed, but if none of the specified
*test*s succeed, none of the *statements* are executed.
The last test may optionally be the keyword `else`, which always succeeds, 
so it may be used to provide code to execute if none of the preceding tests succeeds.

For example:
```
if { x < 0 :: !println("negative")
   | x = 0 :: !println("zero")
   | else  :: !println("positive")
}
```

Other conditional constructs include [case statements](#cases),
[conditional and case expressions](#conditional-and-case-expressions),
and loop control tests, as discussed in the
[iteration statements](#iteration-statements) section.


## <a name="cases"></a>Case statements

Wybe's `case` construct has the form:

> `case` *expression* `in {` *cases* `}`

where *expression* is used to select the code to execute, and *cases* is one
or more cases, separated by vertical bar characters (`|`). Each case takes the
form:

> *case_expr* `::` *statements*

where *case_expr* is an expression and *statements* is one or more statements
separated by semicolons (`;`) or newlines.  Each *case_expr* is matched in turn
with the initial *expression*; when a match is found, the corresponding
*statements* are executed, and all others are ignored.  If the final *case_expr*
is the `else` keyword, and no earlier *case_expr* matched, then the *statements*
corresponding to the `else` *case_expr* will be executed.  If no *case_expr*
matches and there is no `else` case, then no *statements* will be executed.  In
any case, execution then continues after the `case` statement.

A *case_expr* can be a backward mode expression to select cases based on
[pattern matching](#pattern-matching).  A `case` statement is semantically
equivalent to an `if` statement where each *test* is of the form *case_expr* `=`
*expression*, although the *expression* will only be evaluated once.

For example:
```
case coord in {
    cartesian(?x,?y) :: println(sqrt(x**2 + y**2))
|   polar(?r,_)      :: println(r)
}
```

## <a name="conditional-expressions"></a>Conditional and case expressions

Wybe's conditional and case constructs can also be used as expressions.  Both
have the same form as their statement versions, except that instead of each case
providing one or more statements, they provide a single expression.

Note that for both `if` and `case` expressions, the `else` is required.

For example:
```
!println(
    if { x < 0 :: "negative"
       | x = 0 :: "zero"
       | else  :: "positive"
    })
```
and
```
println(
    case coord in {
      cartesian(?x,?y) :: sqrt(x**2 + y**2)
    | polar(?r,_)      :: r
    | else             :: error("should not be possible")
})
```

Note that where an `if` or `case` expression is used as an argument of another
expression, it must be enclosed within parentheses.


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


## <a name="iteration-statements"></a>Iteration statements

Iteration is specified with the `do` and `for` statements, of the form:

> `do` `{` *statements* `}`

or

> `for` *generator* `{` *statements* `}`

where a *generator* is one or more expressions of the form

> `?`*var1*  `in` *sequence*

separated by semicolons or newlines. Each *generator* is a value of any
type that implements the backwards mode of the cons operator (`[|]`),
where the list is input and the head and tail are outputs. Presently
`array`, `list`, and `range` in the standard library implement this operator.

The enclosed *statements* in both `do` and `for` loops may include any ordinary
Wybe statements, plus any of the following:

> `break`

Exit the loop immediately, continuing execution with the code following the
loop.  For a `for` loop, this may mean some values of the generators will never
be generated.

> `next`

Immediately return to the top of the loop without completing the current
iteration.  For a `for` loop, move on to the next value(s) of the generator(s).

> `while` *test*

If *test* fails, exit the loop immediately, otherwise continue.

> `until` *test*

If *test* succeeds, exit the loop immediately, otherwise continue.

> `when` *test*

If *test* fails, restart the loop immediately, otherwise continue.

> `unless` *test*

If *test* succeeds, restart the loop immediately, otherwise continue.

These special loop control statements may be used anywhere inside a `for` or
`do` statement. For example:

```
do {!print(prompt)
    !read(?response)
    until valid_answer(response)
    !println("Invalid response; please try again.")
}
```


## <a name="submodules"></a>(sub)modules

A Wybe module may contain submodules.
Each submodule of a module has access to everything in the containing module,
whether or not it is public.
However, the parent module can only access items declared `pub`lic in its
submodules.
The parent module need not explicitly import its submodules; this is done
automatically.

A submodule is declared as follows:

> `module` *name* `{` *items* `}`

where *name* is the module name and *items* are the contents of the submodule,
separated by newlines or semicolons.


## <a name="defining-types"></a>Defining Types
### <a name="constructor-declarations"></a>Constructor declarations

Wybe supports abstract algebraic data types. Every Wybe type is a module, and
each type's primitive operations are the operations of that module. A module
becomes a type just by declaring the type's constructor(s) with a declaration of
the form:

> `constructors` *ctors*

where *ctors* is one or more constructor declarations, separated by vertical bar
characters (`|`).  Each constructor declaration takes the same form as the
prototype part of a function declaration:

> *ctor*`(`*param*`:`*type*, ... *param*`:`*type*`)`

In contrast to regular procedure prototypes, the parameter names are optional,
and can be removed, along with the accompanying `:`.

If *name* is an infix operator symbol, you must surround it with backquotes, or
declare the constructor with infix syntax, much like defining a function
whose name is an operator, again with optional parameter names:

> `(`*param*`:`*type* *ctor* *param*`:`*type*`)`

This declaration defines a constructor function *ctor* that takes parameters of
the specified types and returns a value of the type being defined (namely, the
current module) holding all the provided data.  Constructor functions can also
be used ["backwards"](function-calls), with the constructed value provided and
the arguments taken as outputs, to extract the data stored in the constructed
value.  Note that, unlike object-oriented languages, a constructor in Wybe
cannot specify a body, it simply creates a value of the specified type
containing the specified data.  If you wish to carry out some computation to
determine what values to store, you may write a function or procedure that calls
the constructor.  Since Wybe does not require any special syntax to call a
constructor (such as `new` in many object-oriented languages), they are ordinary
functions, aside from the fact that they are automatically generated.

The form of declaration above keeps the constructors of a type private; they may
be used within the current module, but not outside.  To make all constructors
public, simply precede the `constructor` keyword with `pub`. 
If you want a particular constructor to be public, precede that constructor 
with the `pub` keyword.

Note that, unlike most object-oriented languages, making constructors public
does not commit you to any particular representation of the type.
You may define your own public functions to act as constructors, and they will
be indistinguishable from the actual constructors by users of the type.

As a convenience, you may use the keyword `constructor` instead of
`constructors` in the declaration; Wybe makes no distinction between them.

For example, you can make the enclosing module define a Cartesian coordinate
type with the following declaration:

```
pub constructor coordinate(x:int, y:int)
```

With this declaration,
the following statement may be used to construct a Cartesian coordinate with X
component 7 and Y component 4:
```
?pos = coordinate(7,4)
```
And this statement will unpack a coordinate `pos` into variables `x` and `y`:
```
coordinate(?x,?y) = pos
```

Additionally, two procedures are automatically generated for each named
*member*: one to access the member, and one to mutate it.
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

Even more conveniently, for the first of these, you can use the infix `^`
function call syntax.  In the example above, the second line could instead be
written:

```
!println(pos^x)
```

It is important to note that "mutating" a value does not actually modify it in
place; it creates a fresh value of that type that is identical except for the
member being changed.
Wybe does not have the concept of
[object identity](https://en.wikipedia.org/wiki/Identity_(object-oriented_programming)),
nor the concepts of pointers or references.
You can safely have multiple variables refer to the same data without worrying
that modifying the data through one of them will change the values of the
others.  Thus, Wybe implements a
[copy-on-write](https://en.wikipedia.org/wiki/Copy-on-write) semantics.
For example
```
?pos = coordinate(7,4)
!println(pos^x)
?oldpos = pos
incr(!pos^x) # shift pos to the right; doesn't affect oldpos
!println(pos^x)
!println(oldpos^x)
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
!println(pos^x)
incr(!pos^x)  # shift pos to the right
!println(pos^x)
```
so that it does in fact mutate the coordinate object in place,
saving an unnecessary object creation.

The `constructors` declaration must specify the forms of all the possible values
of that type.  Wybe does not support a special *null* or *nil* value.  For
example, you could define a binary tree type as follows:
```
constructors empty | node(left:_, value:int, right:_)
```
(Note that the type `_` is an
[alias for the type defined in the current module](#_-type).)

Deconstructing a value of a type with multiple constructors,
or accessing or altering any of its members, is a test, since the
value may not have the intended constructor.
This ensures that it is not possible to mistake a value created with one
constructor for one made with a different constructor.
In the tree type example, you might write:
```
def {test} member(elt:int, tree:_) {
    if { node(?left, ?value, ?right) = tree ::
            if { elt = value:: succeed
               | elt < value:: member(elt, left)
               | else       :: member(elt, right)
            }
       | else:: fail
    }
}
```

## <a name="_-type"></a>The `_` type

As a special case, the type `_` is treated as an alias for whatever type is
defined by the module in which it appears.  That provides a shorter
name for the type being defined, and also allows the type to be renamed simply
by renaming the file it is defined in.  For example, the following code could
be placed in a Wybe source file to define a linked list type with whatever name
is deemed suitable.

```
constructors(T) null | cons(head:T, tail:_(T))


def concat(a:_(T), b:_(T)):_(T) =
    if cons(?h, ?t) = a then cons(h, concat(t,b)) else b
```


## <a name="type-declarations"></a>Type declarations

In some cases, a module may wish to define multiple types.  This can be done by
declaring separate submodules within the module, and declaring constructors in
each of those submodules.  As a convenience, Wybe allows the submodule and its
constructors to be declared with a single declaration of the form:

> `type` *type* `{` *ctors* *defs* `}`

where *type* is the module name and *ctors* declares one or more constructors,
separated by vertical bar characters (`|`), just as they would appear in a
`constructor` declaration.
To make the declared *type* public, precede the `type` keyword with the keyword
`pub`.

Optionally, the constructors can be preceded by the `constructors` 
(or `constructor`) keyword. Each constructor can be made public by preceding
that constructor with the `pub` keyword. To make all constructors public, precede
`constructors` keyword with `pub`.

The *defs* part may be empty, but if specified, may include any number of
procedure and function declarations, which will have full access to the
constructors of the type, whether or not they are public.


## <a name="generics"></a>Generic types

Wybe supports *generic* types, a feature called *parametric polymorphism*. A
generic type is one that takes other types as parameters, specified by following
the type name with the desired parameters, separated by commas and enclosed in
parentheses. For example, the elements of a list must all be the same type, but
that can be any valid Wybe type; a list of integers can be specified by
`list(int)` and a list of lists of strings can be specified as
`list(list(string))`. This allows list operations to work with lists of any
element type, without the need to separately define different kinds of lists, or
the operations on them.

The basis of generic types is the *type variable*, which stands for a type we
don't know yet, and thus is a variable in the type system.  A type variable is
denoted by an uppercase letter followed by zero or more numbers.  Since we
rarely have more than one or two type variables in any given context, we
conventionally use a single upper case letter for a type variable.

Generic types are defined in the same way as described above, except that:

  * the keyword `constructor` or `constructors` is followed by a list of type
    variables separated by commas and enclosed in parentheses; and
  * these type variables may be used as types in the definitions of the
    constructors of the type.

For example, a generic list type can be defined as:

```
constructors(T) null | cons(head:T, tail:_(T))
```

If specified with a `type` declaration, this would be written:

```
type list(T) {null | cons(head:T, tail:_(T)) ... }
```

All type variables appearing in the definition of any constructor must appear in
the list of type parameters.

Generic types can also be specified in procedure parameters by using type
variables.  Each occurrence of the same type variable must signify the same
type.  For example, you can define list concatenation:

```
def concat(a:list(T), b:list(T)):list(T) =
    if { cons(?h, ?t) = a:: cons(h, concat(t,b)) | else:: b }
```

This will concatenate lists of any type, but the types of the elements of the
two input lists must be the same, and the result will be a list of the same
type.


## <a name="resources"></a>Resources

Resources provide an alternative argument passing mechanism,
based on name rather than argument position.
They are intended for values that are unique in the computation,
where there is only one value of that sort in each part of the computation,
yet the value is used widely in the program.
For example, the command line parameters of an application may used in many
parts of the code, but explicitly passing that throughout the application
may be a nuisance.
An application may build up logging message throughout, but explicitly threading
the log through the entire application can become tiresome, and can make code
maintenance more difficult.
Resources are often useful where an imperative application would use a global or
static variable, or where an object-oriented application would use a class
variable.

### <a name="resource-declarations"></a>Declaring a resource

The benefit of resources is that they are lightweight,
because they do not need to be explicitly passed between procedures
and their type only needs to be specified once,
where it is declared.
Passing a value as a resource
also ensures that it is named and used consistently
throughout the module that declares it, and any modules that import it.

A resource can be declared at the level of a module, as follows:

> `resource` *name*`:`*type*

It may optionally specify an initial value:

> `resource` *name*`:`*type* `=` *expr*

In this case, the resource is
defined in any top level code in that module, as well as any top level code in
any module that `use`s this module, but not in any module that this module
`use`s.  The latter restriction is necessary because when two modules depend on
one another, the order in which their resources are initialised is unspecified.

A resource may be exported, allowing it to be referred to in other modules, by
preceding the `resource` declaration with the `pub` keyword.

### Defining a resourceful procedure

Any procedure may declare that it uses any number of resources,
providing the named resources are visible in the enclosing module
(i.e., defined in that module or any imported module),
by adding a `use` clause to the procedure declaration,
between the procedure header and body:

> `def` *name*`(`*params*`)` `use`
> *dir<sub>1</sub>* *resource<sub>1</sub>*, ...
> *dir<sub>n</sub>* *resource<sub>n</sub>* `{` *body* `}`

Each *dir<sub>i</sub>* indicates the direction of information flow for the
corresponding resource; as for parameters, no flow prefix indicates that the
resource is only an input, a question mark (`?`) indicates it is only an output,
and an exclamation point (`!`) indicates that the resource is both input and
output.
The order in which the resources are listed is not significant, and any number
of resources may be specified.
This allows the resource name to be used as a local variable in the procedure
body, just as if it were an ordinary parameter.

Importantly, resources available in a procedure become available in any
procedures it calls that also declare that they `use` that resource.

### <a name="calling-resourceful"></a>Calling a resourceful procedure

A procedure may only be called in a context in which all the resources it uses
are defined, and a call to a resourceful procedure must be preceded by an
exclamation point (`!`) to signify that it receives inputs or produces outputs
that do not appear in its argument list.
This exclamation point serves as a warning that some values not explicitly
listed among the arguments in the call are used or defined or both, and the
declaration of the procedure must be consulted to see which values they are.

Most commonly, a procedure that uses a resource is called in the
definition of another procedure that uses that resource.
However, it may also be called inside a [scoped](#scoping) resource use.

### <a name="scoping"></a>Scoping a resource use

A resource may have its value scoped to a number of statements and the
procedures called by those statements, and so on recursively.
This creates a scope in which the resource is known, allowing a procedure that
is not declared to use a resource to call a procedure that does.
A scope introducing one or more resources may be specified with a statement of
the form:

> `use` *resource<sub>1</sub>*`,` ... *resource<sub>n</sub>* `in` `{` *body* `}`

If the resource was undefined prior to entering the `use` statement,
it will still be undefined at the start of the *body*, and it will again
be undefined after the `use` statement completes.
If the resource is already defined outside the scope of the `use` statement,
the value at the start of *body* will be the same as the value before the `use`
statement, and the value at the completion of the *body* will again be the same
as the value before entering the `use` statement.
Thus a `use` statement will not alter the existence or the values of the
resources it names. This also applies to higher order terms that have a
`resource` modifier.


### Predefined resources

Wybe uses predefined resources for a few key language features.
In particular, the `io` resource holds a representation of the state of the
world outside the computation being performed, including the file system.
Thus, all procedures that perform input/output are declared to `use !io`,
the `!` being necessary because any procedure that performs I/O changes the state of
the world outside the computation, either by outputting something, or by
changing the part of an input stream being read.
Therefore, any call to a procedure that performs I/O (or that calls a procedure
that performs I/O) must be preceded with an `!` to indicate that it modifies a
resource.

The `io` resource is implicitly defined at the top level of a Wybe program.
There are also predefined `argc` and `argv` resources holding the number of
command line arguments and an array of the arguments themselves.  The `command`
resource holds the name by which the current executable was executed, as a
string, and the `arguments` resource holds the command line arguments supplied
when the program was run, as an array of strings.  Finally, the `exit_code`
resource is initialised to 0 at the start of execution, and may be changed to
any integer during the computation to set the exit condition that will be
returned to the operating system at the termination of the program.  To use the
`argc`, `argv`, `command`, `arguments`, or `exit_code` resources, a module must
`use` the `command_line` module.  This is part of the Wybe library, but is not
automatically imported.

### Implicit resources

Wybe defines a few "implicit" resources, which do not actually reflect the state
of the computation, but instead provide access to information about the
program's source code.  Implicit resources are built into Wybe, and thus do not
need to be imported.

Because they only depend on the program source code,
which is always available, implicit resources can be used anywhere.  If a
procedure that uses an implicit resource is called in the context of a procedure
that does not `use` that resource, the value supplied for the resource reflects
the location of the source code of the call to that procedure.  If called in the
context of a procedure that does `use` that resource, the value of the resource
in that context is used.  Thus, a procedure can obtain information about the
context in which it is called simply by using the appropriate resources.
However, if that procedure is called from another procedure that uses that
resource, the caller's caller's calling context will be used instead.

Because implicit resources are read-only and available everywhere, a
call to a 
procedure that uses only implicit resources need not be preceded with an
exclamation mark.  Similarly, a procedure that uses no non-implicit resources
can be called using function application syntax.  However, because the `use`
syntax is not permitted in function declarations, it must be defined as a
procedure (see the [Functions are Procedures](#functions-are-procedures) section).

The implicit resources supported by Wybe are:

| Resource Name                | Type       | Meaning                                            |
| ---------------------------- | ---------- | -------------------------------------------------- |
| `call_source_file_name`      | `c_string` | the name of the file in which the call appears     |
| `call_source_file_full_name` | `c_string` | the name and directory in which the call appears   |
| `call_source_line_number`    | `int`      | the line number on which the call appears          |
| `call_source_column_number`  | `int`      | the column number of the start of the call         |
| `call_source_location`       | `c_string` | the file name, line, and column number of the call |
| `call_source_full_location`  | `c_string` | the call directory, file name, line, and column    |


## <a name="uniqueness"></a>Unique types

*Unique* types are types instances of which are only permitted to have a single
reference during program execution.  This ensures that values of this type are
threaded linearly through program execution.  If a value of a unique type is
passed as an argument to a procedure or function, then it cannot be passed as an
argument to any other procedure or function (or as two or more different
arguments in a single procedure or function call).  In practice, that means that
a unique value is generally passed both into and out of a procedure, typically
using the `!`*variable* syntax (see [variables](#variables)).  It is often most
convenient to pass unique values around as resources, without referring to them
by name.  This ensures that they are threaded linearly.

The `wybe.phantom` type, which is the type of the `io` resource, is defined to
be unique.  This prohibits any code that would make a copy of the `io` resource.
For example, both of these code samples are **illegal** in Wybe:

```
def bad1 use !io {
    ?mustnt = io
}

def bad2 use !io {
    if {
        !read('x':char) ::
            !println("Read an x")
    |   else ::
            !read(_:char)
            !println("Read something else")
    }
}
```

The first one is an error because both `mustnt` and the `io` resource hold the
same phantom value.  The second one is erroneous because the same value of the
`io` resource is used for the `read` statement and for the second `println`
statement (remember, the values of all variables at the start of an else branch
are the same as at the start of the condition).  The second example could
legally be written as:

```
def ok2 use !io {
    read(?ch:char)
    case ch in {
        'x' :: !println("Read an x")
    |   else:: !println("Read something else")
    }
}
```

This also means that the `io` resource must be passed both into an out of a
procedure that may perform input/output; therefore, a calling a procedure
declared to `use io`, instead of `use !io` will cause an error, because after
the call to that procedure, the `io` resource would be returned to the value it
held prior to the call.


### Declaring unique types

A type may be declared to be unique by including the `{unique}` modifier when
declaring the type.  For a `constructor` (or `constructors`) declaration, 
the declaration of a unique type takes this form:

> `constructor` *typevars* `{unique}` *ctors*

where *typevars* is either empty or a parenthesised list type type variables, 
and *ctors* is [as described above](#constructor-declarations).  For example:

```
constructor {unique} unique_position(x:int, y:int)
```

When used in a `type` declaration, it has this form:

> `type` `{unique}` *type* `{` *ctors* *defs* `}`

Note that parameters of constructors must not have unique types, unless the
constructor is a member of a unique type.  Also, accessors for unique types are
not usually useful, because once you have accessed one member of the type, you
cannot use the value again, such as to access the other members.  Instead, it is
usually preferable to use a deconstructor.  This code is illegal, because it
uses `uniq_pos` twice:

```
?uniq_pos = unique_position(3,4)
...
?radius = sqrt(uniq_pos^x ** 2 + uniq_pos^y ** 2)
```

However, this equivalent code is legal:

```
?uniq_pos = unique_position(3,4)
...
unique_position(?x, ?y) = uniq_pos
?radius = sqrt(x ** 2 + y ** 2)
```

Note that unique types do not have equality and disequality tests (`=` and `~=`)
automatically generated for them, because they are unlikely to be useful.


## Packages

Each Wybe source file defines a module whose name is the base name of the file.
A number of modules may be grouped together into an overarching module by
putting them together in a directory containing a (possibly empty) file named
`_.wybe`.  The name of the overarching module is the base name of the directory.
For example, given a directory hierarchy:

    /a/b/c/d/
    /a/b/c/d/_.wybe
    /a/b/c/d/e.wybe
    /a/b/c/d/f.wybe
    /a/b/c/d/g/
    /a/b/c/d/g/_.wybe
    /a/b/c/d/g/h.wybe
    /a/b/c/d/g/i.wybe

the name of the module defined in `e.wybe` is `d.e`, because the
file `/a/b/c/d/_.wybe` makes `d` a module.  Likewise, `h.wybe` is the module
`d.g.h`.

As discussed in the section on [importing modules](#importing), a module may be
imported by specifying its full name in a `use` declaration.  For example,
either the `e.wybe` or `h.wybe` file could import both the `f.wybe` and
`i.wybe` files with the declaration:

```
use d.f, d.g.i
```

## Libraries

In addition to modules nested under a module's topmost ancestor module, modules
may import any modules in any of the Wybe library directories.  These are
configured when Wybe is installed, but can be overridden with the `--libdir` or
`-L` command line options, or by setting the `$WYBELIBS` shell variable.


## <a name="foreign-interface"></a>Low-level features (foreign interface)

### <a name="purity"></a>Purity

Wybe code is mostly purely logical, and the Wybe compiler takes advantage of
this.  For example, if none of the outputs of a proc call are actually used, 
the compiler will eliminate the call.
A proc call may also be omitted if a proc call with the same inputs has previously 
been made; in this case, the compiler will assume the output(s) will be identical.
The compiler may also reorder calls however it likes, as long as all the inputs 
to a proc are available when the proc is called.  As long as your code is purely 
logical, all of these optimisations and more are perfectly safe.

However, occasionally it is important that the compiler not perform such optimisations.
For example, the `exit` command has no outputs, it is only executed for its effect 
(terminating the program prematurely).  In some cases, purely logical Wybe procs 
can be written based on impure building blocks, particularly when interfacing to 
code written in conventional languages.

To support such cases, the Wybe compiler provides a *purity* system, 
allowing you to declare the purity of your procedures and functions, 
which tells the Wybe compiler (and other programmers) to treat them more carefully.

Wybe supports the following three levels of purity:

- *pure*  
the default purity level.  An ordinary procedure or function, calls to which 
are subject to all optimisations.

- *impure*  
an impure procedure, calls to which should not be reordered or omitted.
Impure procs must be declared to be so, and in general, a proc that calls an 
impure proc must itself be impure.  The bodies of impure procs are also not 
optimised as extensively as pure and semipure procs.  Even calls to pure procs 
appearing in the bodies of impure procs will not be optimised.  This provides 
a way to prevent unwanted optimisation in a fine-grained way, such as for the 
purposes of benchmarking.

- *semipure*  
a proc that is not pure, so calls to it must not be reordered or omitted, 
however its impurity is not "contagious".  It may be called from an ordinary, 
pure proc without that proc becoming impure.  It may also call impure procs.
Note that calls to pure procs in the bodies of semipure procs are optimised as usual;
it is only in the bodies of *impure* procs that calls to ordinary pure procs are 
not optimised.

In the absence of any declaration of impurity, your procedures and functions 
will be assumed to be pure.  An ordinary pure proc can call a semipure proc, 
but if it calls an impure proc, the compiler will report an error.  You can 
specify that your proc is pure despite calling impure procs by explicitly 
promising that it is pure.

Note that top-level code in any module is treated as semipure:  it may call 
impure procs, but calls to pure procs will be optimised as normal.

Purity is managed by including one of the following modifiers, between curly 
braces, in the proc declaration, between the `def` keyword and the procedure or 
function name:

- `pure`
explicitly promise that the proc is pure, despite calling impure procs.

- `semipure`
specify that the proc is effectively impure, meaning that calls to it are not 
subject to normal optimisations, but that its callers are not rendered impure by 
calling it.

- `impure`
the proc is impure, so calls to it are not subject to normal optimisations, and 
its callers should also be considered impure unless explicitly promised to be pure 
with a `pure` modifier.

Any call to an `impure` or `semipure` proc must be preceded with the `!` annotation, 
as if it were a call to a proc that used resources.  This reminds the reader that 
the call is not pure, and that they must be careful when reading or modifying the code.  
For example, to prematurely exit the program, you can insert the following proc call:

```
!exit(1)
```

If you wish to include other modifiers along with one of these, include them all 
between the braces, in any order, separated by commas.


### Inlining

The Wybe compiler optimises your code in some situations by replacing a proc call 
with its definition, while being careful not to change the meaning of the program.  
The compiler uses heuristics to determine when to do this, and for the most part 
it is not something you need to think about.  In general, the compiler will decide 
to inline small, non-recursive functions and procedures.

If you wish to have finer control, you can do this by placing one of these two 
modifiers between curly braces between `def` and the procedure or function name:

- `inline`
force inlining of calls to this proc

- `noinline`
prevent inlining of calls to this proc

If you wish to include other modifiers along with one of these, include them all 
between the braces, in any order, separated by commas.


### Foreign language interface

The foreign language interface allows Wybe to call functions written in other
languages.  In particular, Wybe is built on the LLVM infrastructure, so Wybe
allows LLVM instructions to be used as low level operations.  Wybe also permits
C code to be called.  It should be noted that the Wybe compiler does minimal
checking of arguments to these instructions, and cannot ensure that these
operations are pure, so it is quite possible to cause type errors or purity
errors through the foreign language interface.  Therefore, it is recommended to
define a Wybe procedure or function as an interface to each foreign operation to
be used, and to code that function paying close attention to argument types and
purity.  After that, the Wybe type and purity system will ensure the correctness
of calls to these interface functions or procedures.


#### Linking foreign code

A Wybe module my specify a dependency on a foreign object file using a variant
of the `use` declaration:

> `use foreign object` *filebasename*

where *filebasename* is the base name of the foreign file, omitting any file
extension.  This will ensure that when an executable is built, the specified
file will be linked in.

A dependency on a foreign library file may be specified with the following declaration:

> `use foreign library` *libarybasename*

where *librarybasename* is the base name of the foreign library, omitting any
file extension.  When an executable is built, the specified library will be
linked in with a `-l`*librarybasename* switch.


#### Calling foreign code

To call code written in other languages from Wybe, use the `foreign` construct.
This is a very low-level interface, and performs no sanity checking, 
so be careful to get the call right.

The form of a foreign call is:

> `foreign` *language* *function*(*arg*, *arg*, ...)

where *language* is the name of the foreign language the function is written in,
*function* is the name of the foreign function to call, and the *arg*s are the
arguments to be passed.  For functions written in C, *language* is `c`.

Note that, like other Wybe calls, foreign calls are assumed to be pure.  If your
foreign call is performing some kind of interaction with the outside world, it
should use the `io` resource, to ensure that the call is performed correctly.
This is actually quite simple:  the `io` state is simply eliminated by the
compiler when it is passed in a foreign call, so you can simply pass it into and
out of a foreign call, and it will vanish as the call happens, and reappear on
return from the call.  For example, the `print` proc for the `char` type in the
standard library is defined this way:

```
pub def print(x:char) use !io { foreign c putchar(x, !io) }
```

To improve the safety of the interface, it is recommended to define a separate
Wybe proc to make each foreign call, as shown above.  This will allow the Wybe
type checker to ensure the type safety of your calls, as long as your foreign
call is type correct.

Foreign calls may optionally specify *modifiers* to provide extra information 
useful to the Wybe compiler.  If modifiers are to be specified, they are written 
after the *language* name:

> `foreign` *language* `{`*modifiers*`}` *function*(*arg*, *arg*, ...)

where *modifiers* is a comma-separate sequence of identifiers specifying this
information.  Supported modifiers in foreign calls are:

- **impure**:  the call is [impure](#purity)
- **semipure**:   the call is [impure](#purity), but does not cause its
  caller to be impure
- **terminal**:  the call will not return
- **unique**:  do not report [uniqueness errors](#unique-types) arising from use
  of unique arguments to the call (but do note the use or definition of unique
  arguments)
- **test**:  the call is a [test](#tests); that is, it has one extra output argument,
  beyond those explicitly provided, which indicates whether the call succeeds.
  Where *language* is `llvm`, the output argument is a 1 bit integer; otherwise
  the output argument is an `int`, which indicates success for any value other
  than 0.

For example, the `exit` proc in the standard library is implemented as
follows:

```
pub def {terminal,semipure} exit(code:int) {
    foreign c {terminal,semipure} exit(code)
}
```
and the less than test for integers is defined as
```
pub def {test} (x:_ <  y:_) { foreign llvm {test} icmp_slt(x,y) }
```


#### Using LLVM instructions

The lowest-level interface, to raw LLVM instructions, takes the same form as
calls to foreign code, where the foreign *language* is `llvm`.  These have a
functional style, although you can use the procedural style if you prefer.  For
example, instead of

```
?x2 = foreign llvm add(x, 1)
```
you can write
```
foreign llvm add(x, 1, ?x2)
```

For more detail on the behaviour of these operations, please consult the
[LLVM documentation](https://llvm.org/docs/).


##### Integer operations

In the following, all inputs and outputs listed as `int` can in fact be any 
integer type:  signed or unsigned, and any number of bits of precision.  
However, all `int` inputs and outputs must be the same number of bits of precision.  
All `bool` outputs may be any 1-bit integer type.


- `foreign llvm add(`arg1:int, arg2:int`)`:int
Integer addition
- `foreign llvm sub(`arg1:int, arg2:int`)`:int
Integer subtraction
- `foreign llvm mul(`arg1:int, arg2:int`)`:int
Integer multiplication
- `foreign llvm udiv(`arg1:int, arg2:int`)`:int
unsigned integer division
- `foreign llvm sdiv(`arg1:int, arg2:int`)`:int
Signed integer division
- `foreign llvm urem(`arg1:int, arg2:int`)`:int
unsigned integer remainder
- `foreign llvm srem(`arg1:int, arg2:int`)`:int
Signed integer remainder
- `foreign llvm icmp_eq(`arg1:int, arg2:int`)`:bool
Integer equality
- `foreign llvm icmp_ne(`arg1:int, arg2:int`)`:bool
Integer disequality
- `foreign llvm icmp_ugt(`arg1:int, arg2:int`)`:bool
Integer unsigned strictly greater
- `foreign llvm icmp_uge(`arg1:int, arg2:int`)`:bool
Integer unsigned greater or equal
- `foreign llvm icmp_ult(`arg1:int, arg2:int`)`:bool
Integer unsigned strictly less
- `foreign llvm icmp_ule(`arg1:int, arg2:int`)`:bool
Integer unsigned less or equal
- `foreign llvm icmp_sgt(`arg1:int, arg2:int`)`:bool
Integer unsigned strictly greater
- `foreign llvm icmp_sge(`arg1:int, arg2:int`)`:bool
Integer signed greater or equal
- `foreign llvm icmp_slt(`arg1:int, arg2:int`)`:bool
Integer signed strictly less
- `foreign llvm icmp_sle(`arg1:int, arg2:int`)`:bool
Integer signed less or equal
- `foreign llvm shl(`arg1:int, arg2:int`)`:int
Left shift
- `foreign llvm lshr(`arg1:int, arg2:int`)`:int
Logical right shift (shift zeros in at right)
- `foreign llvm ashr(`arg1:int, arg2:int`)`:int
Arithmetic right shift (copy sign bit at right)
- `foreign llvm or(`arg1:int, arg2:int`)`:int
Bitwise or
- `foreign llvm and(`arg1:int, arg2:int`)`:int
Bitwise and
- `foreign llvm xor(`arg1:int, arg2:int`)`:int
Bitwise exclusive or

##### Floating point operations

Similar to above, all inputs and outputs listed as `float` can be any legal 
LLVM floating point type:  16, 32, 64, or 128 bits.  Again, in a single instruction, 
all the `float` inputs and outputs must be the same bit width.

- `foreign llvm fadd(`arg1:float, arg2:float`)`:float
Floating point addition
- `foreign llvm fsub(`arg1:float, arg2:float`)`:float
Floating point subtraction
- `foreign llvm fmul(`arg1:float, arg2:float`)`:float
Floating point multiplication
- `foreign llvm fdiv(`arg1:float, arg2:float`)`:float
Floating point division
- `foreign llvm frem(`arg1:float, arg2:float`)`:float
Floating point remainder
- `foreign llvm fcmp_eq(`arg1:float, arg2:float`)`:bool
Floating point equality
- `foreign llvm fcmp_ne(`arg1:float, arg2:float`)`:bool
Floating point disequality
- `foreign llvm fcmp_slt(`arg1:float, arg2:float`)`:bool
Floating point (signed) strictly less
- `foreign llvm fcmp_sle(`arg1:float, arg2:float`)`:bool
Floating point (signed) less or equal
- `foreign llvm fcmp_sgt(`arg1:float, arg2:float`)`:bool
Floating point (signed) strictly greater
- `foreign llvm fcmp_sge(`arg1:float, arg2:float`)`:bool
Floating point (signed) greater or equal

#####  <a name="conversion"></a>Integer/floating point conversion

These operations convert between floating point and integer representations.
They work for any bitwith float and integer types.

- `foreign llvm uitofp(`arg1:int`)`:float
Convert unsigned integer to float
- `foreign llvm sitofp(`arg1:int`)`:float
Convert signed integer to float
- `foreign llvm fptoui(`arg1:float`)`:int
Convert float to unsigned integer
- `foreign llvm fptosi(`arg1:float`)`:int
Convert float to signed integer


#### Foreign types

In addition to the [`constructor`](#constructor-declarations) declaration, it is
possible to declare a low-level type by specifying its representation.  This
declaration has the form:

> `representation is` *rep*

where *rep* has one of these forms:

- `address`
the type is a machine address, similar to the `void *` type in C.
- *n* `bit` *numbertype*
a primitive number type comprising *n* bits, where *n* is any non-negative
integer and *numbertype* is one of:
  - `signed`
  a signed integer type
  - `unsigned`
  an unsigned integer type
  - `float`
  a floating point number; *n* must be 16, 32, 64, or 128.

Like a `constructor` declaration, a `representation` declaration makes the
enclosing module into type.  Also like a `constructor` declaration, a submodule
declaration may be combined with the specification of a representation using the
form:

> `type` *type* `is` *rep* `{` *defs* `}`

where *rep* is as above, and *defs* specifies other members of the type.

Note that it is not permitted to specify both constructors and an explicit
representation for a type.

To make a representation type [unique](#unique-types), follow `is` with
`{unique}`.

#### Type casting
In some cases, foreign code may need to cast values of one Wybe type to another,
to satisfy both sides of an interface.  This follows a syntax similar to
applying [type constraints](#type-constraints), except that the variable is
separated from its type with a `:!`:

> *expr* `:!` *type*

This differs from an ordinary type constraint in that:

-  this may only be used in foreign calls;
-  it may only be applied to (input or output) variables; and
-  it specifies the type of the expression without requiring that the value
   produced by the expression should be the same; i.e., the type of the expression
   is *changed* to the specified type.

The final point is the key difference:  a *type constraint* specifies what
the type of the expression must be, while a *type cast* specifies that its type
should be converted from whatever it is to the specified type.  A type
constraint will cause a type error if the specified type is incompatible with
the type of the expression, while a type cast will silently convert the type.

The behaviour of a type cast is slightly different for input and output
arguments.  In both cases, a cast specifies the type of the argument to the
foreign instruction.  For an input argument, this means you are specifying the
type *to* which the argument should be converted; for an output argument you are
specifying the type *from* which the argument should be converted.  In most
cases, for output arguments, you will want to specify the type to convert *to*.
You can do this by combining a type constraint with a type cast by following the
output variable name with a type constraint (giving the type to convert *to*),
and following that with a type cast (giving the type to convert *from*).

It is also important to understand that type casts may extend or truncate the
value being passed by adding or removing most siginficant bits to the value, but
it will not change the bits of the value.  If you wish to convert between
floating point and integer representations, see the [integer/floating point
conversion](#conversion) instructions.

A type cast may be combined with a type constraint to specify both the type of 
the expression *and* the type of the value:

> *var* `:!` *type*`:`*type2*

This specifies that the type of the variable *var* is *type2*, but that the type 
of the whole *var* `:!` *type*`:`*type2* expression is *type*.


#### Wybe low-level memory management primitives

The LPVM instructions are low-level memory manipulation instructions.  Note
these are foreign instructions specifying the *language* `lpvm` (rather than
`llvm`).


- `foreign lpvm alloc(`*size:*`int`, `?`*struct:type*`)`
Allocate (at least) *size* bytes of memory and store the address in *struct*,
which has its specified type.

- `foreign lpvm access(`*struct:type*, *offset:*`int`, *size*:`int`,
                        *start_offset*:`int`, `?`*member:type2*`)`
Access the field of type *type2* at address *struct* + *offset*. The size of the
structure is *size* bytes. The intention of the *start_offset* is to handle
tagged pointers: a tagged pointer will appear to point *start_offset* bytes past
the start of the actual structure in memory; subtracting this will allow the
start of the structure to be found, so it can be copied.

- `foreign lpvm mutate(`*struct:type*, `?`*struct2:type*,
                        *offset:*`int`, *destructive*:`bool`,
                        *size*:`int`, *start_offset*:`int`, *member:type2*`)`
*struct2* is the same as *struct*, except that it has *member*, with type
*type2*, at *struct* + *offset*. The start of the structure is actually
*start_offset* bytes before *struct* in memory, and the size of the structure is
*size* bytes. The intention of the *start_offset* is to handle tagged pointers:
a tagged pointer will appear to point *start_offset* bytes past the start of the
actual structure in memory; subtracting this will allow the start of the
structure to be found, so it can be copied. If *destructive* is `true`, then
this instruction is permitted to perform the operation destructively, making
*struct2* the same address as *struct*.

- `foreign lpvm cast(`*var1:type1*, `?`*var2:type2*`)` Move *var1* to *var2*
converting its type from *type1* to *type2*, without changing the
representation. This just allows getting around LLVM strong typing; it does not
actually require any instructions.


#### Handling impurity

Impure operations, such as input/output operations, can present a challenge in
Wybe.  The Wybe compiler is entitled to, and does, eliminate operations that do
not produce needed values.  Likewise, it can and does reorder operations in
function and procedure definitions, as long as it ensures that the inputs to an
operation are all computed before executing that operation.  However, the
compiler respects (purity declarations)[#purity]:  if a procedure is declared
`impure` or `semipure`, calls to it will not be eliminated or reordered.

Additionally, the Wybe library defines a unique type `phantom`, whose
representation has zero bits.  The
compiler automatically removes any input or output arguments whose types have
zero bits when LLVM code is being generated, including calls to foreign code.
The type of the `io` resource is `phantom`, thus the `io` resource can be passed
into or out of any foreign call without anything actually being passed to the
foreign function or LLVM instruction.  Yet the phantom value is threaded through
the code, ensuring that the compiler respects the ordering of operations.

This gives two ways of managing impurity in Wybe:

 * An operation can `use` the `!io` resource or another resource or value of
   type `phantom`; or
 * It can be declared `impure` or `semipure`.

If impurity is managed through a `phantom` (or other zero-bit type) resource or
value, that resource or value will need to be threaded through the entire
application.  In most cases, this is the preferred approach:  it gives the
compiler more scope for optimisation, and provides documentation to the user of
how operations impact the state of the computation.

Managing impurity through the purity system allows low-level Wybe code to
circumvent the purity of the language, but then to present a pure interface to
that code.  For example, the `logging` library module allows the programmer to
insert "debugging printfs" into their code.  Such operations are not meant to be
used in a released application, but can be very useful for the programmer to
understand the behaviour of their code.
