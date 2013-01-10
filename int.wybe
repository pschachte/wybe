# frege integer type

class int
    # says this is just a single word with no constructor
    foreign c "int"

    # Allow integers to be used as manifest constants for expressions
    pub syn expr ::= integer

    # Define a number token
    pub lex integer ::= decimalnum
    # pub lex number ::= '0x' hexnum
    # pub lex number ::= '0' octalnum

    # the function after the lexeme name is called with both nonterminal
    # parts as arguments to construct the lexeme value
    # grammar rule is left recursive, as that gets left-associative
    # construction; will be translated to right recursion

    lex decimalnum ::= makedecimalnum: decimalnum digit
    lex decimalnum ::= decimaldigit:   digit

    fun decimaldigit(ch:char) = foreign c \\ ch - '0' \\
    fun makedecimalnum(num, ch:char) = 
    	foreign c \\ num * 10 + (ch - '0') \\

    # This overrides an inherited version; inherited to_string calls it
    pub repr(i):string =
	s = ""
	if i < 0 then
	    s = "-" 
	    i = -i
	do  s = ('0' + i%10) ++ s
	    i /= 10
	while i > 0
	s


    pub syn expr ::= expr '+' expr

    pub x::in + y::n = foreign(c, \\ x + y \\)
    pub foreign(c, \\ z - y \\) + y::in = z::in
    pub x::in + foreign(c, \\ z - x \\) = z::in


    pub syn expr ::= expr '-' expr

    pub x::in - y::n = foreign(c, \\ x - y \\)
    pub foreign(c, \\ z + y \\) - y::in = z::in
    pub x::in - foreign(c, \\ z + x \\) = z::in


    pub syn expr ::= expr '*' expr

    pub x::in * y::n = foreign(c, \\ x * y \\)
    pub foreign(c, \\ z / y \\) * y::in = z::in
    pub x::in * foreign(c, \\ z / x \\) = z::in


    pub syn expr ::= expr '/' expr

    pub x::in / y::n = foreign(c, \\ x / y \\)
    pub foreign(c, \\ z * y \\) / y::in = z::in
    pub x::in / foreign(c, \\ z * x \\) = z::in


    pub syn expr ::= expr '%' expr

    pub x::in % y::n = foreign(c, \\ x % y \\)
