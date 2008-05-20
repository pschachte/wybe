# frege integer type

class int
    # says this is just a single word with no constructor
    rep word

    pub syn expr ::= number

    # Define a number token
    pub lex number ::= '0x' radixnum(16)
    pub lex number ::= '0' radixnum(8)
    # This one's difficult, as we use the first part of the number as an
    # argument to parse the second 
    pub lex number ::= radix = radixnum(10) 'r' radixnum(radix)
    pub lex number ::= radixnum(10)

    # the function after the lexeme name is called with both nonterminal
    # parts as arguments to construct the lexeme value
    # grammar rule is left recursive, as that gets left-associative
    # construction; will be translated to right recursion
    lex radixnum(r) makeradixnum(r) ::= 
    	radixnum(r) radixchar(r)
    lex radixnum(r) makeradixnum(r,0) ::= radixchar(r)

    fun makeradixnum(radix, num, ch:char) = num * radix + 
    	    if ('0' <= ch & ch <= '9') then ch - '0'
	    elif ('a' <= ch & ch <= 'a'+radix-9) then ch - 'a' + 10
	    elif ('A' <= ch & ch <= 'A'+radix-9) then ch - 'A' + 10

    lex radixchar(r) check radixdigitcheck(r) ::= digit
    lex radixchar(r) check radixalphacheck(r) ::= alpha

    fun radixdigitcheck(radix, digit:char) = digit <= '0' + radix

    fun radixalphacheck(radix, digit:char) = 
    	digit >= 'a' & digit <= 'a' + radix |
    	digit >= 'A' & digit <= 'A' + radix

    # these should be in a common char.frg library
    public lex digit ::= '0' - '9'

    public lex alpha ::= 'a' - 'z'
    public lex alpha ::= 'A' - 'Z'

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


    pub syn expr ::= expr + expr

    pub x::in + y::n = foreign(c, \\ x + y \\)
    pub foreign(c, \\ z - y \\) + y::in = z::in
    pub x::in + foreign(c, \\ z - x \\) = z::in


    pub syn expr ::= expr - expr

    pub x::in - y::n = foreign(c, \\ x - y \\)
    pub foreign(c, \\ z + y \\) - y::in = z::in
    pub x::in - foreign(c, \\ z + x \\) = z::in


    pub syn expr ::= expr * expr

    pub x::in * y::n = foreign(c, \\ x * y \\)
    pub foreign(c, \\ z / y \\) * y::in = z::in
    pub x::in * foreign(c, \\ z / x \\) = z::in


    pub syn expr ::= expr / expr

    pub x::in / y::n = foreign(c, \\ x / y \\)
    pub foreign(c, \\ z * y \\) / y::in = z::in
    pub x::in / foreign(c, \\ z * x \\) = z::in


    pub syn expr ::= expr % expr

    pub x::in % y::n = foreign(c, \\ x % y \\)
