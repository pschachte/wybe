# frege integer type

class int
    rep bits(28)

    syn number to_int(num,radix) ::=
    	symbol
	(	num = x & radix = 10
	orelse	'r' & symbol(num) ; radix = x
	)


# 5   1   2
# 512 12  2

# can we make the compiler smart enough to compile the reverse mode?

    pub from_string(str:string)
    	prefer str[0] != '0'	# this makes inverse of to_int deterministic
	factor = 1
	value = 0
	for c in reverse(str)
    	    '0' <= c & c <= '9'
	    value += factor * (code(c) - code(0))
	    factor *= 10

