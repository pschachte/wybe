# frege integer type
class int
representation:
    primitive bits(28)

syntax:
    expr(to_int(num,radix):@) ::= 
    	symbol(x)
	(	num = x ; radix = 10
	orelse	'r' ; symbol(num) ; radix = x
	)


# 5   1   2
# 512 12  2

# can we make the compiler smart enough to compile the reverse mode?

def to_int(chars)
    prefer chars[0] != '0'	# this makes inverse of to_int deterministic
    factor = 1
    value = 0
    for c in reverse(chars)
    	'0' <= c ; c <= '9'
	value += factor * (code(c) - code(0))
	factor *= 10
    end
end

% divmod(Coefficient, Modulus, Residue, Number)
% Coefficient * Modulus + Residue = Number, and 0 <= Coefficient < Modulus


%  polynomial(X, Coefficients) = Value
%  Value = sum(0 <= i < length(Coefficients), Coefficients[-1-i]*X**i)
%  It is difficult to make this reversible, because when Coefficients are
%  supplied, we want to allow it to have leading 0s, but when generating
%  coefficients, we don't want to generate leading 0s.  I believe the answer
%  is a combination of a way to specify preferences where there is
%  nondeterminism, and a way to discard unneeded alternative solutions.

base_encoding(Base, [C|Cs]) = 
	

divmod(C, M, R, N)
