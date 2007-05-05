# frege integer type
class int
representation:
    primitive bits(28);

syntax:
    expr(I:@) ::= symbol(S) where
		    to_int(S) = I ;

    to_int(chars) = value where
		    prefer chars[0] != '0',
		    for c in chars as 
		        factor from 1 by (10*) as
		        value from 0 by (+ factor * digitval)
		    do {
			    digitval = code(c) - code(0),
			    0 <= digitval < 10
		    } ;

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
