# frege linked list class

use sequence	# do we need this, since we say 'implements seq...' below

class list(T) implements sequence(T)

    # Constructors (ranges are implicitly exclusive & exhaustive)
    pub con []
    pub con [ head:T | tail ]

    # Other public methods

    # Special syntax
    pub syn expr ::= expr 'in' expr

    pub e:T in l =
	e = l.first or e in l.rest

    pub length(l):int =
	count _ in l
	      	
    pub syn expr ::= expr '++' expr

    pub []    ++ l = l
	[h|t] ++ l = [h|t++l]

    pub reverse []    = []
	reverse [h|t] = (reverse t) ++ [h]

end
