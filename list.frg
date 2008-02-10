# frege linked list class

class list(T) implements sequence(T)

    # Constructors (implicitly exclusive & exhaustive)
    pub con []
    pub con [ head:T | tail ]

    # Other public methods

    # Special syntax
    pub syn 400 in(element, list) ::= element:399 'in' list:399

    pub e:T in l =
	e = l.head or e in l.tail

    pub length(l):int =
	count _ in l
	      	
    pub syn 380 ++(l1, l2) ::= l1:379 '++' l2:380

    pub []    ++ l = l
	[h|t] ++ l = [h|t++l]

    pub reverse []    = []
	reverse [h|t] = (reverse t) ++ [h]

end
