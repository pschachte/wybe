class sequence(T) {

    pub syn expr ::= '[' ']'
    pub syn expr ::= '[' expr exprlist opttail ']'

    syn exprlist ::=
    syn exprlist ::= ',' expr exprlist

    syn opttail ::=
    syn opttail ::= '|' expr

    # Constructors (ranges are implicitly exclusive & exhaustive)
    pub abstract con []
    pub abstract con [ first:T | rest:sequence(T) ]

}
