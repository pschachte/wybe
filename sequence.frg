class sequence(t) {

    # Define as algebraic type
abstract:
	empty | sequence(first:t, rest:@) ;

    # Give custom syntax
syntax:
    extend expr(empty) ::= [] ;
    extend expr(sequence(f,r)) ::= '[', expr(s), seq_tail(r), ']' ;
    
    seq_tail(empty) ::= '' ;
    seq_tail(sequence(f,r)) ::= ',', expr(f), seq_tail(r) ;

}
