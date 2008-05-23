pub class basicchar
    # specify representation as foreign type, without constructors
    foreign c "char"

    pub lex digit ::= '0' - '9'

    pub lex alpha ::= 'a' - 'z' | 'A' - 'Z'
