pub class basicchar
    # specify representation as foreign type, without constructors
    foreign "char"

    pub class smallint
	foreign "unsigned char"

    pub smallint(ch):smallint = foreign \\ (unsigned char) ch \\
