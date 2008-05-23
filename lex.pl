%  File     : lex.pl
%  RCS      : $Id: lex.pl,v 1.7 2008/05/24 09:00:21 schachte Exp $
%  Author   : Peter Schachte
%  Origin   : Mon Apr  9 14:16:33 2007
%  Purpose  : Lexical analysis for frege
%  Copyright: © 2007 Peter Schachte.  All rights reserved.
%


:- module(lex, [
	        get_token/3,
		bracket/3
   ]).


%  get_token(Stream, Token, Pos)
%  Token is the next Frege token to be read from Stream, and it appears at
%  file position Pos.  Pos is a Prolog stream position term.  Token is one of
%  the following:
%	bracket(Shape,End)	where Shape in {round,square,curly} and
%				End in {open,close}
%	string(Chars,Kind)	where Kind in {single,double,back,here}
%				and Chars is a list of character codes
%	symbol(Atom)		where Atom is a Prolog atom
%	punct(Atom)		where Atom is a Prolog atom

get_token(Stream, Token, Pos) :-
	stream_property(Stream, position(Pos0)),
	get_code(Stream, Char),
	lex_token(Char, Stream, Pos0, Token, Pos).


lex_token(-1, _, _, _, _) :- !, fail.			% fail at eof
lex_token(0'#, Stream, _, Token, Pos) :-
	!,
	get_code(Stream, Char1),
	skip_line(Char1, Stream),
	stream_property(Stream, position(Pos0)),
	get_code(Stream, Char2),
	lex_token(Char2, Stream, Pos0, Token, Pos).
lex_token(0'(, _, Pos, bracket(round,open), Pos) :-
	!.
lex_token(0'), _, Pos, bracket(round,close), Pos) :-
	!.
lex_token(0'[, _, Pos, bracket(square,open), Pos) :-
	!.
lex_token(0'], _, Pos, bracket(square,close), Pos) :-
	!.
lex_token(0'{, _, Pos, bracket(curly,open), Pos) :-
	!.
lex_token(0'}, _, Pos, bracket(curly,close), Pos) :-
	!.
lex_token(0'', Stream, Pos, string(Chars,single), Pos) :-
	!,
	get_code(Stream, Char1),
	read_string(Char1, Stream, Chars, 0'').
lex_token(0'", Stream, Pos, string(Chars,double), Pos) :-
	!,
	get_code(Stream, Char1),
	read_string(Char1, Stream, Chars, 0'").
lex_token(0'`, Stream, Pos, string(Chars,back), Pos) :-
	!,
	get_code(Stream, Char1),
	read_string(Char1, Stream, Chars, 0'`).
lex_token(0'\\, Stream, Pos, string(Chars,here), Pos) :-
	!,
	get_code(Stream, Char1),
	read_terminator(Char1, Stream, Term0),
	Term = [0'\\|Term0],
	read_here_string(Term, Stream, Chars, Seen, Seen, Term).
lex_token(Char0, Stream, _, Token, Pos) :-
	Char0 =< 0' ,			% must be a whitespace character
	!,
	stream_property(Stream, position(Pos0)),
	get_code(Stream, Char1),
	lex_token(Char1, Stream, Pos0, Token, Pos).
lex_token(Char0, Stream, Pos, Token, Pos) :-
	symbol_char(Char0),
	!,
	Token = symbol(Atom),
	symbol_chars(Stream, Chars),
	atom_codes(Atom, [Char0|Chars]).
lex_token(Char0, Stream, Pos, punct(Atom), Pos) :-
	nonsymbol_chars(Stream, Chars),
	atom_codes(Atom, [Char0|Chars]).


skip_line(0'\n, _) :- !.
skip_line(_, Stream) :-
	get_code(Stream, Char),
	skip_line(Char, Stream).


read_string(Char, Stream, Chars, Term) :-
	(   Char =:= Term
	->  Chars = []
	;   Char =:= 0'\\
	->  get_code(Stream, Escaped),
	    char_escape(Escaped, Stream, Chars, Chars1, Char1),
	    read_string(Char1, Stream, Chars1, Term)
	;   Chars = [Char|Chars1],
	    get_code(Stream, Char1),
	    read_string(Char1, Stream, Chars1, Term)
	).


char_escape(Char, Stream, Chars, Chars0, Char1) :-
	(   one_char_escape(Char, Esc)
	->  Chars = [Esc|Chars0],
	    get_code(Stream, Char1)
	;   special_char_escape(Char, Stream, Chars, Chars0, Char1)
	->  true
	;   Chars = [Char|Chars0],
	    get_code(Stream, Char1)
	).


one_char_escape(0't, 0'\t).
one_char_escape(0'v, 0'\v).
one_char_escape(0'n, 0'\n).
one_char_escape(0'r, 0'\r).
one_char_escape(0'f, 0'\f).
one_char_escape(0'b, 0'\b).
one_char_escape(0'0, 0'\0).
% XXX Possibly handle alphanumeric escapes by translation to evaluation of
% XXX special variable, eg 'escape_t' for \t?  Then substitution of pattern
% XXX replacement could be handled by binding escape_1, etc.  But then how
% XXX to handle regexps?


% backslash at end of line in a string ignores newline and all following
% whitespace characters, so you can layout strings as you like.
special_char_escape(0'\n, Stream, Chars, Chars, Char1) :-
	get_code(Stream, Char),
	skip_white(Char, Stream, Char1).
% XXX Also define an escape like \( ... ) to evaluate enclosed expr.
% XXX This could handle formatted output pretty well.


skip_white(Char, Stream, Char1) :-
	(   Char > 0' % space character
	->  Char1 = Char
	;   Char < 0
	->  Char1 = Char
	;   get_code(Stream, Char2),
	    skip_white(Char2, Stream, Char1)
	).


read_terminator(0'\\, _, Term) :-
	!,
	Term = [0'\\].
read_terminator(Char, Stream, [Char|Term]) :-
	get_code(Stream, Char1),
	read_terminator(Char1, Stream, Term).


%  read_here_string(Term, Stream, Chars, Seen, Seen0, Wholeterm)
%  Chars is a list of characters up to the first occurrence of Wholeterm.
%  Term is the remainder of Wholeterm yet to be seen.  Seen is a list of
%  the characters from Wholeterm already seen, followed by Seen0.

read_here_string([], _, [], _, _, _).
read_here_string([Char0|Term], Stream, Chars, Seen, Seen0, Wholeterm) :-
	get_code(Stream, Char),
	(   Char =:= Char0
	->  Seen0 = [Char|Seen1],
	    read_here_string(Term, Stream, Chars, Seen, Seen1, Wholeterm)
	;   Chars = Seen,
	    Seen0 = [Char|Chars1],
	    read_here_string(Wholeterm, Stream, Chars1, Sn, Sn, Wholeterm)
	).


symbol_char(Char) :-
	(   Char >= 0'a, Char =< 0'z
	->  true
	;   Char >= 0'A, Char =< 0'Z
	->  true
	;   Char >= 0'0, Char =< 0'9
	->  true
	;   Char =:= 0'_
	).


punctuation_char(Char) :-
	Char > 0' ,
	\+ special_char(Char),
	\+ symbol_char(Char).


symbol_chars(Stream, Chars) :-
	peek_code(Stream, Char),
	(   symbol_char(Char)
	->  Chars = [Char| Chars1],
	    get_code(Stream, _),
	    symbol_chars(Stream, Chars1)
	;   Chars = []
	).


nonsymbol_chars(Stream, Chars) :-
	peek_code(Stream, Char),
	(   punctuation_char(Char)
	->  Chars = [Char| Chars1],
	    get_code(Stream, _),
	    nonsymbol_chars(Stream, Chars1)
	;   Chars = []
	).


bracket(square,  open, '[').
bracket(square, close, ']').
bracket(round,  open, '(').
bracket(round, close, ')').
bracket(curly,  open, '{').
bracket(curly, close, '}').
       


special_char(0'().
special_char(0')).
special_char(0'[).
special_char(0']).
special_char(0'{).
special_char(0'}).
special_char(0'').
special_char(0'"). %"
special_char(0'`).
special_char(0'#).
