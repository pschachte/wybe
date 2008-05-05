%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.7 2008/05/05 14:22:38 schachte Exp $
%  Author   : Peter Schachte
%  Origin   : Thu Mar 13 16:08:59 2008
%  Purpose  : Parser for Frege
%  Copyright: © 2008 Peter Schachte.  All rights reserved.
%
%  This module returns abstract syntax trees (ASTs, or parse trees) as terms
%  of the form:
%
%	node(Nonterm, Alternative, Children, Position)
%
%  where Nonterm is the nonterminal of this AST node label (what kind of node
%  it is), Alternative is a number that uniquely identifies this rule,
%  Children is a list of child nodes, and Position is an opaque term holding
%  stream position of the start of the node.  Terminal nodes are represented
%  as one of the token term types defined in lex.pl.
%
%  This parser generator is incremental, since new grammar rules can be
%  defined at any time.  Each time a grammar rule is added, all the tables
%  are updated accordingly.
%
%  The generated parser consists of dynamic predicates of the form:
%
%	 item('use', _Prec, Stream, Term) :-
%	 	get_token(Stream, Token),
%	 	use_decl(Token, 1, Stream, Term).
%	 item('module', _Prec, Stream, Term) :-
%	 	get_token(Stream, Token),
%	 	module_decl(Token, 1, Stream, Term).
%	 item('class', _Prec, Stream, Term) :-
%	 	get_token(Stream, Token),
%	 	class_decl(Token, 1, Stream, Term).
%
%  The first argument of each clause head is a distinct token, so indexing
%  makes the code deterministic.  To ensure this is possible, three
%  transformations, left recursion elimination, left unfolding, and left
%  factoring, are applied.  Grammars that cannot be made deterministic by
%  repeated application of these transformations are rejected.
%
%
%  Left Recursion Elimination
%
%  Left recursion elimination converts direct left recursion into right
%  recursion.  For example, a grammar defined like:
%
%    a ::= a 'x' b
%    a ::= a 'y' c
%    a ::= 'd'
%    a ::= 'e'
%
%  is automatically transformed into:
%
%    a ::= 'd' a_tail
%    a ::= 'e' a_tail
%    a_tail ::= 'x' b
%    a_tail ::= 'y' c
%
%
%  Left Unfolding
%
%  Each final grammar rule must begin by consuming a terminal; left unfolding
%  replaces a leftmost nonterminal with the body of each rule for that
%  nonterminal.  For example, a grammar defined like:
%
%    a ::= b c
%    a ::= d e
%    b ::= 'x' f
%    b ::= 'y' g
%    d ::= h i j
%    d ::=
%
%  is automatically transformed into:
%
%    a ::= 'x' f c
%    a ::= 'y' g c
%    a ::= h i j e
%    a ::= e
%    b ::= 'x' f
%    b ::= 'y' g
%    d ::= h i j
%    d ::=
%
%  This expansion is repeated until the leftmost item in the body of each
%  grammar rule is a terminal.
%
%
%  Left Factoring
%
%  Each resulting grammar rule must begin by consuming a distinct token;
%  where multiple rules for the same nonterminal begin with the same token,
%  they are combined into a single rule beginning with the initial common
%  part, and following with a new nonterminal defined as the final, different
%  parts of the rules.  For example, a grammar defined like: 
%
%    a ::= 'x' a b c
%    a ::= 'x' a d e
%    a ::= 'y' f
%
%  is automatically transformed into:
%
%    a ::= 'x' a a_tail
%    a ::= 'y' f
%    a_tail ::= b c
%    a_tail ::= d e
%
%  (and then left unfolding is applied to a_tail).
%
%
%  Final Nullable Nonterminals
%
%  Nullable nonterminals (those that can generate the empty string) must be
%  handled specially, since parsing a nullable nonterminal may not consume
%  any tokens.  So they must return the next terminal following the parsed
%  nonterminal.  If a nullable nonterminal is last in a production, then
%  parsing the nonterminal of that production must also return the following
%  nonterminal.  Thus we call any nonterminal "final nullable" if it has any
%  production ending a nullable or final nullable nonterminal.  We must
%  generate slightly different code to handle final nullable nonterminals to
%  take account of the returned terminal.
%
%
%  Incremental generation
%
%  As each new production is added, we left unfold each production until its
%  leftmost element is either nonexistent, a terminal, or the nonterminal
%  this rule defines.  If it is nonexistent and this nonterminal is not
%  already marked final nullable, we so mark it and reprocess all callers.
%  If it is now left-recursive, or if the nonterminal is already marked as
%  left-recursive, then first, if the nonterminal was not already marked
%  left-recursive, then we so mark it and re-process all existing productions
%  for that nonterminal for left recursion, and second we process the new
%  production for left recursion.  After all this, if the leftmost element is
%  identical to the leftmost element of another production for this
%  nonterminal, then we left factor it.  Finally we record all the
%  nonterminals called by the production, so that we can quickly find the
%  callers of any nonterminal.

:- module(parser, [
		   get_item/2,
		   add_production/2
   ]).


:- use_module(lex).
:- use_module(library(gensym)).


% Read a top-level item (declaration or directive) from the specified stream.

get_item(Stream, Item) :-
	get_token(Stream, Token, _),
	parser_rule:item(Token, 1, Stream, Item).


%  Entry into the dynamic part of the parser.
:- dynamic parse_table/5.


%  Everything in the parser_rule module is dynamic; this one is mentioned here.
:- dynamic parser_rule:item/4.


%  We keep track of nonterminals used but undefined, for error reporting.
:- dynamic undef_nonterm/1.
undef_nonterm(item).

%  Keep track of which nonterminals are left recursive and what their tail
%  predicates are
:- dynamic left_recursive/2.

%  We keep track of final nullable nonterminals.
:- dynamic final_nullable/1.

%  We keep track of which nonterminals use which.
:- dynamic used_by/2.


%  add_production(Nonterm, Body)
%  Add new grammar rule Nonterm ::= Body to grammar.  This produces a
%  deterministic LL(1) parser.  The code automatically incrementally performs
%  the above-described transformations to create a deterministic parser, if
%  possible.  Does not warn if the grammar is il-formed, since productions
%  added later may correct the problem.  Errors are reported when they are
%  discovered during parsing.


add_production(Head, Body) :-
	(   compile_body(Body, Head, Stream, true, true, Lead, Lrec, Nable,
			 Body1, Terms, Args),
	    concat_atoms(Terms, Functor),
	    record_production(Head, Lead, Stream, Functor, Args, Lrec, Nable,
			      Body1),
	    fail
	;   true
	).


%  compile_body(Rule, Head, Stream, Lmost, Rmost,
%		Lead, Lrec, Nable, Body, Terms, Args)
%  Body is the code to parse input according to grammar rule Rule, a rule for
%  nonterminal Head.  Lmost and Rmost are true iff Rule is the leftmost
%  and/or rightmost part of the input rule.  Lead is the initial terminal
%  that must be matched for this rule to match.  Lrec is true iff Rule is
%  left-recursive, in which case Body omits the left-recursive nonterminal.
%  Nable is true iff Rule is final nullable.

compile_body((B1|B2), Head, Stream, Lmost, Rmost, Lead, Lrec, Nable, Body, Terms, Args) :-
	!,
	( Body0 = B1 ; Body0 = B2 ),
	compile_body(Body0, Head, Stream, Lmost, Rmost, Lead, Lrec, Nable, Body, Terms, Args).
compile_body((B1,B2), Head, Stream, Lmost, Rmost, Lead, Lrec, Nable, Body, Terms, Args) :-
	!,
	compile_body(B1, Head, Stream, Lmost, false, Lead, Lrec, _, Body1,
		     Terms1, Args1),
	compile_body(B2, Head, Stream, false, Rmost, _, _, Nable, Body2,
		     Terms2, Args2),
	conjoin(Body1, Body2, Body),
	append(Terms1, Terms2, Terms),
	append(Args1, Args2, Args).
compile_body('', _, _, _, _, '', false, true, true, [], []) :-
	!.
compile_body(Terminal, _, Stream, Lmost, _, Symbol, false, false, Goal,
	     [Terminal], []) :-
	terminal_symbol(Terminal, Symbol),
	!,
	(   Lmost == true
	->  Goal = true
	;   terminal_goal(Symbol, Stream, Goal)
	).
compile_body(Nonterminal, Head, Stream, Lmost, Rmost, Lead, Lrec, Nable,
	     Goal, [], [Arg]) :-
	(   Lmost == true			% the left-most element
	->  (	Nonterminal == Head		% directly recursive
	    ->	Lrec = true,
		Goal = true
	    ;	Lrec = false,			% expand left nonterminal
		recorded_production(Nonterminal, Lead, Goal)
	    )
	;   nonterminal_goal(Nonterminal, Stream, Arg, Goal)
	),
	(   Rmost = true,
	    final_nullable(Nonterminal)
	->  Nable = true
	;   Nable = false
	).


is_terminal(bracket(_,_)).
is_terminal(string(_,_)).
is_terminal(symbol(_)).
is_terminal(punct(_)).


nonterminal_goal(Nonterm, Stream, Term, nonterminal(Stream,Nonterm,1,Term)).

terminal_goal(Symbol, Stream, terminal(Stream,Symbol)).
	

terminal_symbol(symbol(Sym), Sym).
terminal_symbol(punct(Sym), Sym).
terminal_symbol(bracket(Kind,End), Sym) :-
	bracket(Kind, End, Sym).
terminal_symbol(string(Chars,Kind), string(Chars,Kind)).


concat_atoms(Atoms, Atom) :-
	concat_codes(Atoms, Codes),
	atom_codes(Atom, Codes).

concat_codes([], []).
concat_codes([Atom|Atoms], Cs) :-
	token_codes(Atom, Cs1),
	append(Cs1, Cs2, Cs),
	concat_codes(Atoms, Cs2).

token_codes(symbol(Atom), Codes) :-
	!,
	atom_codes(Atom, Codes).
token_codes(punct(Atom), Codes) :-
	!,
	atom_codes(Atom, Codes).
token_codes(bracket(Shape,End), Codes) :-
	bracket(Shape,End,Sym),
	!,
	atom_codes(Sym, Codes).


conjoin((A,B), C, Conj) :-
	!,
	conjoin(B, C, Conj1),
	conjoin(A, Conj1, Conj).
conjoin(true, A, A) :-
	!.
conjoin(A, B, Conj) :-
	(   B == true
	->  Conj = A
	;   Conj = (A,B)
	).


record_production(Nonterm, Lead, Stream, Functor, Args, _Lrec, _Nable, Body) :-
	Head =.. [Nonterm, Lead, Prec, Stream, Term],
	Term =.. [Functor|Args],
	(   clause(parse_table(Nonterm,_,_,_,_),_)
	->  true
	;   Generalcall =.. [Nonterm, A, B, C, D],
	    assert(parse_table(Nonterm,A,B,C,D):-parser_rule:Generalcall)
	),
	Pattern =.. [Nonterm, Lead, Prec, Stream, Oldterm],
	(   retract((parser_rule:(Pattern:-_:Oldbody)))
	->  left_factor(Oldbody, Body, Commonbody, Newoldbody, Newbody),
	    (	Newoldbody = Newbody
	    ->	assert(parser_rule:Pattern:-Oldbody),
		throw(redundant_rule(Nonterm,Lead,Body))
	    ;	gensym('rule ', Newname),
		Newhead =.. [Newname, Lead, Prec, Stream, Generalterm],
		conjoin(Commonbody, Newhead, Factoredbody),
		assert(parser_rule:Pattern:-Factoredbody),
		assert((parser_rule:Newhead:-Newoldbody))
	    )
	;   Newhead = Head,
	    Newbody = Body
	),
	assert((parser_rule:Newhead:-Newbody)).


left_factor((Old1,Olds), New, Common, Newold, Newnew) :-
	!,
	split_conj(New, New1, News),
	(   Old1 = New1
	->  left_factor(Olds, News, Commons, Newold, Newnew),
	    conjoin(Old1, Commons, Common)
	;   Common = true,
	    Newold = (Old1,Olds),
	    Newnew = New
	).
left_factor(Old, New, Common, Newold, Newnew) :-
	split_conj(New, New1, News),
	(   Old = New1
	->  Newold = true,
	    Newnew = News,
	    Common = Old
	;   Common = true,
	    Newold = Old,
	    Newnew = New
	).
	

split_conj((New1,News), New1, News) :-
	!.
split_conj(New1, New1, true).



terminal(Stream, Expected) :-
	get_token(Stream, Token, Position),
	terminal_symbol(Token, Found),
	(   Expected = Found
	->  true
	;   throw(terminal_error(Expected, Found, Position))
	).

nonterminal(Stream, Nonterm, Prec, Value) :-
	get_token(Stream, Token, Position),
	terminal_symbol(Token, Symbol),
	(   parse_table(Nonterm, Symbol, Stream, Prec, Value)
	->  true
	;   throw(nonterminal_error(Nonterm, Symbol, Position))
	).
