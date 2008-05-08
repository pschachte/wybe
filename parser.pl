%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.9 2008/05/09 07:49:15 schachte Exp $
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
	(   compile_body(Body, Stream, Body1, Toks, Args),
	    concat_atoms(Toks, Functor),
	    Term =.. [Functor|Args],
	    record_production(Head, Stream, Term, Body1),
	    fail
	;   true
	).


%  compile_body(Rule, Stream, Body, Toks, Args)
%  Body is the code to parse input according to grammar rule Rule.

compile_body((B1|B2), Stream, Body, Toks, Args) :-
	!,
	( Body0 = B1 ; Body0 = B2 ),
	compile_body(Body0, Stream, Body, Toks, Args).
compile_body((B1,B2), Stream, Body, Toks, Args) :-
	!,
	compile_body(B1, Stream, Body1, Toks1, Args1),
	compile_body(B2, Stream, Body2, Toks2, Args2),
	conjoin(Body1, Body2, Body),
	append(Toks1, Toks2, Toks),
	append(Args1, Args2, Args).
compile_body('', _, true, [], []) :-
	!.
compile_body(Terminal, Stream, Goal, [Terminal], []) :-
	terminal_symbol(Terminal, Symbol),
	!,
	terminal_goal(Symbol, Stream, Goal).
compile_body(Nonterminal, Stream, Goal, [], [Arg]) :-
	nonterminal_goal(Nonterminal, Stream, Arg, Goal).


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


concat_atoms(Toks, Atom) :-
	concat_codes(Toks, Codes),
	atom_codes(Atom, Codes).

concat_codes([Tok|Toks], Cs) :-
	terminal_symbol(Tok, Sym),
	symbol_codes(Sym, Cs1),
	concat_codes1(Toks, Cs2),
	append(Cs1, Cs2, Cs).


concat_codes1([], []).
concat_codes1([Tok|Toks], Cs) :-
	terminal_symbol(Tok, Sym),
	symbol_codes(Sym, Cs1),
	append(Cs1, [0' |Cs2], Cs),
	concat_codes1(Toks, Cs2).

symbol_codes(string(Chars,_), Chars) :-
	!.
symbol_codes(Sym, Codes) :-
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


%  record_production(Nonterm, Stream, Term, Body)
%  Add a new production for Nonterm with body Body.  Tokens are to be read
%  from Stream, and the result of this grammar rule is Term.

record_production(Nonterm, Stream, Term, Body) :-
	left_unfold(Body, Nonterm, Body1),
	(   left_recursive_body(Body1, Nonterm, Body2)
	->  (	left_recursive_body(Body2, Nonterm, _)
	    ->	throw(double_left_recursive(Nonterm, Body))
	    ;	update_left_recursive(Nonterm),
		make_lrec_production(Nonterm, Stream, Term, Body2, Realbody)
	    )
	;   left_recursive_nonterm(Nonterm, Stream, Term, Tailcall)
	->  conjoin(Body2, Tailcall, Realbody)
	),
	(   initial_goal(Realbody, terminal(Stream,Sym), Rest)
	->  Head =.. [Nonterm, Sym, _Prec, Stream, Term],
	    add_grammar_clause(Head, Rest)
	;   throw(left_unfolding_failed(Nonterm, Body))
	).


initial_goal((A,B), A, B) :-
	!.
initial_goal(Init, Init, true).



left_unfold(Body0, Nonterm, Body) :-
	initial_goal(Body0, Lead, Rest),
	left_unfold1(Lead, Rest, Body0, Nonterm, Body).

left_unfold1(terminal(_,_), Body, _, _, Body).
left_unfold1(nonterminal(_,Nonterm,_,_), Rest, Body0, Parent, Body) :-
	(   Nonterm == Parent
	->  Body = Body0
	;   nonterm_clause(Nonterm, Body1),
	    conjoin(Body1, Rest, Body)
	).


left_recursive_body(Body, Nonterm, Rest) :-
	initial_goal(Body, nonterm(_,Nonterm,_,_), Rest).


left_recursive_nonterm(Nonterm, Stream, Term, Tailcall) :-
	left_recursive(Nonterm, Tailpred),
	Tailcall =.. [Tailpred, Stream, Term].

add_grammar_clause(Head, Body) :-
	Head =.. [Nonterm, Lead, Prec, Stream, Term],
	add_nonterm_master_clause(Nonterm),
	Pattern =.. [Nonterm, Lead, OldPrec, OldStream, Oldterm],
	(   retract((parser_rule:(Pattern:-_:Oldbody)))
	->  (	Newoldbody = Newbody
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


add_nonterm_master_clause(Nonterm) :-
	(   clause(parse_table(Nonterm,_,_,_,_),_)
	->  true
	;   Generalcall =.. [Nonterm, A, B, C, D],
	    assert(parse_table(Nonterm,A,B,C,D):-parser_rule:Generalcall)
	).


left_factor((Old1,Olds), New, Common, Newold, Newnew) :-
	!,
	initial_goal(New, New1, News),
	(   Old1 = New1
	->  left_factor(Olds, News, Commons, Newold, Newnew),
	    conjoin(Old1, Commons, Common)
	;   Common = true,
	    Newold = (Old1,Olds),
	    Newnew = New
	).
left_factor(Old, New, Common, Newold, Newnew) :-
	initial_goal(New, New1, News),
	(   Old = New1
	->  Newold = true,
	    Newnew = News,
	    Common = Old
	;   Common = true,
	    Newold = Old,
	    Newnew = New
	).
	

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
