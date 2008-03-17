%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.2 2008/03/17 13:07:28 schachte Exp $
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

:- module(parser, [
		   get_item/2
		   add_production/2
   ]).


:- use_module(lex).


% Read a top-level item (declaration or directive) from the specified stream.

get_item(Stream, Item) :-
	get_token(Stream, Token, _),
	parser_rule:item(Token, 1, Stream, Item).


%  Everything in the parser_rule module is dynamic; this one is mentioned here.
:- dynamic parser_rule:item/4.


%  We keep track of nonterminals used but undefined, for error reporting.
:- dynamic undef_nonterm/1.
undef_nonterm(item).


%  add_production(Nonterm, Body)
%  Add new grammar rule Nonterm ::= Body to grammar.  This produces a
%  deterministic LL(1) parser.  The code automatically left-factors the
%  grammar, and eliminates left recursion.
%
%  The generated parser consists of dynamic predicates of the form:
%

item('use', _Prec, Stream, Term) :-
	get_token(Stream, Token),
	use_decl(Token, 1, Stream, Term).
item('module', _Prec, Stream, Term) :-
	get_token(Stream, Token),
	module_decl(Token, 1, Stream, Term).
item('class', _Prec, Stream, Term) :-
	get_token(Stream, Token),
	class_decl(Token, 1, Stream, Term).
	


add_production(Nonterm, Body) :-
	add_production1(Body, Nonterm).

add_production1((B1;B2), Nonterm) :-
	!,
	add_production1(B1, Nonterm),
	add_production1(B2, Nonterm).
add_production1(Body, Nonterm) :-
	left_recursion(Nonterm, Leftrec),
	transform(Body, Nonterm, Leftrec, Clauses, Leftrec1),
	maybe_add_left_recursion(Leftrec1, Leftrec, Nonterm),
	add_clauses(Clauses, Nonterm, Leftrec1).


left_recursion(Nonterm, Leftrec) :-
	(   is_left_recursive(Nonterm)
	->  Leftrec = true
	;   Leftrec = false
	).


:- dynamic is_left_recursive/1.


transform((L,R), Nonterm, Tail, Leftrec0, Clauses, Leftrec) :-
	!,
	transform_tail(R, Tail1, Tail),
	transform(L, Nonterm, Tail1, Leftrec0, Clauses, Leftrec).
transform(Token, Nonterm, Tail, Leftrec0, [Clause], Leftrec0) :-
	token(Token),
	!,
	Head =.. [Nonterm,Token,Prec,Stream,Term],
	generate_clause(Nonterm, Token, Tail, Leftrec0, Clause).
transform(Nonterm1, Nonterm, Tail, Leftrec0, Clauses, Leftrec) :-
	(   recursive_invocation(Nonterm, Nonterm1)
	->  Leftrec = true
	;   Leftrec = Leftrec0
	),
	


recursive_invocation(Parent, Parent) :-
	!.
recursive_invocation(Parent, Child) :-
	leftmost_nonterm(Child, Parent).
