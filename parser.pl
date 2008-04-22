%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.5 2008/04/23 07:30:54 schachte Exp $
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
		   get_item/2
		   add_production/2
   ]).


:- use_module(lex).
:- use_module(library(gensym)).


% Read a top-level item (declaration or directive) from the specified stream.

get_item(Stream, Item) :-
	get_token(Stream, Token, _),
	parser_rule:item(Token, 1, Stream, Item).


%  Everything in the parser_rule module is dynamic; this one is mentioned here.
:- dynamic parser_rule:item/4.


%  We keep track of nonterminals used but undefined, for error reporting.
:- dynamic undef_nonterm/1.
undef_nonterm(item).

%  Keep track of which nonterminals are left recursive
:- dynamic left_recursive/1.

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


add_production(Nonterm, Body) :-
	(   compile_body(Body, Nonterm, true, Body1),
	    record_production(Nonterm, Body1),
	    fail
	;   true
	).

compile_body((B1|B2), Nonterm, Leftmost, Body) :-
	(   Body0 = B1
	;   Body0 = B2),
	compile_body(Body0, Nonterm, Leftmost, Body).
compile_body((B1,B2), Nonterm, Leftmost, Body) :-
	compile_body(B1, Nonterm, Leftmost, Body1),
	compile_body(B2, Nonterm, false, Body2),
	conjoin(Body1, Body2, Body).




add_production1((B1;B2), Nonterm) :-
	!,
	add_production1(B1, Nonterm),
	add_production1(B2, Nonterm).
add_production1(Body, Nonterm) :-
	already_left_recursive(Nonterm, Leftrec),
	transform(Body, Nonterm, Leftrec, Clauses, Leftrec1),
	maybe_remove_left_recursion(Leftrec1, Leftrec, Nonterm),
	add_clauses(Clauses, Nonterm, Leftrec1).


already_left_recursive(Nonterm, Leftrec) :-
	(   is_left_recursive(Nonterm,Tailnonterm)
	->  Leftrec = Tailnonterm
	;   Leftrec = ''
	).



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


maybe_remove_left_recursion(true, false, Nonterm) :-
	gensym('leftrec ', Tailnonterm),
	assert(is_left_recursive(Nonterm, Tailnonterm)),
	remove_left_recursion(Nonterm, Tailnonterm).


remove_left_recursion(Nonterm, Tailnonterm) :-
	Head =.. [Nonterm, Token,Prec,Stream,Term] ,
	(   retract((Head :- Body)),
	    
