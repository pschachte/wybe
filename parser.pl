%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.12 2008/05/15 06:37:10 schachte Exp $
%  Author   : Peter Schachte
%  Origin   : Thu Mar 13 16:08:59 2008
%  Purpose  : Parser for Frege
%  Copyright: © 2008 Peter Schachte.  All rights reserved.

:- module(parser, [ test/0, test2/0,
		    get_item/2,
		    add_production/2,
		    init_parser/0
		  ]).

test :-
	add_production(cond,
		       (symbol(if),expr,symbol(then),stmts,symbol(endif))).
test2 :-
	add_production(cond,
		       (symbol(if),expr,symbol(then),stmts,symbol(else),stmts,symbol(endif))).


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
%  The generated parser consists of a dynamic predicate for each nonterminal
%  of the grammar, whose arguments are the next input token, the stream to
%  read from, and the resulting abstract syntax tree.  Each clause consumes
%  the next input token.
%
%	 item('use', Stream, use(Term)) :-
%	 	nonterminal(use_decl, Stream, Term).
%	 item('module', Stream, module(Term)) :-
%	 	nonterminal(module_decl, Stream, Term).
%	 item('class', Stream, Term) :-
%	 	nonterminal(class_decl, Stream, Term).
%
%  The first argument of each clause head is a distinct token, so indexing
%  makes the code deterministic.  To ensure this is possible, three
%  transformations are applied:  left recursion elimination, left unfolding,
%  and left factoring.  Grammars that cannot be made deterministic by
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
%  production ending in a nullable or final nullable nonterminal.  We must
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

:- use_module(lex).
:- use_module(library(gensym)).


% Read a top-level item (declaration or directive) from the specified stream.

get_item(Stream, Item) :-
	get_token(Stream, Token, _),
	parser_rule:item(Token, Stream, Item).


%  Entry into the dynamic part of the parser.
:- dynamic parse_table/4.
:- dynamic parse_table/5.
:- dynamic parse_table/6.


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


init_parser :-
	retractall(parser_rule:_),
	retractall(parse_table(_,_,_,_)),
	retractall(parse_table(_,_,_,_,_)),
	retractall(parse_table(_,_,_,_,_,_)),
	retractall(left_recursive(_,_)),
	retractall(final_nullable(_)).


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
	    record_production(Head, Stream, [], Term, Body1, Head, Body1),
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


nonterminal_goal(Nonterm, Stream, Term, nonterminal(Stream,Nonterm,Term)).

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
concat_codes1([Tok|Toks], [0' |Cs]) :-
	terminal_symbol(Tok, Sym),
	symbol_codes(Sym, Cs1),
	append(Cs1, Cs2, Cs),
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


%  record_production(Nonterm, Stream, Extras, Term, Body)
%  Add a new production for Nonterm with body Body.  Tokens are to be read
%  from Stream, and the result of this grammar rule is Term, and Extras is a
%  list of the extra inputs the grammar rule must take to construct Term.

record_production(Nonterm, Stream, Extras, Term, Body, Orig_nonterm, Orig_body) :-
	left_unfold(Body, Nonterm, Body1),
	(   left_recursive_body(Body1, Nonterm, Body2)
	->  (	left_recursive_body(Body2, Nonterm, _)
	    ->	throw(double_left_recursive(Orig_nonterm, Orig_body))
	    ;	update_left_recursive(Nonterm),
		make_lrec_production(Nonterm, Stream, Term, Body2, Realbody)
	    )
	;   left_recursive_nonterm(Nonterm, Stream, Term, Tailcall)
	->  conjoin(Body2, Tailcall, Realbody)
	;   Realbody = Body1
	),
	(   initial_goal(Realbody, terminal(Stream,Sym), Rest)
	->  add_grammar_clause(Nonterm, Stream, Extras, Term, Sym, Rest,
			   Orig_nonterm, Orig_body)
	;   throw(left_unfolding_failed(Nonterm, Body, Orig_nonterm, Orig_body))
	).


add_grammar_clause(Nonterm, Stream, Extras, Term, Sym, Body,
		   Orig_nonterm, Orig_body) :-
	(   matching_clause(Nonterm, Sym, Stream, Extras, Oldterm,
			    Oldbody, Ref)
	->  left_factor(Nonterm, Sym, Stream, Extras, Oldterm, Oldbody,
			Ref, Term, Body, Orig_nonterm, Orig_body)
	;   Newhead =.. [Nonterm, Sym, Stream, Term | Extras],
	    assert((parser_rule:Newhead:-Body)),
	    add_nonterm_master_clause(Nonterm, Extras)
	).



initial_goal((A,B), A, B) :-
	!.
initial_goal(Init, Init, true).



left_unfold(Body0, Nonterm, Body) :-
	initial_goal(Body0, Lead, Rest),
	left_unfold1(Lead, Rest, Body0, Nonterm, Body).

left_unfold1(terminal(_,_), _, Body, _, Body).
left_unfold1(nonterminal(_,Nonterm,_), Rest, Body0, Parent, Body) :-
	(   Nonterm == Parent
	->  Body = Body0
	;   nonterm_clause(Nonterm, Body1),
	    conjoin(Body1, Rest, Body2),
	    left_unfold(Body2, Nonterm, Body)
	).


left_recursive_body(Body, Nonterm, Rest) :-
	initial_goal(Body, nonterm(_,Nonterm,_,_), Rest).


left_recursive_nonterm(Nonterm, Stream, Term, Tailcall) :-
	left_recursive(Nonterm, Tailpred),
	Tailcall =.. [Tailpred, Stream, Term].


matching_clause(Nonterm, Sym, Stream, Extras, Oldterm, Oldbody, Ref) :-
	Pattern =.. [Nonterm, Sym, Stream, Oldterm | Extras],
	parser_rule:clause(Pattern, _:Oldbody, Ref).
	


left_factor(Nonterm, Sym, Stream, Extras, Oldterm, Oldbody, Ref, Term, Body,
	    Orig_nonterm, Orig_body) :-
	(   Body = Oldbody	% trying to add a redundant grammar rule
	->  throw(redundant_rule(Orig_nonterm, Orig_body))
	;   split_common_start(Oldbody, Body, Commonbody, Newold, Newbody, Ex),
	    append(Extras, Ex, Allextras),
	    (	generated_nonterm(Newold, Gennonterm, Allextras)
	    ->	true
	    ;	erase(Ref),
		gensym('rule ', Gennonterm),
		Newcall =.. [gennonterm, Stream, Gennonterm,
			     Generalterm | Allextras],
		conjoin(Commonbody, Newcall, Factoredbody),
		add_grammar_clause(Nonterm, Stream, Extras, Generalterm, Sym,
				   Factoredbody, Orig_nonterm, Orig_body),
		record_production(Gennonterm, Stream, Allextras, Oldterm,
				  Newold, Orig_nonterm, Orig_body)
	    ),
	    record_production(Gennonterm, Stream, Allextras, Term,
			      Newbody, Orig_nonterm, Orig_body)
	).


	%     ->	(   Body = Oldbody
	% 	->  throw(redundant_rule(Orig_nonterm, Orig_body))
	% 	;   split_common_start(Oldbody, Body, Commonbody,
	% 			       Newold, Newbody),
	% 	    
	% 	    erase(Ref),
	% 	    Pattern1 =.. [Nonterm, Sym, Stream, Term],
	% 	    assert(parser_rule:Pattern1:-Factoredbody),
	% 	    assert(parser_rule:Newhead:-Newold)
	% 	)
	%     ;	Newhead = Head,
	% 	Newbody = Body
	%     ),
	%     assert((parser_rule:Newhead:-Newbody)),
	%     add_nonterm_master_clause(Nonterm, Extras)
	% ;   throw(left_unfolding_failed(Nonterm, Body, Orig_nonterm, Orig_body))
	% ).



% e ::=
%     e + e
%     e * e
%     ( e )
%     int

% e(E) ->
%     int(X) etail(X, E)
%     ( e(X) ) etail(X, E)

% etail(X, E) ->
%     + e(Y) etail(+(X,Y), E)		% left assoc
%     * e(Y) etail(Y, Z) [E = *(X,Z)]	% right assoc


add_nonterm_master_clause(Nonterm, Extras) :-
	Head =.. [parse_table, Nonterm,A,B,C|Extras],
	(   clause(Head,_)
	->  true
	;   Generalcall =.. [Nonterm, A, B, C | Extras],
	    assert(Head:-parser_rule:Generalcall)
	).


split_common_start((Old1,Olds), New, Common, Newold, Newnew, Extras) :-
	!,
	initial_goal(New, New1, News),
	(   Old1 = New1
	->  split_common_start(Olds, News, Commons, Newold, Newnew, Extras2),
	    conjoin(Old1, Commons, Common),
	    nonterm_goal_arg(Old1, Extras, Extras2)
	;   Common = true,
	    Newold = (Old1,Olds),
	    Newnew = New,
	    Extras = []
	).
split_common_start(Old, New, Common, Newold, Newnew, Extras) :-
	initial_goal(New, New1, News),
	(   Old = New1
	->  Newold = true,
	    Newnew = News,
	    Common = Old,
	    nonterm_goal_arg(Old, Extras, [])
	;   Common = true,
	    Newold = Old,
	    Newnew = New,
	    Extras = []
	).
	
nonterm_goal_arg(terminal(_,_), Vs, Vs).
nonterm_goal_arg(nonterminal(_,_,V), [V|Vs], Vs).
nonterm_goal_arg(gennonterm(_,_,V), [V|Vs], Vs).
nonterm_goal_arg(gennonterm(_,_,V,_), [V|Vs], Vs).
nonterm_goal_arg(gennonterm(_,_,V,_,_), [V|Vs], Vs).

generated_nonterm(gennonterm(Gennonterm, _, _), Gennonterm, []).
generated_nonterm(gennonterm(Gennonterm, _, _, A), Gennonterm, [A]).
generated_nonterm(gennonterm(Gennonterm, _, _, A, B), Gennonterm, [A,B]).


%  Runtime code

terminal(Stream, Expected) :-
	get_token(Stream, Token, Position),
	terminal_symbol(Token, Found),
	(   Expected = Found
	->  true
	;   throw(terminal_error(Expected, Found, Position))
	).

nonterminal(Stream, Nonterm, Value) :-
	get_token(Stream, Token, Position),
	terminal_symbol(Token, Symbol),
	(   parse_table(Nonterm, Symbol, Stream, Value)
	->  true
	;   throw(nonterminal_error(Nonterm, Symbol, Position))
	).

gennonterm(Stream, Nonterm, Value) :-
	get_token(Stream, Token, Position),
	terminal_symbol(Token, Symbol),
	(   parse_table(Nonterm, Symbol, Stream, Value)
	->  true
	;   throw(nonterminal_error(Nonterm, Symbol, Position))
	).

gennonterm(Stream, Nonterm, Value, E1) :-
	get_token(Stream, Token, Position),
	terminal_symbol(Token, Symbol),
	(   parse_table(Nonterm, Symbol, Stream, Value, E1)
	->  true
	;   throw(nonterminal_error(Nonterm, Symbol, Position))
	).

gennonterm(Stream, Nonterm, Value, E1, E2) :-
	get_token(Stream, Token, Position),
	terminal_symbol(Token, Symbol),
	(   parse_table(Nonterm, Symbol, Stream, Value, E1, E2)
	->  true
	;   throw(nonterminal_error(Nonterm, Symbol, Position))
	).
