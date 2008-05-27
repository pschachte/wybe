%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.18 2008/05/28 05:38:29 schachte Exp $
%  Author   : Peter Schachte
%  Origin   : Thu Mar 13 16:08:59 2008
%  Purpose  : Parser for Frege
%  Copyright: © 2008 Peter Schachte.  All rights reserved.

%% TODO:
%%	Support lex rules
%%	Decide whether or not to do left unfolding
%%	Handle left recursion
%%	Handle associativity
%%	Handle precedence
%%	Clean up


:- module(parser, [ test/0, test2/0,
		    add_production/2,
		    init_parser/0
		  ]).

test :-
	add_production(cond,
		       ("if",expr,"then",stmts,"endif")).
test2 :-
	add_production(cond,
		       ("if",expr,"then",stmts,"else",stmts,"endif")).


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


/****************************************************************
			    Parser Infrastructure
****************************************************************/

%  parse_nonterm(Ch0, Nonterm, Stream, Item, Ch)
%  parse_nonterm(Ch0, Nonterm, Stream, Stack, Item, Ch)
%  Item is the AST derived by parsing nonterminal Nonterm beginning with
%  character Ch0, with other chars read from Stream.  Ch is the first
%  character following the Nonterm.  Stack is a list of ASTs from nontermals
%  already parsed.

parse_nonterm(Ch0, Nonterm, Stream, Item, Ch) :-
	parse_nonterm(Ch0, Nonterm, Stream, [], Item, Ch).


parse_nonterm(Ch0, Nonterm, Stream, Stack0, Item, Ch) :-
	(   nonterm_rule(Ch0, Nonterm, Rule)
	->  true		% force determinism
	;   throw(syntax_error)
	),
	get_code(Stream, Ch1),
	rule_body(Rule, Body),
	parse_body(Body, Stream, Ch1, Ch, Stack0, Item).


parse_body([], _, Ch, Ch, [Item], Item).
parse_body([X|Xs], Stream, Ch0, Ch, Stack0, Item) :-
	parse_item(X, Stream, Ch0, Ch1, Stack0, Stack),
	parse_body(Xs, Stream, Ch1, Ch, Stack, Item).


parse_item(symchars(Expected), Stream, Ch0, Ch, Stack, Stack) :-
	(   match_chars(Expected, Stream, Ch0, Ch1),
	    \+ symbol_char(Ch1)
	->  skip_white(Ch1, Stream, Ch)
	;   throw(unexpected(Ch0, Expected))
	).
parse_item(punctchars(Expected), Stream, Ch0, Ch, Stack, Stack) :-
	(   match_chars(Expected, Stream, Ch0, Ch1),
	    \+ punctuation_char(Ch1)
	->  skip_white(Ch1, Stream, Ch)
	;   throw(unexpected(Ch0, Expected))
	).
parse_item(justchars(Expected), Stream, Ch0, Ch, Stack, Stack) :-
	(   match_chars(Expected, Stream, Ch0, Ch)
	->  true
	;   throw(unexpected(Ch0, Expected))
	).
parse_item(chartoken(Char), Stream, Ch0, Ch, Stack, Stack) :-
	(   Char == Ch0
	->  get_code(Stream, Ch1),
	    skip_white(Ch1, Stream, Ch)
	;   throw(unexpected(Ch0, Char))
	).
parse_item(nonterm(Nonterm), Stream, Ch0, Ch, Stack, [Item|Stack]) :-
	parse_nonterm(Ch0, Nonterm, Stream, Item, Ch).
parse_item(finish(Id,Count), _, Ch, Ch, Stack0, [Item|Stack]) :-
	parse_result(Id, Count, Stack0, Stack, Item).
parse_item(continue(Nonterm), Stream, Ch0, Ch, Stack0, Item) :-
	parse_nonterm(Ch0, Nonterm, Stream, Stack0, Item, Ch).


parse_result(Id, Count, Stack0, Stack, Item) :-
	functor(Id, Count, Item),
	pop_args(Count, Stack0, Stack, Item).

pop_args(N, Stack0, Stack, Item) :-
	(   N =< 0
	->  Stack = Stack0
	;   Stack0 = [Arg|Stack1],
	    arg(N, Item, Arg),
	    N1 is N - 1,
	    pop_args(N1, Stack1, Stack, Item)
	).



match_chars([], _, Ch, Ch).
match_chars([Ch0|Chs], Stream, Ch0, Ch) :-
	get_code(Stream, Ch1),
	match_chars(Chs, Stream, Ch1, Ch).


symbol_char(Char) :-
	(   Char >= 0'a, Char =< 0'z
	->  true
	;   Char >= 0'A, Char =< 0'Z
	->  true
	;   Char >= 0'0, Char =< 0'9
	->  true
	;   Char =:= 0'_
	).


all_symchars([]).
all_symchars([Ch|Chs]) :-
	symbol_char(Ch),
	all_symchars(Chs).


punctuation_char(Char) :-
	Char > 0' ,
	\+ special_char(Char),
	\+ symbol_char(Char).

all_punctchars([]).
all_punctchars([Ch|Chs]) :-
	punctuation_char(Ch),
	all_punctchars(Chs).


special_char(0'().
special_char(0')).
special_char(0'[).
special_char(0']).
special_char(0'{).
special_char(0'}).
special_char(0'').
special_char(0'"). %"
special_char(0'`).
special_char(0',).


skip_white(0'#, Stream, Char) :-
	!,
	get_code(Stream, Char1),
	skip_line(Char1, Stream, Char).
skip_white(Char0, Stream, Char) :-
	(   Char0 > 0' % space character
	->  Char = Char0
	;   Char0 < 0
	->  Char = Char0
	;   get_code(Stream, Char1),
	    skip_white(Char1, Stream, Char)
	).


skip_line(0'\n, Stream, Ch) :-
	!,
	get_code(Stream, Ch).
skip_line(_, Stream, Ch) :-
	get_code(Stream, Ch1),
	skip_line(Ch1, Stream, Ch).


:- dynamic nonterm_rule/3.
:- dynamic rule_body/2.


% nonterm_rule(0'i, stmt, 1).

% rule_body(1,
% 	  [symchars("f"),nonterm(expr),symchars("then"),
% 	   nonterm(stmts),symchars("end")]).





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
	retractall(nonterm_rule(_,_,_)).


%  add_production(Nonterm, Body)
%  Add new grammar rule Nonterm ::= Body to grammar.  This produces a
%  deterministic LL(1) parser.  The code automatically incrementally performs
%  the above-described transformations to create a deterministic parser, if
%  possible.  Does not warn if the grammar is il-formed, since productions
%  added later may correct the problem.  Errors are reported when they are
%  discovered during parsing.


add_production(Head, Body) :-
	atom_concat(Head, ' ', Prefix),
	gensym(Prefix, Id),
	(   compile_body(Body, Comp, [finish(Id,Args)], 0, Args),
	    record_production(Head, Comp, Head, Body),
	    fail
	;   true
	).


%  compile_body(Rule, Comp, Comp0, Args, Args0)
%  Comp is the code to parse input according to grammar rule Rule, followed
%  by Comp0.

compile_body((B1|B2), Comp, Comp0, Args0, Args) :-
	!,
	( Body0 = B1 ; Body0 = B2 ),
	compile_body(Body0, Comp, Comp0, Args0, Args).
compile_body((B1,B2), Comp, Comp0, Args, Args0) :-
	!,
	compile_body(B1, Comp, Comp1, Args, Args1),
	compile_body(B2, Comp1, Comp0, Args1, Args0).
compile_body('', Comp, Comp, Args, Args) :-
	!.
compile_body([Ch|Chs], [Goal|Comp0], Comp0, Args, Args) :-
	!,
	terminal_goal([Ch|Chs], Goal).
compile_body(Nonterminal, [Goal|Comp], Comp, Args0, Args) :-
	Args is Args0 + 1,
	nonterminal_goal(Nonterminal, Goal).


is_terminal(bracket(_,_)).
is_terminal(string(_,_)).
is_terminal(symbol(_)).
is_terminal(punct(_)).


terminal_goal(Chars, Goal) :-
	(   Chars = [Ch],
	    special_char(Ch)
	->  Goal = chartoken(Ch)
	;   all_symchars(Chars)
	->  Goal = symchars(Chars)
	;   all_punctchars(Chars)
	->  Goal = punctchars(Chars)
	;   throw(invalid_token(Chars))
	).


nonterminal_goal(Nonterm, nonterminal(Nonterm)).



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


conjoin_compiled([A|B], C, [A|BC]) :-
	!,
	conjoin_compiled(B, C, BC).
conjoin_compiled(A, B, [A|B]).


%  record_production(Nonterm, Comp, Orig_nonterm, Orig_body)
%  Add a new production for Nonterm with compiled body Comp.  Orig_nonterm
%  and Orig_body are the nonterminal and body as original written by the
%  user, for error-reporting purposes.  Id is the constructor generated for
%  this production.

record_production(Nonterm, Comp, Orig_nonterm, Orig_body) :-
	% do we really want to do this?
	left_unfold(Comp, Nonterm, Comp1),
	(   left_recursive_body(Comp1, Nonterm, Comp2)
	->  (	left_recursive_body(Comp2, Nonterm, _)
	    ->	throw(double_left_recursive(Orig_nonterm, Orig_body))
	    ;	update_left_recursive(Nonterm),
		make_lrec_production(Nonterm, Comp2, Realbody)
	    )
	;   left_recursive_nonterm(Nonterm, Tailcall)
	->  append(Comp2, Tailcall, Realbody)
	;   Realbody = Comp1
	),
	(   initial_body_char(Realbody, Char, Rest)
	->  add_grammar_clause(Nonterm, Char, Rest, Orig_nonterm, Orig_body)
	;   throw(left_unfolding_failed(Nonterm, Comp, Orig_nonterm, Orig_body))
	).


add_grammar_clause(Nonterm, Char, Body, Orig_nonterm, Orig_body) :-
	(   clause(nonterm_rule(Char, Nonterm, Oldbody), true, Ref)
	->  left_factor(Nonterm, Char, Oldbody, Ref, Body,
			Orig_nonterm, Orig_body)
	;   assert(nonterm_rule(Char, Nonterm, Body))
	).



initial_body_char([symchars([Char|Chars])|Rest], Char, [symchars(Chars)|Rest]).
initial_body_char([punctchars([Char|Chars])|Rest], Char,
		  [punctchars(Chars)|Rest]).
initial_body_char([justchars([Char|Chars])|Rest], Char, [justchars(Chars)|Rest]).
initial_body_char([chartoken(Char)|Rest], Char, Rest).



initial_goal((A,B), A, B) :-
	!.
initial_goal(Init, Init, true).



left_unfold([nonterm(Nonterm)|Rest], Parent, Body) :-
	!,
	(   Nonterm == Parent		% left recursive!
	->  Body = [nonterm(Nonterm)|Rest]
	;   nonterm_clause(Nonterm, Body1),
	    conjoin_compiled(Body1, Rest, Body2),
	    left_unfold(Body2, Nonterm, Body)
	).
left_unfold(Body, _, Body).



left_recursive_body([nonterm(Parent)|Rest], Parent, Rest).


left_recursive_nonterm(Nonterm, nonterm(Tailpred)) :-
	left_recursive(Nonterm, Tailpred).


matching_clause(Nonterm, Sym, Stream, Extras, Oldterm, Oldbody, Ref) :-
	Pattern =.. [Nonterm, Sym, Stream, Oldterm | Extras],
	parser_rule:clause(Pattern, _:Oldbody, Ref).
	


left_factor(Nonterm, Char, Oldbody, Ref, Body, Orig_nonterm, Orig_body) :-
	(   split_common_start(Oldbody, Newold, Body, Newbody,
			       Commonbody, Commontail),
	    (	Newold = [finish(_,_)],
		Newbody = [finish(_,_)]
	    ->			% trying to add a redundant grammar rule
		throw(redundant_rule(Orig_nonterm, Orig_body))
	    ;	Newold = [continue(Gennonterm)|_]
	    ->	true
	    ;	erase(Ref),
		gensym('GEN', Gennonterm),
		Commontail = [continue(Gennonterm)],
		add_grammar_clause(Nonterm, Char, Commonbody,
				   Orig_nonterm, Orig_body),
		record_production(Gennonterm, Newold, Orig_nonterm, Orig_body)
	    ),
	    record_production(Gennonterm, Newbody, Orig_nonterm, Orig_body)
	).


% Thinking about left recursion, associativity, and precedence:
%
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


split_common_start([Old1|Olds], [New1|News], Common, Common0, Newold, Newnew) :-
	(   Old1 = New1
	->  Common = [Old1|Common1],
	    split_common_start(Olds, News, Common1, Common0, Newold, Newnew)
	;   split_common_token(Old1, Old2, New1, New2, Common1)
	->  Common = [Common1|Common0],
	    Newold = [Old2|Olds],
	    Newnew = [New2|News]
	;   Common = Common0,
	    Newold = [Old1|Olds],
	    Newnew = [New1|News]
	).
	

split_common_token(Olds0, Olds, News0, News, justchars(Commonchs)) :-
	token_chars(Olds0, Oldchs0, Olds, Oldchs),
	token_chars(News0, Newchs0, News, Newchs),
	common_initial_sublist(Oldchs0, Newchs0, Commonchs, Oldchs, Newchs).
	
token_chars(symchars(Chs1), Chs1, symchars(Chs2), Chs2).
token_chars(punctchars(Chs1), Chs1, punctchars(Chs2), Chs2).
token_chars(justchars(Chs1), Chs1, justchars(Chs2), Chs2).

common_initial_sublist(Xs0, Ys0, Common, Xs, Ys) :-
	(   Xs0 = [X|Xs1],
	    Ys0 = [X|Ys1]
	->  Common = [X|Common1],
	    common_initial_sublist(Xs1, Ys1, Common1, Xs, Ys)
	;   Common = [],
	    Xs = Xs0,
	    Ys = Ys0
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
