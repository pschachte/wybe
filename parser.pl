%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.27 2008/06/03 08:49:18 schachte Exp $
%  Author   : Peter Schachte
%  Origin   : Thu Mar 13 16:08:59 2008
%  Purpose  : Parser for Frege
%  Copyright: © 2008 Peter Schachte.  All rights reserved.

%% TODO:
%%   o	Handle mixing character and range rules
%%   o	Handle associativity for multi-recursive rules
%%   o	Handle precedence
%%   o	Handle recursive meta-grammar rules
%%   o	Ensure lex rules include only chars from a single class
%%   o	After invoking lex rules from syn rules, skip whitespace
%%   o	More efficient handling of tail-recursive construction for
%%	right-recursive rules?
%%   o	Handle separate compilation of multiple files, where each file *starts*
%%	being parsed with the standard syntax, with additions made as
%%	dependencies are loaded.

:- module(parser, [ process_file/2,
		    process_file/3,
		    process_stream/2,
		    add_production/2,
		    add_production/3,
		    parse_nonterm/5,
		    init_parser/0,
		    % XXX For testing:
		    show_parser/0,
		    test/0, test2/0, test3/0, test4/0
		  ]).



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



test :-
	add_production(cond,
		       ("if",expr,"then",stmts,"endif")).
test2 :-
	add_production(cond,
		       ("if",expr,"then",stmts,"else",stmts,"endif")).

test3 :-
	add_production((A|B), A),
	add_production((A|B), B).


test4 :-
	add_production(int, mkint1:("0"-"9"), lex),
	add_production(int, mkint2:(int, "0"-"9"), lex).


mkint1(Ch, Int) :-
	mkint2(0, Ch, Int).

mkint2(Int0, Ch, Int) :-
	Int is Int0*10 + Ch - 0'0.


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
%    a_tail ::= 'x' b a_tail
%    a_tail ::= 'y' c a_tail
%    a_tail ::=
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

:- use_module(library(gensym)).


/****************************************************************
			    Parser Infrastructure
****************************************************************/

%  process_file(+File, +Handler)
%  process_file(+File, +Options, +Handler)
%  Open and process File, calling Handler with each item as it is read.
%  Options is as for open; it defaults to [].

process_file(File, Handler) :-
	process_file(File, [], Handler).

process_file(File, Options, Handler) :-
	open(File, read, Stream, Options),
	process_stream(Stream, Handler),
	close(Stream).


%  process_stream(+Stream, +Handler)
%  Call Handler with each item as it is read from Stream.

process_stream(Stream, Handler) :-
	get0(Stream, Char),
	process_stream1(Char, Stream, Handler).


process_stream1(-1, _, _) :-		% End of file
	!.
process_stream1(Char, Stream, Handler) :-
	parse_nonterm(Char, item, Stream, Item, Char1),
	(   call(Handler, Item)
	->  true
	;   write('! Handler failed !\n')
	),
	process_stream1(Char1, Stream, Handler).
	


%  parse_nonterm(Ch0, Nonterm, Stream, Item, Ch)
%  parse_nonterm(Ch0, Nonterm, Stream, Stack0, Stack, Ch)
%  Item is the AST derived by parsing nonterminal Nonterm beginning with
%  character Ch0, with other chars read from Stream.  Ch is the first
%  character following the Nonterm.  Stack is a list of ASTs from nontermals
%  already parsed.

parse_nonterm(Ch0, Nonterm, Stream, Item, Ch) :-
	parse_nonterm(Ch0, Nonterm, Stream, [], [Item|Rest], Ch),
	(   Rest == []
	->  true
	;   throw(internal_error('non-empty stack after parse'))
	).


parse_nonterm(Ch0, Nonterm, Stream, Stack0, Stack, Ch) :-
	(   nonterm_rule(Ch0, Nonterm, Body)
	->  Stack1 = Stack0,		% force determinism
	    get_code(Stream, Ch1)
	;   range_rule(Nonterm, Lo_ch, Hi_ch, Body),
	    Lo_ch =< Ch0, Ch0 =< Hi_ch
	->  Stack1 = [Ch0|Stack0],	% force determinism
	    get_code(Stream, Ch1)
	;   catchall_rule(Nonterm, Body)
	->  Stack1 = Stack0,		% force determinism
	    Ch1 = Ch0
	;   throw(syntax_error)
	),
	parse_body(Body, Stream, Ch1, Ch, Stack1, Stack).


parse_body([], _, Ch, Ch, Stack, Stack).
parse_body([X|Xs], Stream, Ch0, Ch, Stack0, Stack) :-
	%  Funky code to make parsing more tail recursive
	(   Xs == []
	->  parse_item(X, Stream, Ch0, Ch, Stack0, Stack)
	;   parse_item(X, Stream, Ch0, Ch1, Stack0, Stack1),
	    parse_body(Xs, Stream, Ch1, Ch, Stack1, Stack)
	).


parse_item(chars(Expected), Stream, Ch0, Ch, Stack, Stack) :-
	(   match_chars(Expected, Stream, Ch0, Ch)
	->  true
	;   throw(unexpected(Ch0, Expected))
	).
parse_item(token_end(Class), Stream, Ch0, Ch, Stack, Stack) :-
	(   token_end(Class, Ch0)
	->  skip_white(Ch0, Stream, Ch)
	;   throw(runtogethertokens(Ch0, Class))
	).
parse_item(range(Low,High), Stream, Ch0, Ch, Stack, Stack) :-
	(   Low =< Ch0, Ch0 =< High
	->  get_code(Stream, Ch)
	;   throw(out_of_range(Ch0, Low, High))
	).
parse_item(nonterminal(Nonterm), Stream, Ch0, Ch, Stack0, Stack) :-
	parse_nonterm(Ch0, Nonterm, Stream, Stack0, Stack, Ch).
parse_item(build(Id,Count), _, Ch, Ch, Stack0, [Item|Stack]) :-
	parse_result(Id, Count, Stack0, Stack, Item).
parse_item(call(Pred,Count), _, Ch, Ch, Stack0, [Item|Stack]) :-
	call_result(Count, Pred, Stack0, Stack, Item).



token_end(special, _).
token_end(symbol, Ch) :-
	\+ symbol_char(Ch).
token_end(punctuation, Ch) :-
	\+ punctuation_char(Ch).


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


call_result(1, Id, [A|Stack], Stack, Item) :-
	!,
	call(Id, A, Item).
call_result(2, Id, [A,B|Stack], Stack, Item) :-
	!,
	call(Id, B, A, Item).
call_result(3, Id, [A,B,C|Stack], Stack, Item) :-
	!,
	call(Id, C, B, A, Item).
call_result(4, Id, [A,B,C,D|Stack], Stack, Item) :-
	!,
	call(Id, D, C, B, A, Item).
call_result(5, Id, [A,B,C,D,E|Stack], Stack, Item) :-
	!,
	call(Id, E, D, C, B, A, Item).
call_result(_, _, _, _, _) :-
	throw('call of constructor with too many args!').



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


punctuation_char(Char) :-
	Char > 0' ,
	\+ special_char(Char),
	\+ symbol_char(Char).


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
:- dynamic range_rule/4.
:- dynamic catchall_rule/2.
:- dynamic meta_grammar_rule/2.
:- dynamic left_recursive/2.
:- dynamic generated_nonterminal/1.

init_parser :-
	retractall(nonterm_rule(_,_,_)),
	retractall(range_rule(_,_,_,_)),
	retractall(catchall_rule(_,_)),
	retractall(meta_grammar_rule(_,_)),
	retractall(left_recursive(_,_)),
	retractall(generated_nonterminal(_)).



show_parser :-
	listing(nonterm_rule),
	listing(range_rule),
	listing(catchall_rule),
	listing(meta_grammar_rule).



/****************************************************************
			    The Parser Generator
****************************************************************/

%  add_production(Nonterm, Body)
%  add_production(Nonterm, Body, Kind)
%  Add new grammar rule Nonterm ::= Body to grammar.  This produces a
%  deterministic LL(n) parser.  The code automatically incrementally performs
%  the above-described transformations to create a deterministic parser, if
%  possible.  Does not warn if the grammar is il-formed, since productions
%  added later may correct the problem.  Errors are reported when they are
%  discovered during parsing.  Kind is either 'syn', in which case each
%  terminal is taken to be a discrete token (so any following whitespace is
%  skipped), or 'lex', in which case each terminal is just taken to be
%  characters.  The default is 'syn'.


add_production(Head, Body) :-
	add_production(Head, Body, syn).


add_production(Head, Body, Kind) :-
	(   compound(Head)
	->  assert(meta_grammar_rule(Head, Body))
	;   Body = Constructor:Body1
	->  add_production1(Head, call(Constructor,Args), Args, Body1, Kind)
	;   atom_concat(Head, ' ', Prefix),
	    gensym(Prefix, Id),
	    add_production1(Head, build(Id,Args), Args, Body, Kind)
	).

add_production1(Head, Build, Args, Body, Kind) :-
	(   compile_body(Body, Comp, [Build], 0, Args, Kind),
	    record_production(Head, Comp, Head, Body),
	    fail
	;   true
	).


%  compile_body(Rule, Comp, Comp0, Args, Args0, Kind)
%  Comp is the code to parse input according to grammar rule Rule, followed
%  by Comp0.

compile_body((B1,B2), Comp, Comp0, Args, Args0, Kind) :-
	!,
	compile_body(B1, Comp, Comp1, Args, Args1, Kind),
	compile_body(B2, Comp1, Comp0, Args1, Args0, Kind).
compile_body([Ch|Chs], Comp, Comp0, Args, Args, Kind) :-
	!,
	terminal_goal([Ch|Chs], Comp, Comp0, Kind).
compile_body("", Comp, Comp, Args, Args, _).
compile_body([Ch1]-[Ch2], [range(Ch1,Ch2)|Comp0], Comp0,
	     Args0, Args, Kind) :-
	!,
	(   Kind = lex
	->  Args is Args0 + 1
	;   throw('char range only permitted in lex rules')
	).
compile_body(Nonterminal, Comp, Comp0, Args0, Args, Kind) :-
	(   compound(Nonterminal)
	->  meta_grammar_rule(Nonterminal, Metabody),
	    compile_body(Metabody, Comp, Comp0, Args0, Args, Kind)
	;   Comp = [nonterminal(Nonterminal)|Comp0],
	    Args is Args0 + 1
	).


terminal_goal(Chars, [chars(Chars)|Comp1], Comp0, Kind) :-
	(   uniform_token(Chars, Class)
	->  token_end_goal(Kind, Class, Comp1, Comp0)
	;   throw(invalid_token(Chars))
	).


uniform_token([_], _).
uniform_token([Ch], special) :-
	special_char(Ch).
uniform_token([Ch|Chs], symbol) :-
	symbol_char(Ch),
	uniform_token(Chs, symbol).
uniform_token([Ch|Chs], punctuation) :-
	punctuation_char(Ch),
	uniform_token(Chs, punctuation).


token_end_goal(lex, _, Comp, Comp).
token_end_goal(syn, Class, [token_end(Class)|Comp0], Comp0).


%  record_production(Nonterm, Comp, Orig_nonterm, Orig_body)
%  Add a new production for Nonterm with compiled body Comp.  Orig_nonterm
%  and Orig_body are the nonterminal and body as original written by the
%  user, for error-reporting purposes.  Id is the constructor generated for
%  this production.

record_production(Nonterm, Comp, Orig_nonterm, Orig_body) :-
	left_unfold(Comp, Nonterm, Comp1),
	(   Comp = [nonterminal(Nonterm)|Comp2]
	->  convert_left_recursive(Nonterm, Rulenonterm),
	    append(Comp2, [nonterminal(Rulenonterm)], Body)
	;   Body = Comp1,
	    Rulenonterm = Nonterm
	),
	(   initial_body_char(Body, Char, Rest)
	->  add_grammar_clause(Char, Rulenonterm, Rest, Orig_nonterm, Orig_body)
	;   throw(left_unfolding_failed(Nonterm, Comp, Orig_nonterm, Orig_body))
	).


add_grammar_clause(Char, Nonterm, Body, Orig_nonterm, Orig_body) :-
	(   left_recursive(Nonterm, Tailnonterm)
	->  make_lrec_production(Body, Tailnonterm, Body1)
	;   Body1 = Body
	),
	add_grammar_clause1(Char, Nonterm, Body1, Orig_nonterm, Orig_body).



add_grammar_clause1('', Nonterm, Body, Orig_nonterm, Orig_body) :-
	!,
	(   clause(catchall_rule(Nonterm, _), true)
	->  throw(multiple_catcall_rules(Orig_nonterm, Orig_body))
	;   assert(catchall_rule(Nonterm, Body))
	).
add_grammar_clause1(Low-High, Nonterm, Body, Orig_nonterm, Orig_body) :-
	!,
	(   clause(range_rule(Nonterm, Low, High, Oldbody), true, Ref)
	->  left_factor(Nonterm, Low-High, Oldbody, Ref, Body,
			Orig_nonterm, Orig_body)
	;   assert(range_rule(Nonterm, Low, High, Body))
	).
add_grammar_clause1(Char, Nonterm, Body, Orig_nonterm, Orig_body) :-
	(   clause(nonterm_rule(Char, Nonterm, Oldbody), true, Ref)
	->  left_factor(Nonterm, Char, Oldbody, Ref, Body,
			Orig_nonterm, Orig_body)
	;   assert(nonterm_rule(Char, Nonterm, Body))
	).



initial_body_char([Instr|Rest], Char, Body) :-
	initial_instr_char(Instr, Char, Rest, Body).


initial_instr_char(chars([Char|Chars]), Char, Rest,
		   [chars(Chars)|Rest]).
initial_instr_char(range(Low,High), Low-High, Rest, Rest).
initial_instr_char(build(X,Y), '', Rest, [build(X,Y)|Rest]).
initial_instr_char(call(X,Y), '', Rest, [call(X,Y)|Rest]).



left_unfold([nonterminal(Nonterm)|Rest], Parent, Body) :-
	!,
	(   Nonterm == Parent		% left recursive!
	->  Body = [nonterminal(Nonterm)|Rest]
	;   nonterm_rule(Ch, Nonterm, Body1),
	    append([chars([Ch])|Body1], Rest, Body)
	;   range_rule(Nonterm, Low, High, Body1),
	    append([range(Low,High)|Body1], Rest, Body)
	;   catchall_rule(Nonterm, Body1),
	    append(Body1, Rest, Body)
	).
left_unfold(Body, _, Body).



left_factor(Nonterm, Char, Oldbody, Ref, Body, Orig_nonterm, Orig_body) :-
	(   split_common_start(Oldbody, Newold, Body, Newbody,
			       Commonbody, Commontail),
	    (	( Newold = [build(_,_)] ; Newold = [call(_,_)] ),
		( Newbody = [build(_,_)] ; Newbody = [call(_,_)] )
	    ->	throw(redundant_rule(Orig_nonterm, Orig_body))
	    ;	Newold = [nonterminal(Gennonterm)|_],
		generated_nonterminal(Gennonterm)
	    ->	true
	    ;	erase(Ref),
		gensym('GEN', Gennonterm),
		assert(generated_nonterminal(Gennonterm)),
		Commontail = [nonterminal(Gennonterm)],
		add_grammar_clause1(Char, Nonterm, Commonbody,
				   Orig_nonterm, Orig_body),
		record_production(Gennonterm, Newold, Orig_nonterm, Orig_body)
	    ),
	    record_production(Gennonterm, Newbody, Orig_nonterm, Orig_body)
	).


split_common_start([Old1|Olds], Newold, [New1|News], Newnew, Common, Common0) :-
	(   Old1 = New1
	->  Common = [Old1|Common1],
	    split_common_start(Olds, Newold, News, Newnew, Common1, Common0)
	;   split_common_token(Old1, Old2, New1, New2, Common1)
	->  Common = [Common1|Common0],
	    Newold = [Old2|Olds],
	    Newnew = [New2|News]
	;   Common = Common0,
	    Newold = [Old1|Olds],
	    Newnew = [New1|News]
	).
	

split_common_token(Olds0, Olds, News0, News, chars(Commonchs)) :-
	token_chars(Olds0, Oldchs0, Olds, Oldchs),
	token_chars(News0, Newchs0, News, Newchs),
	common_initial_sublist(Oldchs0, Newchs0, Commonchs, Oldchs, Newchs).
	
token_chars(chars(Chs1), Chs1, chars(Chs2), Chs2).

common_initial_sublist(Xs0, Ys0, Common, Xs, Ys) :-
	(   Xs0 = [X|Xs1],
	    Ys0 = [X|Ys1]
	->  Common = [X|Common1],
	    common_initial_sublist(Xs1, Ys1, Common1, Xs, Ys)
	;   Common = [],
	    Xs = Xs0,
	    Ys = Ys0
	).


convert_left_recursive(Nonterm, Tailnonterm) :-
	(   left_recursive(Nonterm, Tailnonterm)
	->  true			% already done
	;   gensym('LREC', Tailnonterm),
	    assert(left_recursive(Nonterm, Tailnonterm)),
	    (	clause(nonterm_rule(Char, Nonterm, Body), true, Ref),
		erase(Ref),
		make_lrec_production(Body, Tailnonterm, Body1),
		assertz(nonterm_rule(Char, Nonterm, Body1)),
		fail
	    ;	clause(range_rule(Nonterm, Low, High, Body), true, Ref),
		erase(Ref),
		make_lrec_production(Body, Tailnonterm, Body1),
		assertz(range_rule(Nonterm, Low, High, Body1)),
		fail
	    ;	clause(catchall_rule(Nonterm, Body), true, Ref),
		erase(Ref),
		make_lrec_production(Body, Tailnonterm, Body1),
		assertz(catchall_rule(Nonterm, Body1)),
		fail
	    ;	assertz(catchall_rule(Tailnonterm, []))
	    )
	).


make_lrec_production(Body0, Tailnonterm, Body) :-
	append(Body0, [nonterminal(Tailnonterm)], Body).

