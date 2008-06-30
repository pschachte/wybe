%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.40 2008/07/01 08:53:57 schachte Exp $
%  Author   : Peter Schachte
%  Origin   : Thu Mar 13 16:08:59 2008
%  Purpose  : Parser for Frege
%  Copyright: © 2008 Peter Schachte.  All rights reserved.

%% PROBLEMS:
%%   o	Need a way to support shortest match, so you can do something like:
%%		ident* 'foo' ...
%%	where 'foo' matches ident.  What we really want is
%%	(any ident but 'foo')* 'foo'.
%%	We always want that in such situations, since otherwise it's
%%	difficult to parse such constructs without backtracking.
%%      Possible solution:  fuse nullable nonterminals with following grammar
%%      bodies.  Careful:  for recursive nullable other than tail
%%      recursive, will need multiple (two?) separate fusions.  Also will
%%      need to iterate when the following is also nullable.
%%
%% TODO:
%%   o	Incremental parser generation:  handle new productions that old ones
%%	depend on (unfolding problem) 
%%   o	Handle offside rule
%%   o	Handle associativity for multi-recursive rules
%%   o	Handle precedence
%%   o	Better default construction for lex rules (build list)?
%%   o	Handle recursive meta-grammar rules
%%   o	Handle layout-sensitive grammar
%%   o	Think through interface betweeen syn rules and lex rules.  Insert
%%	token_end after each terminal in a syn rule, but not in a lex rule;
%%	forbid calling syn rule from lex rule?
%%   o	More efficient handling of tail-recursive construction for
%%	right-recursive rules?
%%   o	Handle separate compilation of multiple files, where each file *starts*
%%	being parsed with the standard syntax, with additions made as
%%	dependencies are loaded.
%%   o	Decide if we really want to apply left unfolding
%%
%% New Ideas:
%%   o	"Empty" programming language:  language has only meta-syntax and
%%	parser generator.  All code generation is handled by code written in
%%	the language itself, built on an output language (eg, C or assembler).
%%	This is like IMP3, except it must have provisions for analysis and
%%	optimisation.
%%
%%   o	If each source file begins by listing all file dependencies, then all
%%	grammar rules, and finally the code, then grammar rules could be
%%	compiled to code.  Once the end of the grammar rules is found, the
%%	parser can be generated, dynamically linked in, and used to read the
%%	rest of the file.  This turns on the ability to merge two separately
%%	compiled grammars, which comes down to the ability to merge two sets
%%	of compiled grammar rules for the same nonterminal.


:- module(parser, [ process_file/2,
		    process_file/3,
		    process_stream/2,
		    add_syn/2,
		    add_lex/2,
		    parse_nonterm/5,
		    init_parser/0,
		    % XXX For testing:
		    show_parser/0, test/1
		  ]).


% Meta-circular parser grammar:
%
% syn file ::= eof
% syn file ::= processitem: file <pushindent> item <matchindent>
%
% syn item ::= visibility grammar_kind nonterminal '::=' grammar_body
% syn item ::= visibility 'metagrammar' meta '::=' syn_items
%
% syn visibility ::=
% syn visibility ::= 'pub'
%
% syn grammar_kind ::= 'syn'
% syn grammar_kind ::= 'lex'
%
% syn grammar_body ::= syn_items
% syn grammar_body ::= identifier ':' syn_items
%
% syn meta ::= metaop metapattern
% syn meta ::= metapattern nonterminal
% syn meta ::= metapattern
%
% syn metaop ::= punctop
% syn metaop ::= textop
%
% syn metapattern ::= metapattern nonterminal metaop
% syn metapattern ::= nonterminal metaop
%
% syn syn_items ::= syn_item syn_items
% syn syn_items ::=
%
% syn syn_item ::= nonterminal
% syn syn_item ::= terminal
% syn syn_item ::= charrange
% syn syn_item ::= empty
% syn syn_item ::= '(' grammar_body ')'
%
% syn nonterminal ::= identifier
%
% syn empty ::=
%
% syn charrange ::= singlechar '-' singlechar
%
% syn singlechar ::= minchar: 'minchar'
% syn singlechar ::= maxchar: 'maxchar'
% syn singlechar ::= eof    : 'eof'
% lex singlechar ::= id     : '\'' quotedchar '\'' 
%
% lex terminal ::= '\'' quotedchars '\''
%
% lex quotedchars ::= quotedchar quotedchars
% lex quotedchars ::=
%
% lex quotedchar ::= '\n': '\\n'
% lex quotedchar ::= '\r': '\\r'
% lex quotedchar ::= '\t': '\\t'
% lex quotedchar ::= '\a': '\\a'   # and so on....
% lex quotedchar ::= minchar - maxchar
%
% lex specialchar ::= '('
% lex specialchar ::= ')'
% lex specialchar ::= '['
% lex specialchar ::= ']'
% lex specialchar ::= '{'
% lex specialchar ::= '}'
% lex specialchar ::= ','
% lex specialchar ::= '\''
% lex specialchar ::= '"'
%
% lex punctchar ::= 


% Recursive meta-grammar rules can be handled by generating a new nonterminal
% for each use of a recursive meta-grammar rule, and memoizing it, so that
% the recursive use is replaced by a reference to the same new nonterminal.
% Eg, with definition X* ::= "" | X X* , a production foo ::= a b* is
% translated to foo ::= a new, plus new ::= "" | b new.


% Thinking about left recursion, associativity, and precedence:
%
% pub syn expr ::= '(' expr ')' | num | fncall | exp_expr | mul_expr | add_expr
%
% Put parens around associative recursive nonterminal; no parens means
% non-associative.
%
% pub syn add_expr ::= (expr) '+' expr | (expr) '-' expr | '-' expr
%
% Relative precedence is specified by 'prec' rules, which must come before
% definition of the nonterminal (good enough?).
%
% prec add_expr < mul_expr
% pub syn mul_expr ::= (expr) '*' expr | (expr) '/' expr
%
% prec mul_expr < exp_expr
% pub syn exp_expr ::= expr '^' expr



test(cond) :-
	add_syn(cond, ("if",expr,"then",stmts,"endif")),
	add_syn(cond, ("if",expr,"then",stmts,"else",stmts,"endif")).

test(meta) :-
	add_syn((A|B), A),
	add_syn((A|B), B),
	add_syn(*(A), (""|*(A),A)),
	add_syn(+(A), A),
	add_syn(+(A), (+(A),A)).

test(int) :-
	add_lex(int, mkint1:("0"-"9")),
	add_lex(int, mkint2:(int, "0"-"9")).

test(ident) :-
	add_lex(digit, char:("0"-"9")),
	test(alt),
	add_lex(alpha, char:("a"-"z" | "A"-"Z")),
	add_lex(identchar, char:( alpha | digit | "_")),
	add_lex(ident, mkident:( alpha, identtail )),
	add_lex(identtail, nil:""),
	add_lex(identtail, cons:(identchar, identtail)).


test(stmt).


mkint1(Ch, Int) :-
	mkint2(0, Ch, Int).

mkint2(Int0, Ch, Int) :-
	Int is Int0*10 + Ch - 0'0.

char(Char, Char).

cons(H, T, [H|T]).
nil([]).

mkident(Char, Chars, Ident) :- atom_codes(Ident, [Char|Chars]).


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
%  Left unfolding enables left recursion elimination to remove indirect, as
%  well as direct, left recursion.
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
%  handled specially, since it may not be possible to decide how to parse a
%  nullable nonterminal without knowing what the following grammar rules
%  are.  A final nullable nonterminal is either a nullable nonterminal or has
%  an alternative that ends with a final nullable nonterminal.  We solve this
%  problem by fusing each occurance of a final nullable nonterminal with the
%  following part of the grammar rule it appears in.  For example, a grammar:
%
%    a ::=
%    a ::= b
%    c ::= b a d
%
%  is automatically transformed into:
%
%    a ::=
%    a ::= b
%    c ::= b x
%    x ::= d
%    x ::= b d
%
%  Note that after the transformation, the newly generated nonterminal may
%  itself be final nullable.
%
%
%  Meta Grammar Rules
%
%  In keeping with the theme of extensible programming languages, the grammar
%  formalism itself may be extended with meta grammar rules.  These rules
%  take the form of a grammar rule with alternating nonterminals and
%  operators, starting with either kind and ending with either, and having at
%  least one of each, on the left side of the ::=, and a normal body on the
%  right.  The nonterminals on the left act as variables, and the operators
%  serve as the form of the meta grammar construct.  Each operator either
%  comprises only punctuation characters, or a single special character other
%  than a parenthesis, or a sequence of alphanumerics beginning and ending
%  with an underscore.
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

The parser is based on a stack-based abstract parsing machine with these
instructions:

	chars(Expected)		Match list of chars Expected
	pushchars(Expected)	Match list of chars Expected and push on stack
	token_end(Class)	Skip over separator chars following Class token
	range(Low,High)		Match any char between Low and High, and push
	nonterminal(Nonterm)	Match nonterminal Nonterm
	build(Id,Count)		Pop Count items, and push term with functor ID
	call(Pred,Count)	Pop Count items, and call constructor Pred
	push(Char)		Push single character Char on stack

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


%  NB:	IF any new abstract machine instructions are added, the code for
%	left_unfold must also be updated.

parse_item(chars(Expected), Stream, Ch0, Ch, Stack, Stack) :-
	(   match_chars(Expected, Stream, Ch0, Ch)
	->  true
	;   throw(unexpected(Ch0, Expected))
	).
parse_item(pushchars(Expected), Stream, Ch0, Ch, Stack0, Stack) :-
	(   match_chars(Expected, Stream, Ch0, Ch)
	->  reverse(Expected, Rev),
	    append(Rev, Stack0, Stack)
	;   throw(unexpected(Ch0, Expected))
	).
parse_item(token_end(Class), Stream, Ch0, Ch, Stack, Stack) :-
	(   token_end(Class, Ch0)
	->  skip_white(Ch0, Stream, Ch)
	;   throw(runtogethertokens(Ch0, Class))
	).
parse_item(range(Low,High), Stream, Ch0, Ch, Stack, [Ch0|Stack]) :-
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
parse_item(push(Char), _, Ch, Ch, Stack, [Char|Stack]).



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


call_result(0, Id, Stack, Stack, Item) :-
	!,
	call(Id, Item).
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
call_result(N, Id, Stack0, Stack, Item) :-
	length(Args, N),
	(   append(Revargs, Stack, Stack0)
	->  reverse([Item|Revargs], Args),
	    Goal =.. [Id | Args],
	    (	call(Goal)
	    ->	true
	    ;	throw(constructor_failed(Goal))
	    )
	;   throw(internal_error(shallow_stack, N, Stack0))
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
:- dynamic meta_rule_instance/3.

init_parser :-
	retractall(nonterm_rule(_,_,_)),
	retractall(range_rule(_,_,_,_)),
	retractall(catchall_rule(_,_)),
	retractall(meta_grammar_rule(_,_)),
	retractall(left_recursive(_,_)),
	retractall(generated_nonterminal(_)),
	retractall(meta_rule_instance(_,_,_)).



show_parser :-
	listing(nonterm_rule),
	listing(range_rule),
	listing(catchall_rule),
	listing(meta_grammar_rule).



/****************************************************************
			    The Parser Generator
****************************************************************/

%  add_syn(Nonterm, Body)
%  add_lex(Nonterm, Body)
%  add_production(Nonterm, Body, Kind)
%  Add new grammar rule Nonterm ::= Body to grammar.  This produces a
%  deterministic LL(n) parser.  The code automatically incrementally performs
%  the above-described transformations to create a deterministic parser, if
%  possible.  Does not warn if the grammar is il-formed, since productions
%  added later may correct the problem.  Errors are reported when they are
%  discovered during parsing.  Kind is either 'syn', in which case each
%  terminal is taken to be a discrete token (so any following whitespace is
%  skipped), or 'lex', in which case each terminal is just taken to be
%  characters.


add_syn(Head, Body) :-
	add_production(Head, Body, syn).

add_lex(Head, Body) :-
	add_production(Head, Body, lex).

add_production(Head, Body, Kind) :-
	(   compound(Head)
	->  assert(meta_grammar_rule(Head, Body))
	;   Body = Constructor:Body1
	->  add_production1(Head, [call(Constructor,Args)], Args, Body1, Kind)
	;   atom_concat(Head, ' ', Prefix),
	    gensym(Prefix, Id),
	    add_production1(Head, [build(Id,Args)], Args, Body, Kind)
	).

add_production1(Head, Tail, Args, Body, Kind) :-
	(   compile_body(Body, Comp, Tail, 0, Args, Kind),
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
compile_body([Ch|Chs], Comp, Comp0, Args0, Args, Kind) :-
	!,
	terminal_goal([Ch|Chs], Comp, Comp0, Args0, Args, Kind).
compile_body("", Comp, Comp, Args, Args, _) :-
	!.
compile_body([Ch1]-[Ch2], [range(Ch1,Ch2)|Comp0], Comp0,
	     Args0, Args, Kind) :-
	!,
	(   Kind = lex
	->  Args is Args0 + 1
	;   throw('char range only permitted in lex rules')
	).
compile_body(Nonterminal, Comp, Comp0, Args0, Args, Kind) :-
	(   compound(Nonterminal)
	->  ( \+ meta_grammar_rule(Nonterminal, _)
	    ->	throw(undefined_grammar_construct(Nonterminal))
	    ;	compile_meta(Nonterminal, Comp, Comp0, Args0, Args, Kind)
	    )
	;   Comp = [nonterminal(Nonterminal)|Comp0],
	    Args is Args0 + 1
	).


terminal_goal(Chars, Comp1, Comp0, Args0, Args, Kind) :-
	(   uniform_token(Chars, Class)
	->  token_goal(Kind, Chars, Class, Comp1, Comp0, Args0, Args)
	;   throw(invalid_token(Chars))
	).
	

compile_meta(Metanonterm, Comp, Comp0, Args0, Args, Kind) :-
	make_meta_instance(Metanonterm, Newnonterm, Kind),
	compile_body(Newnonterm, Comp, Comp0, Args0, Args, Kind).


make_meta_instance(Metanonterm, Head, Kind) :-
	(   meta_rule_instance(Metanonterm, Kind, Head)
	->  true
	;   gensym('META', Head),
	    assert(meta_rule_instance(Metanonterm, Kind, Head)),
	    % generate a new concrete rule for every meta rule for this
	    % meta nonterminal (failure driven loop)
	    (	meta_grammar_rule(Metanonterm, Metabody),
		add_production(Head, Metabody, Kind),
		fail
	    ;	true
	    )
	).



uniform_token([], _).
uniform_token([Ch|Chs], Kind) :-
	char_kind(Kind, Ch),
	uniform_token(Chs, Kind).

char_kind(special, Ch) :-
	special_char(Ch),
	!.
char_kind(symbol, Ch) :-
	symbol_char(Ch),
	!.
char_kind(punctuation, Ch) :-
	punctuation_char(Ch).


token_goal(lex, Chars, _, [pushchars(Chars)|Comp], Comp, Args0, Args) :-
	length(Chars, Count),
	Args is Args0 + Count.
token_goal(syn, Chars, Class, [chars(Chars),token_end(Class)|Comp0],
	       Comp0, Args, Args).


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
	(   initial_body_range(Body, Low, High, Rest)
	->  add_grammar_clause(Low, High, Rulenonterm, Rest,
			       Orig_nonterm, Orig_body)
	;   throw(left_unfolding_failed(Nonterm, Comp, Orig_nonterm, Orig_body))
	).


add_grammar_clause(Low, High, Nonterm, Body, Orig_nonterm, Orig_body) :-
	(   left_recursive(Nonterm, Tailnonterm)
	->  make_lrec_production(Body, Tailnonterm, Body1)
	;   Body1 = Body
	),
	add_grammar_clause1(Low, High, Nonterm, Body1, Orig_nonterm, Orig_body).



add_grammar_clause1(Low, High, Nonterm, Body, Orig_nonterm, Orig_body) :-
	(   High < 0
	->  % First instruction doesn't consume a character:  catchall
	    add_catchall(Nonterm, Body, Orig_nonterm, Orig_body)
	;   Low > High
	->  % Empty range:  nothing to do
	    true
	;   Low == High
	->  % Single-character range
	    add_individual(Low, Nonterm, Body, Orig_nonterm, Orig_body)
	;   add_range(Low, High, Nonterm, Body, Orig_nonterm, Orig_body)
	).


add_catchall(Nonterm, Body, Orig_nonterm, Orig_body) :-
	(   clause(catchall_rule(Nonterm, _), true)
	->  throw(multiple_catcall_rules(Orig_nonterm, Orig_body))
	;   assert(catchall_rule(Nonterm, Body))
	).

add_individual(Char, Nonterm, Body, Orig_nonterm, Orig_body) :-
	(   clause(nonterm_rule(Char, Nonterm, Oldbody), true, Ref)
	->  left_factor(Nonterm, Char, Char, Oldbody, Ref, Body,
			Orig_nonterm, Orig_body)
	;   assert(nonterm_rule(Char, Nonterm, Body))
	).

add_range(Low, High, Nonterm, Body, Orig_nonterm, Orig_body):-
	(   clause(range_rule(Nonterm, Low0, High0, Oldbody), true, Ref),
	    Low0 =< High, Low =< High0
	->  % New range overlaps old one: split into consistent ranges
	    CommonLo is max(Low0, Low),
	    Below_common is CommonLo - 1,
	    CommonHi is min(High0, High),
	    Above_common is CommonHi + 1,
	    left_factor(Nonterm, CommonLo, CommonHi, Oldbody, Ref, Body,
			Orig_nonterm, Orig_body),
	    % At most one of these two will do anything
	    add_grammar_clause1(Low0, Below_common, Nonterm, Oldbody,
				Orig_nonterm, Orig_body),
	    add_grammar_clause1(Low, Below_common, Nonterm, Body,
				Orig_nonterm, Orig_body),
	    % At most one of these two will do anything
	    add_grammar_clause1(Above_common, High0, Nonterm, Oldbody,
				Orig_nonterm, Orig_body),
	    add_grammar_clause1(Above_common, High, Nonterm, Body,
				Orig_nonterm, Orig_body)
	;   % No overlap:  just record it
	    assert(range_rule(Nonterm, Low, High, Body))
	).




initial_body_range([Instr|Rest], Low, High, Body) :-
	initial_instr_range(Instr, Low, High, Rest, Body).


initial_instr_range(chars([Char|Chars]), Char, Char, Rest, Body) :-
	(   Chars == []
	->  Body = Rest
	;   Body = [chars(Chars)|Rest]
	).
initial_instr_range(pushchars([Char|Chars]), Char, Char, Rest,
		    [push(Char)|Body]) :-
	(   Chars == []
	->  Body = Rest
	;   Body = [chars(Chars)|Rest]
	).
initial_instr_range(range(Low,High), Low, High, Rest, Rest).
initial_instr_range(build(X,Y), 0, -1, Rest, [build(X,Y)|Rest]).
initial_instr_range(call(X,Y), 0, -1, Rest, [call(X,Y)|Rest]).



left_unfold(Body0, Parent, Body) :-
	left_unfold1(Body0, Body0, Parent, Body).

left_unfold1([First|Rest], Body0, Parent, Body) :-
	left_unfold2(First, Rest, Body0, Parent, Body).
left_unfold1([], _, _, []).

left_unfold2(chars(_), _, Body0, _, Body0).
left_unfold2(pushchars(Expected), Rest, _, Parent,
	     [pushchars(Expected)|Body]) :-
	left_unfold1(Rest, Rest, Parent, Body).
left_unfold2(token_end(_), _, Body0, _, _) :-
	throw(token_end_first(Body0)).
left_unfold2(range(_,_), _, Body0, _, Body0).
left_unfold2(nonterminal(Nonterm), Rest, Body0, Parent, Body) :-
	!,
	(   Nonterm == Parent		% left recursive!
	->  Body = Body0
	;   nonterm_rule(Ch, Nonterm, Body1),
	    append([chars([Ch])|Body1], Rest, Body)
	;   range_rule(Nonterm, Low, High, Body1),
	    append([range(Low,High)|Body1], Rest, Body)
	;   catchall_rule(Nonterm, Body1),
	    append(Body1, Rest, Body)
	;   Body = Body0		% undefined!
	).
left_unfold2(build(Id,Count), Rest, _, Parent, [build(Id,Count)|Body]) :-
	left_unfold1(Rest, Rest, Parent, Body).
left_unfold2(call(Pred,Count), Rest, _, Parent, [call(Pred,Count)|Body]) :-
	left_unfold1(Rest, Rest, Parent, Body).
left_unfold2(push(Char), Rest, _, Parent, [push(Char)|Body]) :-
	left_unfold1(Rest, Rest, Parent, Body).



left_factor(Nonterm, Low, High, Oldbody, Ref, Body, Orig_nonterm, Orig_body) :-
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
		add_grammar_clause1(Low, High, Nonterm, Commonbody,
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
token_chars(pushchars(Chs1), Chs1, pushchars(Chs2), Chs2).

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

