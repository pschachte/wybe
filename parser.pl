%  File     : parser.pl
%  RCS      : $Id: parser.pl,v 1.1 2008/03/13 12:44:26 schachte Exp $
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


% We keep track of nonterminals used but undefined, for error reporting.
:- dynamic undef_nonterm/1.
undef_nonterm(item).


% add_production(Nonterm, Body)

add_production(Nonterm, Body) :-
	add_production1(Body, Nonterm).

add_production1((B1;B2), Nonterm) :-
	add_production1(B1, Nonterm),
	add_production1(B2, Nonterm).
add_production1(Body, Nonterm) :-
	first_set(Body, Firsts),
	
	
