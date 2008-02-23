%  File     : nondet.pl
%  RCS      : $Id: nondet.pl,v 1.1 2008/02/24 05:43:11 schachte Exp $
%  Author   : Peter Schachte
%  Origin   : Sat Feb 23 12:35:32 2008
%  Purpose  : Transform nondeterministic code into (semi-)det code
%  Copyright: © 2008 Peter Schachte.  All rights reserved.
%

:- module(nondet, [
   ]).


/****************************************************************

			     The Transformation

The basis of the transformation is that a nondeterministic predicate is
transformed into a predicate that is called repeatedly to yield its multiple
solutions.  Extra args are introduced to keep track of which solution should
be returned next.  For example:

	vowel(a).
	vowel(e).
	vowel(i).
	vowel(o).
	vowel(u).

is transformed to:

	vowel_1(cl01, cl02, a).
	vowel_1(cl02, cl03, e).
	vowel_1(cl03, cl04, i).
	vowel_1(cl04, cl05, o).
	vowel_1(cl05, cl06, u).

A goal like

	:- vowel(X), test(X).

(where test/1 is semidet) is transformed to a loop that repeatedly calls
vowel_1/3:

	:- goal(cl01, X).

	goal(N, X) :-
		vowel_1(N, N1, X0),
		(   test(X)
		->  X = X0
		;   goal(N1, X)
		).

Naturally, deterministic code does not need to be transformed this way, but
since determinism depends on the mode the code is used in, this
transformation is mode-dependent.  The above example is for the out mode of
vowel/1.  The in mode would switch on its input to decide success or failure.

A more complicated example:

	member(X, tr(L,_,_)) :- member(X, L).
	member(X, tr(_,X,_)).
	member(X, tr(_,_,R)) :- member(X, R).

For the in-in (semi-det) mode, this is transformed to:

	member_1(X, tr(L,Y,R)) :-
		(   member_1(X, L)
		->  true
		(   X = Y
		->  true
		;   member_1(X, R)
		).

For the out-in mode, it is transformed to:

	member_2(cl01, Next, X, T) :-
		member_2(cl01a(cl01), Next, X, T).
	member_2(cl01a(N0), Next, X, T) :-
		T = tr(L,_,_),
		(   member_2(N0, N1, X, L)
		->  Next = cl01a(N1)
		;   member_2(cl02, Next, X, L)
		).
	member_2(cl02, cl03, X, tr(_,X,_)).
	member_2(cl03, Next, X, T) :-
		member_2(Cl03a(cl01), Next, X, T).
	member_2(cl03a(N0), Next, X, T) :-
		T = tr(_,_,R),
		member_2(N0, N1, X, R),
		Next = cl03a(N1).


****************************************************************/

