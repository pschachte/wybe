


gen(N0, Max, N) :- N0 < Max, gen2(P), N is N0 + P + 1.
gen(N0, Max, N) :- N0 < Max, gen2(P), N is N0 + P + 2.
gen(N0, Max, N) :- N0 < Max, T is N0 + 2, gen(T, Max, N1), gen2(P), N is N1 + P + 1.

gen2(0).
gen2(1).

findall(X, gen(7, 10, X), L), length(L, Len).
