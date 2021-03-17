% For the generator:
% def {generator} int_seq(start: int, end: int, ?val: int) {
%    (start < end)
%
%    generate {
%        ?val = start
%    ||
%        ?val = start + 1
%    ||
%        int_seq(start + 2, end, ?val)
%    }
%
%    generate {
%        ?parity = 0
%    ||
%        ?parity = 1
%   }
%
%    ?val = val + parity + 1
%
% }
%
% Transliterated to Prolog:

int_seq(Start, End, Val) :-
        Start < End,
        (   Val0 = Start
        ;   Val0 is Start + 1
        ;   Start2 is Start + 2,
            int_seq(Start2, End, Val0)
        ),
        (   Parity = 0
        ;   Parity = 1
        ),
        Val is Val0 + Parity + 1.



test :- findall(X, int_seq(1, 10, X), L), length(L, Len),
        format('int_seq(1, 10) produces ~w solutions:~n',[Len]),
        maplist(writeln, L).
