# *n* Queens benchmarks

Find a way to place *n* queens on an *n*x*n* chess board so that no queen
attacks any other queen.  That is, there can only be one queen in each row,
column, and diagonal on the board.

The algorithm used in all of these implementations represents the queen in each
row by the column it appears in.  A board is represented by a list or array
(whichever is more idiomatic in that language) of the column of the queen in
each row, numbered from 0 to n-1.  This representation guarantees that each
queen appears in a different row, and that each row has a queen.  We ensure each
queen appears in a different column by never using the same column number in two
rows.  We ensure no two queens appear in the same diagonal by checking that no
two queens have the same sum or difference of their row and column numbers.

The algorithm uses recursion to search for a solution; for each row, we try to
find a column for the queen that doesn't clash with a queen we have placed
earlier.  If we succeed, we add the queen in that column and recursively try to
place the rest of the queens in the extended board.  If not, we have failed to
place a queen in that row with that board.  When our recursive attempt to add
the rest of the queens fails, we try to place the current queen in a later
column in the current row, failing if we cannot.  If we ultimately succeed, we
print out the resulting board.

The classic problem is 8 queens, but that runs too quickly to be a suitable
benchmark, so we test for 32 queens on a 32x32 board.
