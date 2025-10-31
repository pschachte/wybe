# Makefile for n queens benchmarks

EXES = haskell_queens \
		wybe_queens

all: $(EXES)

test: all
	rm -f BENCHMARKS
	../runbenchmarks.sh $(EXES)

clean:
	rm -f $(EXES) BENCHMARKS


c_queens: c_queens.c
	gcc -O3 -lgc -o c_queens c_queens.c

c_queens_imp: c_queens_imp.c
	gcc -O3 -lgc -o c_queens_imp c_queens_imp.c

c_queens_destr: c_queens_destr.c
	gcc -O3 -lgc -o c_queens_destr c_queens_destr.c

c_queens_fast: c_queens_fast.c
	gcc -O3 -o c_queens_fast c_queens_fast.c

haskell_queens: haskell_queens.hs
	ghc -O3 -o haskell_queens haskell_queens.hs

rust_queens: rust_queens.rs
	rustc -C opt-level=3 -o rust_queens rust_queens.rs

rust_queens_destr: rust_queens_destr.rs
	rustc -C opt-level=3 -o rust_queens_destr rust_queens_destr.rs

wybe_queens: wybe_queens.wybe
	wybemk wybe_queens


.PHONY: all clean test