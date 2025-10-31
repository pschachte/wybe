# Makefile for nrev benchmarks

EXES = c_nrev c_nrev_destr c_nrev_fast \
		hs_nrev \
		rust_nrev rust_nrev_destr \
		wybe_nrev

REPETITIONS = 9

all: $(EXES)

test: all
	rm -f BENCHMARKS
	./runbenchmarks.sh $(EXES)

clean:
	rm -f $(EXES) BENCHMARKS


c_nrev: c_nrev.c
	gcc -O3 -lgc -o c_nrev c_nrev.c

c_nrev_imp: c_nrev_imp.c
	gcc -O3 -lgc -o c_nrev_imp c_nrev_imp.c

c_nrev_destr: c_nrev_destr.c
	gcc -O3 -lgc -o c_nrev_destr c_nrev_destr.c

c_nrev_fast: c_nrev_fast.c
	gcc -O3 -o c_nrev_fast c_nrev_fast.c

hs_nrev: hs_nrev.hs
	ghc -O3 -o hs_nrev hs_nrev.hs

rust_nrev: rust_nrev.rs
	rustc -C opt-level=3 -o rust_nrev rust_nrev.rs

rust_nrev_destr: rust_nrev_destr.rs
	rustc -C opt-level=3 -o rust_nrev_destr rust_nrev_destr.rs

wybe_nrev: wybe_nrev.wybe
	wybemk wybe_nrev


.PHONY: all clean test