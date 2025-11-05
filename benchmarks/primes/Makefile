# Makefile for nth prime benchmarks

EXES = c_primes haskell_primes rust_primes wybe_primes

all: $(EXES)

test: all
	rm -f BENCHMARKS
	../runbenchmarks.sh $(EXES)

clean:
	rm -f $(EXES) BENCHMARKS


c_primes: c_primes.c
	gcc -O3 -lgc -o c_primes c_primes.c

haskell_primes: haskell_primes.hs
	ghc -O3 -o haskell_primes haskell_primes.hs

rust_primes: rust_primes.rs
	rustc -C opt-level=3 -o rust_primes rust_primes.rs

wybe_primes: wybe_primes.wybe
	wybemk wybe_primes


.PHONY: all clean test