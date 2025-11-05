# Makefile for nth prime benchmarks

EXES = wybe_prime
# c_prime haskell_prime rust_prime

all: $(EXES)

test: all
	rm -f BENCHMARKS
	../runbenchmarks.sh $(EXES)

clean:
	rm -f $(EXES) BENCHMARKS


c_prime: c_prime.c
	gcc -O3 -lgc -o c_prime c_prime.c

haskell_prime: haskell_prime.hs
	ghc -O3 -o haskell_prime haskell_prime.hs

rust_prime: rust_prime.rs
	rustc -C opt-level=3 -o rust_prime rust_prime.rs

wybe_prime: wybe_prime.wybe
	wybemk wybe_prime


.PHONY: all clean test