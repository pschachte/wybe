# Makefile for nth prime benchmarks

EXES = c_prime c_prime_backwards haskell_prime rust_prime wybe_prime

all: $(EXES)

test: all
	rm -f BENCHMARKS
	../runbenchmarks.sh $(EXES)

clean:
	rm -f $(EXES) BENCHMARKS


%: %.c
	gcc -O3 -o $@ $<

haskell_prime: haskell_prime.hs
	ghc -O3 -o haskell_prime haskell_prime.hs

rust_prime: rust_prime.rs
	rustc -C opt-level=3 -o rust_prime rust_prime.rs

wybe_prime: wybe_prime.wybe
	wybemk wybe_prime


.PHONY: all clean test