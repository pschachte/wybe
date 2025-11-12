# Makefile for nth prime benchmarks

SRCS = c_prime.c c_prime_backwards.c \
		haskell_prime.hs \
		rust_prime.rs \
		wybe_prime.wybe wybe_prime_arr.wybe

EXES := $(shell echo $(SRCS) | sed 's/\.[a-z]*//g')

STATFILE := $(shell basename $(shell pwd))-stats.tex

all: $(EXES)

test:	BENCHMARKS

stats:	$(STATFILE)

BENCHMARKS:	$(EXES)
	rm -f BENCHMARKS
	../runbenchmarks.sh $(EXES)

$(STATFILE): BENCHMARKS
	../exestats.sh $(SRCS) > $(STATFILE)

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


.PHONY: all clean test stats