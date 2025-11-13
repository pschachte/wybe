# Makefile for nth prime benchmarks

SRCS = c_prime.c haskell_prime.hs rust_prime.rs wybe_prime.wybe \
		haskell_prime_nonlazy

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

%: %.hs
	ghc -O3 -o $@ $<

%: %.rs
	rustc -C opt-level=3 -o $@ $<

%: %.wybe
	wybemk $@


.PHONY: all clean test stats