# Makefile for nrev benchmarks

SRCS = c_nrev.c haskell_nrev.hs rust_nrev.rs wybe_nrev.wybe \
		c_nrev_destr.c rust_nrev_destr.rs \
		c_nrev_fast.c		

EXES := $(shell echo $(SRCS) | sed 's/\.[a-z]*//g')

STATFILE := $(shell basename $(shell pwd))-stats.tex

all: $(EXES)

test:	BENCHMARKS

stats:	$(STATFILE)

BENCHMARKS:	$(EXES)
	rm -f BENCHMARKS
	../runbenchmarks.sh $(EXES)

$(STATFILE): BENCHMARKS
	../exestats.sh $(SRCS) > $@

clean:
	rm -f $(EXES) BENCHMARKS 


%: %.c
	gcc -O3 -lgc -o $@ $<

c_nrev_fast: c_nrev_fast.c
	gcc -O3 -o $@ $<

%: %.hs
	ghc -O3 -o $@ $<

%: %.rs
	rustc -C opt-level=3 -o $@ $<

%: %.wybe
	wybemk $@


.PHONY: all clean test stats