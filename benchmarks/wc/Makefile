# Makefile for word count benchmarks

SRCS = c_wc.c haskell_wc.hs	haskell_wc_efficient.hs	rust_wc.rs wybe_wc.wybe

EXES := $(shell echo $(SRCS) | sed 's/\.[a-z]*//g') $(which wc)

STATFILE := $(shell basename $(shell pwd))-stats.tex

all: $(EXES)

test:  $(STATFILE)

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