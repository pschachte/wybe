# Makefile for n queens benchmarks

SRCS = c_queens.c haskell_queens.hs	rust_queens.rs wybe_queens.wybe \
		wybe_queens_arr.wybe

EXES := $(shell echo $(SRCS) | sed 's/\.[a-z]*//g')

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