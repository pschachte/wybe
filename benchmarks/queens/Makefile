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


c_queens: c_queens.c
	gcc -O3 -lgc -o c_queens c_queens.c

haskell_queens: haskell_queens.hs
	ghc -O3 -o haskell_queens haskell_queens.hs

rust_queens: rust_queens.rs
	rustc -C opt-level=3 -o rust_queens rust_queens.rs

wybe_queens: wybe_queens.wybe
	wybemk wybe_queens

wybe_queens_arr: wybe_queens_arr.wybe
	wybemk wybe_queens_arr


.PHONY: all clean test stats