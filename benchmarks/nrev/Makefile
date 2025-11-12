# Makefile for nrev benchmarks

SRCS = c_nrev.c c_nrev_destr.c c_nrev_fast.c \
		haskell_nrev.hs \
		rust_nrev.rs rust_nrev_destr.rs \
		wybe_nrev.wybe

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


c_nrev: c_nrev.c
	gcc -O3 -lgc -o c_nrev c_nrev.c

c_nrev_imp: c_nrev_imp.c
	gcc -O3 -lgc -o c_nrev_imp c_nrev_imp.c

c_nrev_destr: c_nrev_destr.c
	gcc -O3 -lgc -o c_nrev_destr c_nrev_destr.c

c_nrev_fast: c_nrev_fast.c
	gcc -O3 -o c_nrev_fast c_nrev_fast.c

haskell_nrev: haskell_nrev.hs
	ghc -O3 -o haskell_nrev haskell_nrev.hs

rust_nrev: rust_nrev.rs
	rustc -C opt-level=3 -o rust_nrev rust_nrev.rs

rust_nrev_destr: rust_nrev_destr.rs
	rustc -C opt-level=3 -o rust_nrev_destr rust_nrev_destr.rs

wybe_nrev: wybe_nrev.wybe
	wybemk wybe_nrev


.PHONY: all clean test stats