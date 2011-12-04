#  File     : Makefile
#  RCS      : $Id: Makefile,v 1.1 2003/03/30 13:43:53 schachte Exp $
#  Author   : Peter Schachte

all:	frg

%.pdf:	%.tex
	rubber -m pdftex $<

%.ps:	%.tex
	rubber -m dvips $<

%.hs:	%.y
	happy $<

frg:	Parser.hs Scanner.hs
	ghc -o $@ --make Parser.hs

TESTOUTS = $(patsubst %.frg,%.out,$(wildcard test-cases/*.frg))

%.out:	%.frg frg
	./frg < $< > $@

test:
	for f in $(TESTOUTS) ; do \
	    printf "%-40s ... " $$f ; \
	    ./frg < $$f > $(patsubst %.frg,%.out,$$f) ; \
	    diff -q $$f $(patsubst %.frg,%.out,$$f) && echo "PASS" ; \
	    diff -q $$f $(patsubst %.frg,%.out,$$f) || echo "FAIL" ; \
	done