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

TESTCASES = $(wildcard test-cases/*.frg)

test:
	for f in $(TESTCASES) ; do \
	    printf "%-40s ... " $$f ; \
	    out=`echo "$$f" | sed 's/.frg$$/.out/'` ; \
	    exp=`echo "$$f" | sed 's/.frg$$/.exp/'` ; \
	    ./frg < $$f > $$out ; \
	    diff -q $$exp $$out >/dev/null && echo "PASS" ; \
	    diff -q $$exp $$out >/dev/null || echo "FAIL" ; \
	done