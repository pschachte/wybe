#  File     : Makefile
#  RCS      : $Id: Makefile,v 1.1 2003/03/30 13:43:53 schachte Exp $
#  Author   : Peter Schachte

VERSION=0.1

all:	test

%.pdf:	%.tex
	rubber -m pdftex $<

%.ps:	%.tex
	rubber -m dvips $<

%.hs:	%.y
	happy $<

frgc:	frgc.hs Parser.hs Scanner.hs Version.hs
	ghc --make $@

.PHONY: Version.hs

Version.hs:
	@rm -f $@
	@printf "{- Version.hs automatically generated:  DO NOT EDIT -}\n" > $@
	@printf "\n" >> $@
	@printf "module Version (version,buildDate) where\n" >> $@
	@printf "version :: String\nversion = \"%s\"\n" "$(VERSION)" >> $@
	@printf "buildDate :: String\nbuildDate = \"%s\"\n" "`date`" >> $@

TESTCASES = $(wildcard test-cases/*.frg)

test:	frgc
	@for f in $(TESTCASES) ; do \
	    printf "%-40s ... " $$f ; \
	    out=`echo "$$f" | sed 's/.frg$$/.out/'` ; \
	    exp=`echo "$$f" | sed 's/.frg$$/.exp/'` ; \
	    ./frgc -v $$f > $$out 2>&1 ; \
	    diff -q $$exp $$out >/dev/null && echo "PASS" ; \
	    diff -q $$exp $$out >/dev/null || echo "FAIL" ; \
	done