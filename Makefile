#  File     : Makefile
#  RCS      : $Id: Makefile,v 1.1 2003/03/30 13:43:53 schachte Exp $
#  Author   : Peter Schachte

VERSION=0.1

all:	test

%.pdf:	%.tex
	rubber -m pdftex $<

%.hs:	%.y
	happy -a -g $<

wybemk:	*.hs Version.lhs Parser.hs
	ghc -fwarn-incomplete-patterns --make $@

.PHONY:	info

info:  Parser.info

%.info:	%.y
	happy -i -a -g $<

doc:	*.hs
	rm -rf $@
	haddock -h -o $@ *.hs

Version.lhs:	*.hs
	@echo "Generating Version.lhs for version $(VERSION)"
	@rm -f $@
	@printf "Version.lhs automatically generated:  DO NOT EDIT\n" > $@
	@printf "\n" >> $@
	@printf "> module Version (version,buildDate) where\n" >> $@
	@printf "> version :: String\n> version = \"%s\"\n" "$(VERSION)" >> $@
	@printf "> buildDate :: String\n> buildDate = \"%s\"\n" "`date`" >> $@

TESTCASES = $(wildcard test-cases/*.wybe)
#DEBUG=--log=Unbranch

test:	wybemk
	@rm -f ERRS ; touch ERRS
	@printf "testing"
	@ time ( for f in $(TESTCASES) ; do \
	    out=`echo "$$f" | sed 's/.wybe$$/.out/'` ; \
	    log=`echo "$$f" | sed 's/.wybe$$/.log/'` ; \
	    exp=`echo "$$f" | sed 's/.wybe$$/.exp/'` ; \
	    targ=`echo "$$f" | sed 's/.wybe$$/.o/'` ; \
	    ./wybemk --log=FinalDump $(DEBUG) -f $$targ > $$out 2> $$log ; \
	    if [ ! -r $$exp ] ; then \
		printf "[31m?[39m" ; \
		NEW="$${NEW}\n    $$out" ; \
	    elif diff -q $$exp $$out >/dev/null 2>&1 ; then \
		printf "." ; \
	    else \
		dwdiff -c -d '()<>~!@:?.%#' $$exp $$out >> ERRS 2>&1 ; \
		printf "[31mX[39m" ; \
		FAILS="$${FAILS}\n    $$out" ; \
	    fi \
	done ; \
	echo ; \
	if [ -n "$$FAILS" ] ; \
	    then echo "Failed: $$FAILS\nSee ERRS for differences." ; \
	    else echo "ALL TESTS PASS" ; rm -f ERRS ; \
	fi ; \
	if [ -n "$$NEW" ] ; \
	    then echo "New tests: $$NEW\nDo .\update-exp to specify expected output" ; \
	fi )

clean:
	rm -f *.o *.hi Parser.hs Version.lhs *.pdf *.aux
