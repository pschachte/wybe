#  File     : Makefile
#  RCS      : $Id: Makefile,v 1.1 2003/03/30 13:43:53 schachte Exp $
#  Author   : Peter Schachte

VERSION=0.1
# OPTS = -no-user-package-db -package-db .cabal-sandbox/*-packages.conf.d
COPTS = -lgc -I/usr/local/include -L/usr/local/lib

all:	wybemk

%.pdf:	%.tex
	rubber -m pdftex $<

%.hs:	%.y
	happy -a -g $<

wybemk:	*.hs Version.lhs Parser.hs *.c
	cabal build -j3 $@
	# clang -fPIC -shared cbits.c -o cbits.so $(COPTS) 2>/dev/null
	# ghc -fwarn-incomplete-patterns --make $@

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

# On Mac OS X, gtimeout is in homebrew coreutils package
test:	wybemk
	@rm -f ERRS ; touch ERRS
	@rm -f test-cases/*.bc
	@rm -f test-cases/*.o
	@rm -f wybelibs/*.o
	@printf "Testing building wybe library..."
	@gtimeout 2 ./wybemk --force-all --no-std wybelibs/wybe.o
	@printf "Done.\n"
	@printf "Testing test-cases "
	@ time ( for f in $(TESTCASES) ; do \
	    out=`echo "$$f" | sed 's/.wybe$$/.out/'` ; \
	    log=`echo "$$f" | sed 's/.wybe$$/.log/'` ; \
	    exp=`echo "$$f" | sed 's/.wybe$$/.exp/'` ; \
	    targ=`echo "$$f" | sed 's/.wybe$$/.o/'` ; \
	    gtimeout 2 ./wybemk --log=FinalDump $(DEBUG) --force-all $$targ \
		> $$out 2> $$log ; \
	    if [ ! -r $$exp ] ; then \
		printf "[31m?[39m" ; \
		NEW="$${NEW}\n    $$out" ; \
	    elif diff -q $$exp $$out >/dev/null 2>&1 ; then \
		printf "." ; \
	    else \
		printf "\n[34;1m**************** difference building $$targ ****************[0m\n" >> ERRS ; \
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
	rm -f *.o *.hi Parser.hs Version.lhs *.pdf *.aux wybelibs/*.o test-cases/*.o
