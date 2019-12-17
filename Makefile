#  File     : Makefile
#  RCS      : $Id: Makefile,v 1.1 2003/03/30 13:43:53 schachte Exp $
#  Author   : Peter Schachte

VERSION=0.1
# OPTS = -no-user-package-db -package-db .cabal-sandbox/*-packages.conf.d
COPTS = -lgc -I/usr/local/include -L/usr/local/lib
SRCDIR = src
LIBDIR = wybelibs

all:	wybemk

%.pdf:	%.tex
	rubber -m pdftex $<

$(LIBDIR)/cbits.o: $(LIBDIR)/cbits.c
	clang -isysroot `xcrun --show-sdk-path` -I /usr/local/include -c $< -o $@

wybemk:	$(SRCDIR)/*.hs $(SRCDIR)/Version.lhs $(LIBDIR)/cbits.o
	stack install && cp ~/.local/bin/$@ ./$@


doc:	*.hs
	rm -rf $@
	haddock -h -o $@ *.hs

$(SRCDIR)/Version.lhs:	*.hs
	@echo "Generating Version.lhs for version $(VERSION)"
	@rm -f $@
	@printf "Version.lhs automatically generated:  DO NOT EDIT\n" > $@
	@printf "\n" >> $@
	@printf "> module Version (version,buildDate) where\n" >> $@
	@printf "> version :: String\n> version = \"%s\"\n" "$(VERSION)" >> $@
	@printf "> buildDate :: String\n> buildDate = \"%s\"\n" "`date`" >> $@

TESTCASES = $(wildcard test-cases/*.wybe)

# Assemble README markdown source file automatically
src/README.md: src/*.hs Makefile src/README.md.intro src/README.md.outro
	cat src/README.md.intro > $@

	printf "The source files in this directory and their purposes are:\n\n" >> $@
	printf "| File                         " >> $@
	printf "| Purpose                                                  |\n" >> $@
	printf "| ---------------------------- " >> $@
	printf "| -------------------------------------------------------- |\n" >> $@
	for f in src/*.hs ; do \
      b=`basename $$f` ; \
      m=`basename $$f .hs` ; \
	    printf "| `printf '%-29s' [$$b]\(#$$m\)`| " ; \
	    sed -n "s/^-- *Purpose *: *\(.*\)/\1/p" $$f | tr -d '\n' ; \
	    printf " |\n" ; \
	done >> $@
	printf "\n\n# Modules in more detail\n\n" >> $@

	for f in src/*.hs ; do \
      m=`basename $$f .hs` ; \
	    printf "\n## %s\n" $$m ; \
	    echo ; \
	    sed -E -e '/^-- *Purpose *:/{s/^-- *Purpose *:/**Purpose**:/; G; p;}' -e '/BEGIN MAJOR DOC/,/END MAJOR DOC/{//d ; s/^-- ? ?//p;}' -e 'd' <$$f ; \
	done >> $@

	printf "\n\n" >> $@
	cat src/README.md.outro >> $@


# On Mac OS X, gtimeout is in homebrew coreutils package
test:	wybemk
	@rm -f ERRS ; touch ERRS
	@rm -f test-cases/*.bc
	@rm -f test-cases/*.o
	@rm -f $(LIBDIR)/*.o
	@echo "Building $(LIBDIR)/cbits.o"
	@make $(LIBDIR)/cbits.o
	@printf "Testing building wybe library ("
	@printf wybe
	@gtimeout 5 ./wybemk --force-all $(LIBDIR)/wybe.o
	@for f in $(LIBDIR)/*.wybe ; do \
           [ "$$f" = "$(LIBDIR)/wybe.wybe" ] && continue ; \
	   printf " %s" `basename $$f .wybe` ; \
	   gtimeout 2 ./wybemk --force $${f/.wybe/.o} ; \
	done
	@printf ") done.\n"
	@printf "Testing test-cases "
	@ time ( for f in $(TESTCASES) ; do \
		out=`echo "$$f" | sed 's/.wybe$$/.out/'` ; \
		exp=`echo "$$f" | sed 's/.wybe$$/.exp/'` ; \
		targ=`echo "$$f" | sed 's/.wybe$$/.o/'` ; \
		gtimeout 2 ./wybemk --log=FinalDump $(DEBUG) --force-all $$targ 2>&1 \
	  | sed 's/@wybe:[0-9:]*/@wybe:nn:nn/g' > $$out ; \
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
	stack clean
	rm -f $(SRCDIR)/*.o $(SRCDIR)/*.hi Parser.hs $(SRCDIR)/Version.lhs *.pdf *.aux $(LIBDIR)/*.o test-cases/*.o
