# Makefile for Wybe documentation

USERDOC=wybe.pdf wybe.html
DEVDOC=compiler.html design.html lpvm.html

.PHONY:	all
all:	$(USERDOC) $(DEVDOC)

%.html:	%.md
	markdown $< >$@

%.html:	%.tex
	hevea -o $@ $<

%.pdf:	%.tex
	pdflatex $<
