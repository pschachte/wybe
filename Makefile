#  File     : Makefile
#  RCS      : $Id: Makefile,v 1.1 2003/03/30 13:43:53 schachte Exp $
#  Author   : Peter Schachte


DVIPS=dvips
DOT=dot
FIG2DEV=fig2dev
TOHTML=latex2html -no_subdir -info "" -split 0 -no_navigation
TWOUP=../format-handout
MV=mv
ONLY=
# This complication is here because fig2dev 3.2 patch 1 and earlier do not 
# recognize target language 'eps', you you have to use 'ps', and later
# versions generate wrong encapsulated postscript if you say 'ps'
FIG2DEV=fig2dev -L $(if $(findstring 3.2 Patchlevel 1,$(shell fig2dev -V 2>&1)),ps,eps)
FIGDIR=FIG/
TEXDEP=../texdep
EXECPRESERVING=../exec-preserving
PS2PDF=ps2pdf
LATEX=

.SUFFIXES:
.PRECIOUS:	TEXDEP/%.tdep
.PHONY:		%.depend

TEXDEP/MASTER:
	-mkdir TEXDEP
	touch $@

TEXDEP/%.tdep:	%.tex
	$(TEXDEP) -d TEXDEP $<

include TEXDEP/MASTER

%.depend:	%.tex
		-rm TEXDEP/$(basename $@).tdep
		$(MAKE) TEXDEP/$(basename $@).tdep

$(WEBDIR)/%:	%
	cp $< $@
	chmod 664 $@

%.dvi:	%.tex TEXDEP/%.tdep
	$(EXECPRESERVING)  -f -p $*.aux -r $*.aux latex $<

%.INCLUDEONLY.tex:
	echo "% include everything" > $@

%.html:	%.tex
	$(TOHTML) $<

%.ps:	%.dvi
	$(DVIPS) -o $@ $<

%.ps:	%.dot
	$(DOT) -Tps $< -o $@

%.eps:	%.fig
	$(FIG2DEV) $< $@

%.pdf:	%.ps
	$(PS2PDF) $< $@
