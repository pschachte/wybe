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