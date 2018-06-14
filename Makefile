STY-SRC  := freespec.sty speccert.sty phdcmd.sty
BIB-SRC  := manuscript.bib
TEX-SRC  := $(wildcard Chapters/*.tex)    \
            $(wildcard Appendices/*.tex)  \
            abbrev.tex                    \
            nomencl.tex                   \
            abstract.tex                  \
            notation.tex
COQ      := $(wildcard Listings/*.v)
NUSMV    := $(wildcard Listings/*.nusmv)

default: main.pdf

%.pdf: %.tex ${STY-SRC} ${BIB-SRC} ${TEX-SRC} ${COQ} ${NUSMV}
	latexmk $< -shell-escape -pdf

clean:
	rm -f main*.aux
	rm -f main*.bbl
	rm -f main*.blg
	rm -f main*.log
	rm -f main*.toc
	rm -f main*.out
	rm -f main*.idx
	rm -f main*.ind
	rm -f main*.pdf
	rm -f Listings/.*.aux
	rm -f Listings/*.glob
	rm -f Listings/*.vo

coq:
	coqc Listings/Airlock.v
	coqc Listings/SpecCert.v

.PHONY: minimal main default clean coq
