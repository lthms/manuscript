STY-SRC  := freespec.sty speccert.sty phdcmd.sty
BIB-SRC  := manuscript.bib
TEX-SRC  := $(wildcard Chapter/*.tex)     \
            $(wildcard Appendices/*.tex)  \
            abbrev.tex                    \
            nomencl.tex                   \
            abstract.tex
LISTINGS := $(wildcard Listings/*.v)      \
            $(wildcard Listings/*.nusmv)

default: minimal

minimal: main-mini.pdf jury.pdf
full: main.pdf

%.pdf: %.tex ${STY-SRC} ${BIB-SRC} ${TEX-SRC} ${LISTINGS}
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

.PHONY: minimal main default clean
