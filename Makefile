STY-SRC  := freespec.sty speccert.sty
BIB-SRC  := manuscript.bib
TEX-SRC  := Chapters/Introduction.tex \
            Chapters/UseCase.tex      \
            Chapters/RelatedWorks.tex \
            Chapters/SpecCert.tex     \
            Chapters/FreeSpec.tex
ABSTRACT := abstract.tex

default: minimal

minimal: main-mini.pdf
full: main.pdf

%.pdf: %.tex ${STY-SRC} ${BIB-SRC} ${ABBREV} ${TEX-SRC} ${ABSTRACT}
	pdflatex $<
	bibtex $*
	pdflatex $<
	pdflatex $<

clean:
	rm -f main*.aux
	rm -f main*.bbl
	rm -f main*.blg
	rm -f main*.log
	rm -f main*.toc
	rm -f main*.out

.PHONY: minimal main default clean
