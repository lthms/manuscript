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

default: fast

fast:
	@echo -en "\e[33m[ ] Compiling\e[0m"
	@./.build.sh
	@echo -en "\r\e[32m[*] Compiling\e[0m"

latexmk:
	latexmk main.tex -shell-escape -pdf -quiet

%.pdf: %.tex ${STY-SRC} ${BIB-SRC} ${TEX-SRC} ${COQ} ${NUSMV}
	@echo -en "\e[33m[ ] Compiling (1/4)\e[0m"
	@./.build.sh
	@echo -en "\r\e[33m[ ] Bibtex    (2/4)\e[0m"
	@bibtex main > /dev/null
	@echo -en "\r\e[33m[ ] Compiling (3/4)\e[0m"
	@./.build.sh
	@echo -en "\r\e[33m[ ] Compiling (4/4)\e[0m"
	@./.build.sh
	@echo -e "\r\e[32m[*] Compiling      \e[0m"

force: clean main.pdf

clean:
	@echo -en "\e[33m[ ] Removing auxiliary files\e[0m"
	@rm -f main*.aux
	@rm -f main*.bbl
	@rm -f main*.blg
	@rm -f main*.log
	@rm -f main*.toc
	@rm -f main*.out
	@rm -f main*.idx
	@rm -f main*.ind
	@rm -f main*.pdf
	@rm -f Listings/.*.aux
	@rm -f Listings/*.glob
	@rm -f Listings/*.vo
	@echo -e "\r\e[32m[*] Removing auxiliary files\e[0m"

coq:
	coqc Listings/Airlock.v
	coqc Listings/SpecCert.v

.PHONY: minimal main default clean coq force fast latexmk

YELLOW  := "\e[33m"
DEFAULT := "\e[0m"
