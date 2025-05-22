PRJ = suspended

LATEXMK = latexmk -pdf 

SOURCES=$(shell find . -name '*.tex' -or -name '*.bib' -or -name '*.sty')

all: $(addsuffix .pdf,${PRJ})

%.pdf: %.tex ${SOURCES}
	$(LATEXMK) $<

%.view: %.pdf
	open $< &

clean:
	rm -rf *.toc *.aux $(addsuffix .bbl,${PRJ}) *.blg *.log *~* *.bak *.out $(addsuffix .pdf,${PRJ}) cut.sh .latexrun.db* *.fls *.rel _region_.* *.synctex.gz *.fdb_latexmk *.ist *.glo