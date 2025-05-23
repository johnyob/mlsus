PRJ = suspended

LATEXMK = latexmk -pdf -outdir=_build -auxdir=_build

SOURCES=$(shell find . -name '*.tex' -or -name '*.bib' -or -name '*.sty')

all: $(addsuffix .pdf,${PRJ})

.PRECIOUS: %.pdf

%.pdf: %.tex ${SOURCES}
	@mkdir -p _build
	$(LATEXMK) $< || (cp _build/$@ . && false)
	cp _build/$@ .

%.wpdf: %.tex ${SOURCES}
	$(LATEXMK) -pvc $<

%.view: %.pdf
	open $< &

clean:
	rm -rf _build

vacuum: clean
	rm -f suspended.pdf



