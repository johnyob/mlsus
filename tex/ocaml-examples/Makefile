SRC := $(wildcard *.ml)
SRC_OUT := $(SRC:.ml=.out)

OCAMLFLAGS = -principal -w +41


default: suspended.ok
all: suspended.err



types.cmi: types.mli
	ocamlc -c types.mli



%.out: %.ml types.cmi
	@echo "Compiling $@"
	@ocamlc ${OCAMLFLAGS} -i $< 2>&1 || echo "Failed to typecheck"

suspended.cml: ../suspended.tex Makefile
	cat $< | \
	gsed -n -e '/\\begin{program}[[].*check.*[]]/,/\\end{program}/p' | \
	gsed -e '/\\begin{program}/d' -e '/\\end{program}/d' | \
	gsed -e 's/.\\ocamlflags *\([0-9]\)[0-9]. */  (*=\1=*)/' | \
	gsed -e 's/[$$]$$//' -e 's/^[$$]//' | \
	gsed -e 's/°[^°]*°//' \
	     -e 's/[$$][^$$]*[$$]//' \
	     -e 's/_\([0-9]\)/\1/g' | \
	cat > $@
	echo 'let _end_ = ()' >> $@

suspended.all: suspended.cml Makefile
	cat $< | \
	gsed -n -e 's/^let \([a-z][a-z_0-9]*\).*/\1.cml/p' | \
	cat > $@

.PRECIOUS: %.cml
.PRECIOUS: %.cmli

%.cml: suspended.cml Makefile
	echo 'open Types' > $@
	PAT="let $(shell basename $@ .cml) "; \
	cat suspended.cml | \
	gsed -e  "0,/^$${PAT}/s/^$${PAT}/#$${PAT}/" | \
	gsed -n -e  "/#$${PAT}/,/^let /p" | \
	gsed -e  's/^#//' -e  '$$d' | \
	cat >> $@|| (rm $i && false)

CML = $(shell cat suspended.all)

%.cmli: %.cml types.cmi
	@if ocamlc ${OCAMLFLAGS} -i -impl $< > $@ 2>&1; \
	then if grep Warning $@; \
		then gecho -n  Warning; \
		else gecho -n '     OK'; \
	     fi; \
	else gecho -n ' FAILED'; fi  >> $@
	cat $< | \
	gsed -n -e 's/.*=\([0-9]\)=.*/ --  \1/p' | \
	gsed  -e 's/0/Green/' -e 's/1/Red/' -e 's/2/Orange/' >> $@

%!: %
	cat $<

DR = $(HOME)/ocaml/lang/semiun/su/_build/default/src/main.exe
%.oml: %.cml
	cat types.mli $< | grep -v 'open' > $@

%.omli: %.oml
	$(DR) $<

# all: $(SRC_OUT)

suspended.flags: suspended.all $(CML) $(CML:.cml=.cmli)
	for i in $(CML:.cml=.cmli); \
	do gecho -n $$i':	 '; tail -1 $$i; done > $@

suspended.err: suspended.flags
	sed -e '/OK.*Green/d' \
	    -e '/Warning.*Orange/d' \
	    -e '/FAILED.*Red/d'\
	< $< > $@

suspended.ok: suspended.err
	if test -s $<; then cat $< && false; else touch $@; fi


all: suspended.err


clean::
	rm -f *.cml*
	rm types.cmi
