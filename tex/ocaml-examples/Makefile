SRC := $(wildcard *.ml)
SRC_OUT := $(SRC:.ml=.out)

types.cmi: types.mli
	ocamlc -c types.mli

%.out: %.ml types.cmi
	@echo "Compiling $@"
	@ocamlc ${OCAMLFLAGS} -i $< 2>&1 || echo "Failed to typecheck"

all: $(SRC_OUT)

clean::
	rm types.cmi

