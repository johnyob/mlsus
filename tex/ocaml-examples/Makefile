types.cmi: types.mli
	ocamlc -c types.mli

%.out: %.ml types.cmi
	@ocamlc ${OCAMLFLAGS} -i $< 2>&1

clean::
	rm types.cmi

