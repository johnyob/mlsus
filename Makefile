.DEFAULT_GOAL := all

.PHONY: all
all: build

.PHONY: install-ocamlformat
install-ocamlformat:
	opam install -y ocamlformat=0.26.2

.PHONY: install-deps
install-deps: install-switch install-ocamlformat
	opam install -y ocaml-lsp-server
	opam install -y --deps-only --with-test --with-doc .

.PHONY: install-switch
install-switch:
	opam switch create .

.PHONY: build
build:
	dune build

.PHONY: install
install: all 
	dune install --root .

.PHONY: test
test:
	dune runtest

.PHONY: clean
clean:
	dune clean

.PHONY: doc
doc:
	dune build @doc

.PHONY: watch
watch:
	dune build @run -w --force --no-buffer

.PHONY: utop
utop:
	dune utop