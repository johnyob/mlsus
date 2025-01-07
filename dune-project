(lang dune 3.10)

(using menhir 2.1)

(name mlsus)

(source
 (github johnyob/mlsus))

(authors "Alistair O'Brien")

(maintainers "ajo41@cam.ac.uk")

(license GPL-3.0-only)

(generate_opam_files true)

(package
 (name mlsus)
 (depends ocaml dune core core_unix async ppx_jane fmt menhir grace))
