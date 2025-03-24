#import "@preview/ctheorems:1.1.3": *

#let theorem = thmbox(
  "theorem",
  "Theorem",
  bodyfmt: body => [
    #set align(left)
    #body
  ],
)
#let lemma = thmbox(
  "lemma",
  "Lemma",
  bodyfmt: body => [
    #set align(left)
    #body
  ],
)
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong,
  bodyfmt: body => [
    #set align(left)
    #body
  ],
)
#let definition = thmbox(
  "definition",
  "Definition",
  inset: (x: 1.2em, top: 1em),
)

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#show: thmrules
