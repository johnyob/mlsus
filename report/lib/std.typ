
#let judgement-box(inset: 8pt, hspace: 8pt, ..cs) = {
  show math.equation: set align(left)
  let cs = cs.pos()
  $
    #for c in cs {
    rect(stroke: .5pt, inset: inset)[#c]
    h(hspace)
  }
  $
  show math.equation: set align(center)
}

#let comment(c) = text(red)[#c]

#let h1 = h(1cm)

#let v1 = {
  linebreak()
  v(1cm)
}

#let v2 = {
  linebreak()
  v(2cm)
}
