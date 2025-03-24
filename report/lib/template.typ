#let cam-notes(
  // The title
  title: "My Report",
  // Subtitle (optional)
  subtitle: none,
  // Author name
  author: "Alistair O'Brien",
  date: none,
  college: "Queens' College",
  body,
) = {
  // Set the document's basic properties.
  set document(author: author, title: title)
  set text(font: "New Computer Modern", lang: "en")
  show math.equation: set text(weight: 400)
  set heading(numbering: "1.1")

  let chapternum = loc => {
    str(query(heading.where(level: 1, numbering: "1.1").before(loc), loc).len())
  }

  show heading: it => {
    if it.level == 1 {
      v(4.5em)
      set text(size: 25pt)
      it
    } else if it.level < 4 {
      v(1em)
      it.body
      v(0.5em)
    } else {
      it.body
    }
  }

  // Title page.
  set align(center)
  align(right, strong(text(2em, author)))

  v(3fr)
  text(2em, weight: 700, par()[#title])

  if subtitle != none {
    text(1.5em, subtitle)
  }

  v(1fr)

  align(center, image("../assets/cam-crest.jpeg", width: 75%))


  v(1fr)

  // College
  text(
    1.5em,
    par(leading: 0.75em)[
      University of Cambridge\
      Computer Laboratory\
      #college
    ],
  )

  v(1.5fr)

  text(1.5em, date)

  v(1fr)
  pagebreak()

  set align(left)

  // Table of contents.
  outline(depth: 3, target: heading)

  // Main body.
  set page(numbering: "1", number-align: center)
  set par(justify: true)

  show math.equation: set block(breakable: true)

  body
}

#let appendix(body) = {
  set heading(numbering: "A1", supplement: [Appendix])
  counter(heading).update(0)
  body
}
