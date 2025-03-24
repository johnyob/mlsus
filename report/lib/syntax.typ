#let collection-rule(
  // The name of the set being declared
  name: none,
  // The collection being declared
  collection,
  symbols,
) = {
  (
    kind: "collection",
    name: name,
    collection: collection,
    symbols: symbols,
  )
}

#let syntax-rule(
  // The name of the syntax rule, displayed to the left of the definition
  name: none,
  // The collection being defined
  collection: none,
  // The meta-variable denoting elements of the collection
  lhs,
  delim: $::=$,
  ..lines,
) = {
  (
    kind: "syntax",
    name: name,
    collection: collection,
    lhs: lhs,
    delim: delim,
    lines: lines.pos(),
  )
}

// Lays out a syntax definition
#let syntax(
  // The space between each consequtive rule
  name-size: 5cm,
  // The rules the define the syntax
  ..rules,
) = {
  // We layout syntax using a 5-column table
  //
  // |--------------|------------------|----------------------|----------------|------------|
  // | Name (left)  | Set Name (right) | Rule symbol (center) | Delim (center) | Rhs (left) |
  // |--------------|------------------|----------------------|----------------|------------|
  //
  // The delimiter is either a rule production delimiter (usually '::=') or a pad delimiter ('|')

  // Between each rule, we additionally add a gutter-row.
  let gutter-row = (none, none, none, none, none)

  // Name, Set Name, Rule symbol are none.
  let pad = (none, none, none, $|$)

  // Adds in.rev to the collection name
  let layout-collection(collection) = {
    if collection != none {
      $#collection in.rev$
    }
  }

  let layout-collection-rule(rule) = {
    (
      rule.name,
      layout-collection(rule.collection),
      table.cell(
        colspan: 3,
        align: left,
        rule.symbols,
      ),
    )
  }

  let layout-syntax-rule(rule) = {
    // Add pads
    let content = rule.lines.intersperse(pad)

    (
      rule.name,
      layout-collection(rule.collection),
      rule.lhs,
      rule.delim,
      content,
    )
  }

  let layout-rule(rule) = {
    if rule.kind == "syntax" {
      layout-syntax-rule(rule)
    } else if rule.kind == "collection" {
      layout-collection-rule(rule)
    }
  }

  let layout-rules(rules) = {
    let content = rules.map(layout-rule).intersperse(gutter-row).flatten()

    table(
      columns: (
        name-size,
        auto,
        auto,
        auto,
        auto,
      ),
      rows: auto,
      align: (
        left, // name
        right, // set
        center, // symbol
        center, // delim
        left, // rules
      ),
      inset: 0.3em,
      row-gutter: 0.1em,
      stroke: none,
      ..content
    )
  }

  layout-rules(rules.pos())
}
