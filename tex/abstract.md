We propose a new concept of *omnidirectional* type inference: the
ability to resolve ML-style typing constraints in disorder. In contrast,
all known existing implementations which typically infer the types of
let-bound expressions before typechecking their use sites.

This relies on two technical devices: *suspended match constraints*, which
suspend the resolution of some constraints until the context has more
information about a type variable; and *partial type schemes*, which allow
taking instances of partially solved type scheme containing suspended
constraints, with a
mechanism to incrementally update instances as the scheme is refined.

The benefits of omnidirectional type inference are striking for several
advanced ML extensions, typically those that rely on optional type
annotations where principality is fragile. We illustrate them with OCaml's
static overloading of record labels and datatype constructors, semi-explicit
first-class polymorphism, and tuple projections à la SML.

