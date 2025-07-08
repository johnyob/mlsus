We propose a new concept of *omnidirectional* type inference, which is the ability to resolve ML-style typing constraints in disorder, by contrast with all known implementations that typecheck the bindings before the bodies of let-expressions.

This relies on two technical devices. *Suspended match constraints* suspend the resolution of some constraints until the context has more information on a type variable. *Partial type schemes* allow taking instances of a type scheme
that is not completely solved as it contains suspended constraints, with a mechanism to update their instances when their type scheme is refined, incrementally.

The benefits of omnidirectional type inference are striking for several advanced ML extensions, typically those that rely on optional type annotations for which the principal type property is often fragile. We illustrate them with OCaml's static overloading of record labels and constructors, semi-explicit first-class polymorphism, and tuple projections à la SML.
