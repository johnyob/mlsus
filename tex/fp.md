# Some comments from François Pottier

> abstract: "which typically infer" → "typically infer"

- [x] fixe.

> p.1, "from which all other valid types for e are instances of σ" :
> unclear/redundant construction

- [x] removed.

> p.1, "As a result, inference of subexpressions can proceed in any order":
> c'est un peu le contraire de ce que dit l'abstract...

- [x] Made the abstract more precise AND weakened this statement.

> p.2, "specification-drive" → "specification-driven"?

- [x]

> p.2, "OCaml does not make any difference between ex3, ex32, or ex33": yet
> we get orange in ex33 and red in the other two.

- [x]
  Fixed the text with (signficantly) more details.
  Flags now checked by OCaml.

> p.2, "polymorphic types are treated as known and may guide disambiguation,
> whereas monomorphic types are considered not-yet-known and cannot be relied on
> for disambiguation". I am not sure what you mean. Do you mean that if a
> variable has been let-bound then its type is considered known, whereas if it
> has been bound by lambda then it is considered not-yet-known? (The other
> interpretation that I can think of is that you want to test whether a type is
> polymorphic, by counting the number of its quantifiers. But this does not seem
> to make sense.) If it is a matter of "let" versus "lambda", then it has
> nothing to do with polymorphism.

- [ ] I dom't quite understand why François does not understand...

> p.3, "For example, the following would be rejected as ambiguous with
> 𝜋-directional type inference alone": why? Explain. Not clear to me.

- [x] Slighly changed the explanation.

> p.3, "Besides, the implementation of 𝜋-directional type inference has an
> algorithmic cost. For technical reasons, type annotations must unshare type".

> This comment suggests that I have not understood what you mean by
> "π-directional type inference". Your first mention of this concept (p.2, line
> 66) should be accompanied by a citation that explains where this concept was
> introduced. Your comment about "unsharing types" should also be accompanied
> with a citation.

There is already a dictation

- [ ]

> p.3, "in bidirectional fashion" → "in a bidirectional fashion"?

- [ ]

> p.4, "The user must explicitly pass the -principal flag to require the more
> expensive computation when desired". So, when you write "OCaml" in a box,
> do you mean `ocaml` or `ocaml -principal`? Or are your examples insensitive
> to the difference?

- [ ]

> p.4, "In absence" → "In the absence"?

- [ ]

> p.4, "one of its variant" → "one of its variants"

- [ ]

> p.4, "all follow this strategy, to the best of our knowledge". Well, EMLTI
> allows you to work on the right-hand side of a `let` constraint before
> working on the left-hand side, if you wish, or even to work alternately
> on both sides. Its main limitation is that if you decide to rewrite
> `let x = λα.C1 in ...x(τ)...` into
> `let x = λα.C1 in ...(λα.C1)(τ)`
> then you duplicate `C1`,
> so unless `C1` is already fully simplified, you are duplicating work.
> The connection between the two copies of `C1` is lost.
> My guess at this point in the paper is that you want to introduce a more
- [ ]

> p.ecise constraint language where you can keep track of this connection,
> so as to avoid the duplication of work (?).
> That said the existing language in EMLTI also allows this -- it suffices
> to *not* take this rewriting step. But then you lose the ability to
> deduce anything out of x(τ).
> So, my guess is that you want the best of both forms at once?
> i.e. the ability to extract useful information out of x(τ)
> *and* to not duplicate the work of further simplifying C1.

- [ ]

> p.4, "from context" → "from the context"?

- [ ]

> p.5, "implementing partial types schemes is also hard" : in what sense?
> abstract: "which typically infer"   "typically infer"

- [ ]

> p.1, "from which all other valid types for e are instances of  " :
> unclear/redundant construction

- [ ]

> p.1, "As a result, inference of subexpressions can proceed in any order":
> c'est un peu le contraire de ce que dit l'abstract...

- [ ]

> p.2, "specification-drive"   "specification-driven"?

- [ ]

> p.2, "OCaml does not make any difference between ex3, ex32, or ex33": yet
> we get orange in ex33 and red in the other two.

- [ ]

> p.2, "polymorphic types are treated as known and may guide disambiguation,
> whereas monomorphic types are considered not-yet-known and cannot be relied on
> for disambiguation". I am not sure what you mean. Do you mean that if a
> variable has been let-bound then its type is considered known, whereas if it
> has been bound by lambda then it is considered not-yet-known? (The other
> interpretation that I can think of is that you want to test whether a type is
- [ ]

> p.lymorphic, by counting the number of its quantifiers. But this does not seem
> to make sense.) If it is a matter of "let" versus "lambda", then it has
> nothing to do with polymorphism.

- [ ]

> p.3, "For example, the following would be rejected as ambiguous with
>  -directional type inference alone": why? Explain. Not clear to me.

- [ ]

> p.3, "Besides, the implementation of  -directional type inference has an
> algorithmic cost. For technical reasons, type annotations must unshare type".
> This comment suggests that I have not understood what you mean by
> " -directional type inference". Your first mention of this concept (p.2, line
> 66) should be accompanied by a citation that explains where this concept was
> introduced. Your comment about "unsharing types" should also be accompanied
> with a citation.

- [ ]

> p.3, "in bidirectional fashion"   "in a bidirectional fashion"?

- [ ]

> p.4, "The user must explicitly pass the -principal flag to require the more
> expensive computation when desired". So, when you write "OCaml" in a box,
> do you mean `ocaml` or `ocaml -principal`? Or are your examples insensitive
> to the difference?

- [ ]

> p.4, "In absence"   "In the absence"?

- [ ]

> p.4, "one of its variant"   "one of its variants"

- [ ]

> p.4, "all follow this strategy, to the best of our knowledge". Well, EMLTI
> allows you to work on the right-hand side of a `let` constraint before
> working on the left-hand side, if you wish, or even to work alternately
> on both sides. Its main limitation is that if you decide to rewrite
> `let x =   .C1 in ...x( )...` into
> `let x =   .C1 in ...(  .C1)( )`
> then you duplicate `C1`,
> so unless `C1` is already fully simplified, you are duplicating work.
> The connection between the two copies of `C1` is lost.
> My guess at this point in the paper is that you want to introduce a more
- [ ]

> p.ecise constraint language where you can keep track of this connection,
> so as to avoid the duplication of work (?).
> That said the existing language in EMLTI also allows this -- it suffices
> to *not* take this rewriting step. But then you lose the ability to
> deduce anything out of x( ).
> So, my guess is that you want the best of both forms at once?
i.e. the ability to extract useful information out of x( )
*and* to not duplicate the work of further simplifying C1.

p.4, "from context"   "from the context"?

p.5, "implementing partial types schemes is also hard" : in what sense?
