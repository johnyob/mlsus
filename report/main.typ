#import "lib/template.typ": *
#import "lib/std.typ": *
#import "lib/syntax.typ": *
#import "lib/thm.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "cmon.typ": *

#show: cam-notes.with(
  title: [
    Constraint-Based Omnidirectional Type Inference and its Applications
  ],

  subtitle: [ Technical Report ],

  author: "Alistair O'Brien",

  college: [ Queens' College ],

  date: datetime
    .today()
    .display("[month repr:long] [day padding:none], [year repr:full]"),
)

= MLsus

#syntax(
  syntax-rule(
    name: [Constraints],
    collection: Con,
    $C$,
    $ctrue | cfalse | exists alpha. C | ceq$,
    $clam(x, alpha, C, C) | cinst(x, tau)$,
    $cmatch(alpha, rho, f) | cpinst(x, theta, E)$,
  ),
  syntax-rule(
    name: [Multi-Equations],
    $ceq$,
    $tau | tau = ceq$,
  ),
  syntax-rule(
    name: [Closures],
    $rho$,
    $emptyset | rho, alpha$,
  ),
  collection-rule(
    name: [Cases],
    $Ty -> Con$,
    $f$,
  ),
  syntax-rule(
    name: [Types],
    collection: Ty,
    $tau$,
    $alpha | overline(tau) tformer$,
  ),
  syntax-rule(
    name: [Partial Instantiations],
    $theta$,
    $alpha[beta] | theta[alpha := beta]$,
  ),
  syntax-rule(
    name: [Equations],
    $E$,
    $ctrue | E and ceq$,
  ),
  syntax-rule(
    name: [Constraint Contexts],
    collection: ConCtx,
    $cal(C)$,
    $[dot] | C and cal(C) | cal(C) and C | exists alpha. cal(C)$,
    $clam(x, alpha, cal(C), C) | clam(x, alpha, C, cal(C))$,
  ),
)

- $cal(C)[C]$ is defined as usual.
- We assume commutativity and associativity of $and$


== Solver

// Not affected by suspended constraints
- We say $alpha$ dominates $beta$ wrt $C$, written $alpha prec_C beta$, if $C = cal(C)[alpha = overline(tau)[beta]  tformer = ceq]$
- We say $C$ is cyclic iff $alpha prec^*_C alpha$

// Should be affected by suspended constraints
- $C$ determines $alpha$ iff for two different assignments $Phi_1, Phi_2$ that satisfy $C$ and co-incide outside $alpha$ $==> {Phi_1}alpha = {Phi_2}alpha$
- Lemma: Let $overline(alpha) disjoint overline(beta)$. $exists overline(alpha). C and ceq$ determines $overline(beta)$ if $ceq = (tau = ceq')$ and $fv(tau) disjoint overline(alpha), overline(beta)$ and $beta subset.eq fv(ceq')$

- $C$ is a _partially solved form_ iff it is of the form $exists overline(alpha). and.big_i ceq_i and overline(cmatch(beta, rho, f)) and overline(cpinst(x, theta, E))$ where $ceq_i$ has at most one non-variable type, no two multi-equations share a variable, $C$ is not cyclic, and $overline(beta) disjoint overline(alpha)$

- $C$ is a (fully) _solved form_ iff it is of the form $exists overline(alpha). and.big_i ceq_i$ where $ceq_i$ has at most one non-variable type, no two multi-equations share a variable, and $C$ is not cyclic.

#judgement-box($C --> C$)

#[
  #show math.equation: set align(end)

  $
    cal(C)[C_1] &--> cal(C)[C_2] &&"if" C_1 --> C_2 \
// True
C and ctrue &--> C \
// False
cal(C)[cfalse] &--> cfalse &&"if" cal(C) eq.not [dot] \ \ \
// Existentials
(exists overline(alpha). C_1) and C_2 &--> exists alpha. C_1 and C_2 &#h(1cm)&"if" overline(alpha) disjoint C_2 \
clet x = Lambda cin exists overline(alpha).C &--> exists overline(alpha). clet x = Lambda cin C &&"if" overline(alpha) disjoint Lambda \ \ \
// Partial instantiation
clet x = lambda alpha. exists overline(beta). C_1 cin cal(C_2)[overline(cpinst(x, theta, E))] &--> exists overline(beta). clet x = lambda alpha. C_1 cin C_2[overline(cpinst(x, theta \\ overline(beta), E) and overline(theta(beta)) = overline(beta))] &&"if" overline(beta) disjoint cal(C_2) \
&&&and exists alpha. C_1 "determines" overline(beta) \
&&&and forall j. overline(beta) subset.eq dom(theta_j) \
clam(x, theta, exists beta. C, cal(C)[cpinst(x, theta, E)]) &--> clam(x, theta, exists beta. C, cal(C)[exists beta'. cpinst(x, theta[beta := beta'], E)]) &&"if" beta' disjoint theta, E \
clam(x, theta, C and ceq, cal(C)[cpinst(x, theta, E)]) &--> clam(x, theta, C and ceq, cal(C)[cpinst(x, theta, E and ceq) and theta(ceq)]) \
clam(x, alpha, C, cal(C)[cpinst(x, theta, E)]) &--> clam(x, alpha, C, cal(C)[ctrue]) &&"if" exists theta. E tack.double exists alpha. C
 \ \ \
// Application
clet x = lambda alpha. C cin cal(C)[x space tau] &--> clet x = lambda alpha. C cin cal(C)[exists alpha'. alpha' = tau and cpinst(x, alpha[alpha'], ctrue)] &&"if" x, C disjoint cal(C) \

// Let
clet x = lambda alpha. C_1 cin C_2 &--> C_2 and exists alpha. C_1 &&"if" x disjoint C_2 \ \ \
// Suspended constraints
cal(C)[cmatch(alpha, rho, f)] and alpha = tau = ceq &--> cal(C)[f(tau)] and alpha = tau = ceq &&"if" tau disjoint cal(C) and tau in.not varset(Ty) \
exists alpha, overline(beta). cmatch(alpha, rho, f) and C &--> cfalse &&"if" C "never realises" alpha \ \ \
// Unification
alpha = ceq_1 and alpha = ceq_2 &--> alpha = ceq_1 = ceq_2 \
alpha = alpha = ceq &--> alpha = ceq \
overline(tau)[tau] tformer = ceq &--> exists alpha. overline(tau)[alpha] tformer and alpha = tau &&"if" tau in.not varset(Ty) and alpha disjoint overline(tau), ceq \
overline(tau_1) space tformer_1 = overline(tau_2) space tformer_2 = ceq &--> cfalse &&"if" tformer_1 eq.not tformer_2 \
U &--> cfalse &&"if" U "is cyclic"
  $
]

How to determine $C$ never realises $alpha$?

- $alpha$ guards $beta$ wrt $C$ if $C = cal(C)[cmatch(alpha, rho[beta], f)]$
- The relation $alpha$ guards $beta$ wrt $C$ defines a directed graph $G_"guard" (C)$. A root of $G_"guard" (C)$ is a variable (node) with no incoming edges.
- $U and U_"part"$ never realises $alpha$ if $alpha$ is not equated to any constructor type in $U$, $alpha$ is not reachable from the roots of $G_"guard" (U_"part")$, and $alpha$ is not in the range of any partial instantiations in $U_"part"$

How to phrase this in an efficient way?
- Solve $clet$ lambdas first (gives us a lot of information)
- Generalize late -- before partial instantiation (since handling
  existentials with partial instances is costly)
- Solve suspended constraints as soon as possible
