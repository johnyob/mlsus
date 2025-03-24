#let textsf = text.with(font: "roboto")

#let dom = textsf("dom")
#let rng = textsf("rng")

#let varset(s) = $cal(V)_(#s)$
#let disjoint = $op(\#)$

#let Ty = textsf("Ty")
#let Con = textsf("Con")
#let ConCtx = textsf("ConCtx")

#let tformer = textsf("F")

#let clet = textsf("let")
#let cin = textsf("in")
#let ctrue = textsf("true")
#let cfalse = textsf("false")
#let ceq = $epsilon.alt$
#let cmatch(alpha, Delta, f) = $angle.l #alpha angle.r [#Delta] f$
#let clam(x, alpha, C1, C2) = $clet #x = lambda #alpha. space #C1 cin #C2$
#let cinst(x, tau) = $#x space #tau$
#let cpinst(x, theta, E) = $#x _(lambda #theta. #E)$


#let fv = textsf("fv")
