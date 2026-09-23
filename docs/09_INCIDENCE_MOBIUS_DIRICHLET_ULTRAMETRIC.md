# CA-18 — Incidence, Möbius, Dirichlet and ultrametric depth

## 0. Scope

This document develops the second derived layer of causal arithmetic.  It assumes
the previously established source structure

\[
X\circ Y,\qquad
X\backslash Z,\qquad
Z/X,
\qquad
X\mid_L Z,\qquad
X\mid_R Z,
\]

together with ordered causal factorizations and primary restriction towers.

No classical prime, p-adic field, Möbius function or Dirichlet convolution is a
primitive of the theory.  They occur as realizations of structures derived from
causal composition and correlative restriction.

The derivation chain developed here is

\[
\boxed{
\text{causal divisibility}
\to
\text{divisor classes}
\to
\text{incidence algebra}
\to
\mu_C
}
\]

and independently

\[
\boxed{
\text{ordered factorizations}
\to
\text{factorization convolution}
\to
\text{causal arithmetic functions}
\to
\text{Dirichlet realization}.
}
\]

The completion side is

\[
\boxed{
\text{restriction tower}
\to
\text{finite indistinguishability quotients}
\to
\text{nested causal balls}
\to
\text{valuation/separation depth}
\to
\text{ultrametric realization}.
}
\]

These three chains are compatible but are deliberately not identified by
definition.

---

## 1. Why incidence requires divisor classes

Left causal divisibility is

\[
X\mid_LY
\iff
\exists Z,\quad X\circ Z\simeq Y.
\]

Right causal divisibility is

\[
X\mid_RY
\iff
\exists Z,\quad Z\circ X\simeq Y.
\]

On a general causal arithmetic domain these are preorders rather than partial
orders.  A unit or a more general associated factor may produce

\[
X\mid_LY,\qquad Y\mid_LX
\]

without strict equality of source objects.

Therefore the incidence algebra must not silently impose antisymmetry on raw
causal numbers.

The canonical left divisor class is the antisymmetrization

\[
\operatorname{DivClass}_L(C)
=
C/{\sim_L},
\]

where

\[
X\sim_LY
\iff
X\mid_LY\land Y\mid_LX.
\]

Similarly

\[
\operatorname{DivClass}_R(C)
=
C/{\sim_R}.
\]

The implementation uses mathlib Antisymmetrization directly.  Hence

\[
[X]_L=[Y]_L
\iff
X\mid_LY\land Y\mid_LX
\]

and

\[
[X]_L\le[Y]_L
\iff
X\mid_LY.
\]

The same statements hold on the right.

Causal units collapse to the class of the multiplicative identity.  Thus the
quotient performs exactly the identification incidence theory requires and no
more.

---

## 2. Left and right Möbius theories

Whenever the antisymmetrized divisor order is locally finite we define

\[
\mu_C^L
=
\mu_{\operatorname{Inc}
(\operatorname{DivClass}_L(C))}
\]

and

\[
\mu_C^R
=
\mu_{\operatorname{Inc}
(\operatorname{DivClass}_R(C))}.
\]

In a noncommutative causal arithmetic these are distinct invariants.

They satisfy

\[
\mu_C^L*\zeta_C^L=1,
\qquad
\zeta_C^L*\mu_C^L=1
\]

and likewise on the right.

If

\[
X\nmid_LY
\]

then

\[
\mu_C^L([X]_L,[Y]_L)=0.
\]

Thus Möbius support is constrained by causal factorization reachability.

For a finite lower interval the inversion theorem is

\[
g(x)
=
\sum_{y\le x}f(y)
\]

if and only if

\[
f(x)
=
\sum_{y\le x}
\mu_C(y,x)\,g(y).
\]

This is the causal inclusion--exclusion law.

---

## 3. Finite presentations

For computational and target-specific work the project also provides an
explicit LeftDivisorPresentation.

It consists of a partial order \(\delta\) and an injective realization

\[
r:\delta\to C
\]

satisfying

\[
a\le b
\iff
r(a)\mid_Lr(b).
\]

This allows finite certified divisor domains to carry an incidence algebra
without first materializing the entire global antisymmetrization.

There is an analogous right presentation.

The canonical quotient and finite presentations serve different purposes:

- the antisymmetrization gives the intrinsic mathematical object;
- a presentation gives a finite/computable realization of a chosen interval.

---

## 4. Natural-number divisor regression

For nonzero \(n\), define

\[
D(n)=\{d:d\mid n\}.
\]

The implementation gives this finite type its own order

\[
d_1\le_Dd_2
\iff
d_1\mid d_2,
\]

not the usual numerical order.

Its bottom and top are

\[
\bot=1,\qquad \top=n.
\]

A central comparison theorem proves that for a divisor \(d\mid n\),

\[
\operatorname{Iic}_{D(n)}(d)
\]

maps exactly to the ordinary finite set

\[
\operatorname{Div}(d).
\]

Consequently the incidence summation domain and the classical divisor
summation domain are literally the same finite combinatorial object after
forgetting the subtype.

---

## 5. Incidence Möbius equals arithmetic Möbius

Let

\[
\mu_{D(n)}
\]

denote the incidence Möbius function of the divisor poset \(D(n)\).

The implemented comparison theorem is

\[
\boxed{
\mu_{D(n)}(1,d)=\mu_{\rm arith}(d).
}
\]

The proof is structural.

First classical Möbius satisfies

\[
\sum_{e\mid d}\mu_{\rm arith}(e)
=
\begin{cases}
1,&d=1,\\
0,&d\ne1.
\end{cases}
\]

Second, the divisor-interval theorem turns this into the corresponding sum on
the finite causal lower interval.

Third, uniqueness of Möbius inversion forces the incidence coefficient from the
bottom element to equal the arithmetic Möbius value.

Thus classical Möbius is not inserted into the causal incidence algebra.  It is
identified as a realization of its intrinsic inverse-of-zeta structure.

A useful corollary is

\[
\boxed{
\chi_{\rm Euler}(D(n))=\mu(n).
}
\]

Here the Euler characteristic of the bounded divisor poset is by definition

\[
\mu_{D(n)}(\bot,\top).
\]

---

## 6. Primary depth and squarefreeness

For a prime \(p\),

\[
\chi_{\rm Euler}(D(p))=-1.
\]

For a prime power \(p^k\), \(k>0\),

\[
\chi_{\rm Euler}(D(p^k))
=
\begin{cases}
-1,&k=1,\\
0,&k>1.
\end{cases}
\]

Thus repeated traversal of one primary direction creates Möbius cancellation.

For squarefree \(n\),

\[
\chi_{\rm Euler}(D(n))
=
(-1)^{\Omega(n)}.
\]

This admits the following causal reading:

- one independent primary channel contributes a sign \(-1\);
- repeated depth in the same channel contributes zero to the endpoint Möbius
  coefficient;
- independent primary channels multiply.

The generic product theorem is implemented directly from incidence algebra:

\[
\mu_{P\times Q}
((a_1,b_1),(a_2,b_2))
=
\mu_P(a_1,a_2)\mu_Q(b_1,b_2).
\]

For bounded channels,

\[
\chi_{\rm Euler}(P\times Q)
=
\chi_{\rm Euler}(P)\chi_{\rm Euler}(Q).
\]

This is the incidence-theoretic origin of multiplicativity under independent
primary decomposition.

---

## 7. Canonical factorization profiles and valuation additivity

A CanonicalAtomicDomain consists of a causal factorization producer

\[
\operatorname{factors}(X)
=
[P_1,\ldots,P_r]
\]

such that every atomic factorization of \(X\) has the same multiplicity profile.

The intrinsic profile is

\[
\nu_C(X)
=
\operatorname{profile}(\operatorname{factors}(X)).
\]

For an atom \(P\),

\[
v_P(X)=\nu_C(X)(P).
\]

Because concatenating atomic factorizations realizes multiplication,

\[
\operatorname{factors}(X)
++
\operatorname{factors}(Y)
\]

is an atomic factorization of \(XY\).  Uniqueness of the profile therefore
forces

\[
\boxed{
\nu_C(XY)=\nu_C(X)+\nu_C(Y).
}
\]

Evaluating at \(P\) gives

\[
\boxed{
v_P(XY)=v_P(X)+v_P(Y).
}
\]

Hence valuation additivity is derived from uniqueness of primary causal
factorization.  It is not an independent axiom.

The natural-number regression proves

\[
\operatorname{Irreducible}_C(n)
\iff
n\text{ is prime}
\]

and

\[
\operatorname{profile}
(n.\operatorname{primeFactorsList})
=
n.\operatorname{factorization}.
\]

Therefore the generic causal multiplicity specializes pointwise to the usual
prime exponent.

---

## 8. Factorization convolution

Incidence convolution and Dirichlet/factorization convolution must be kept
distinct.

Incidence convolution composes interval kernels:

\[
(F*_{\rm inc}G)(a,b)
=
\sum_{a\le x\le b}
F(a,x)G(x,b).
\]

Factorization convolution acts on arithmetic functions:

\[
(f\star_C g)(X)
=
\sum_{AB=X} f(A)g(B).
\]

The project defines a FiniteSystem carrying a finite certified set

\[
\operatorname{Pairs}(X)
=
\{(A,B):AB=X\}.
\]

Then

\[
(f\star_Cg)(X)
=
\sum_{(A,B)\in\operatorname{Pairs}(X)}
f(A)g(B).
\]

These are related through divisibility/factorization geometry but they are not
definitionally the same operation.

---

## 9. Causal arithmetic functions

For a finite factorization system \(S\), a causal arithmetic function is a
function

\[
f:C\to R
\]

that vanishes outside the admissible domain of \(S\).

Factorization convolution closes on these functions because a nonadmissible
target has no admitted factorization pairs.

For the natural-number system,

\[
\operatorname{Pairs}(n)
=
n.\operatorname{divisorsAntidiagonal}.
\]

There is an implemented equivalence

\[
\boxed{
\operatorname{CAF}_{\mathbb N}(R)
\simeq
\operatorname{ArithmeticFunction}(R).
}
\]

Under this equivalence,

\[
\boxed{
f\star_Cg
\longmapsto
f*g
}
\]

where the product on the right is ordinary Dirichlet convolution.

Thus Dirichlet convolution is the classical realization of finite causal
factorization convolution.

Classical Möbius and zeta then satisfy

\[
\mu*\zeta=1=\zeta*\mu.
\]

The project keeps this theorem separate from the incidence inverse theorem and
connects them through the divisor-poset comparison.

---

## 10. Restriction depth

For an inverse causal tower

\[
A_0\leftarrow A_1\leftarrow A_2\leftarrow\cdots
\]

a completed history is

\[
x=(x_0,x_1,\ldots)
\]

with compatible restrictions.

Define

\[
x\sim_ny
\]

when the histories agree through every level \(k\le n\).

Coherence implies

\[
x\sim_ny
\iff
x_n=y_n.
\]

Therefore finite indistinguishability is already determined by the deepest
visible restriction.

The relations \(\sim_n\) are nested equivalence relations:

\[
x\sim_ny,\quad m\le n
\Longrightarrow
x\sim_my.
\]

---

## 11. Causal balls

Define

\[
B_n(x)
=
\{y:x\sim_ny\}.
\]

The project proves:

\[
m\le n
\Longrightarrow
B_n(x)\subseteq B_m(x).
\]

If

\[
y\in B_n(x)
\]

then

\[
B_n(y)=B_n(x).
\]

Consequently, for equal depth,

\[
\boxed{
B_n(x)=B_n(y)
\quad\text{or}\quad
B_n(x)\cap B_n(y)=\varnothing.
}
\]

This is the characteristic ball geometry of an ultrametric space, obtained
before assigning any real-valued distance.

---

## 12. Finite observational quotients

The quotient

\[
Q_n
=
Hist/{\sim_n}
\]

records exactly the states distinguishable at depth \(n\).

There is a canonical evaluation

\[
Q_n\hookrightarrow A_n.
\]

It is always injective.

If every state of \(A_n\) extends to a completed history, evaluation is an
equivalence

\[
Q_n\simeq A_n.
\]

The quotients themselves form an inverse system:

\[
Q_{n+1}\to Q_n.
\]

Evaluation commutes with these restriction maps.

Thus finite observation is itself a causal inverse tower.

---

## 13. Exact p-adic realization

For the primary tower

\[
A_n=\mathbb Z/p^{n+1}\mathbb Z
\]

every finite state extends to a p-adic history.

Hence

\[
\boxed{
Q_n
\simeq
\mathbb Z/p^{n+1}\mathbb Z.
}
\]

The equivalences commute with modular reduction, so the entire inverse systems
are identified, not merely their individual levels.

Therefore

\[
\#Q_n=p^{n+1}.
\]

At the limit,

\[
\boxed{
Hist_\infty(A_\bullet)\simeq\mathbb Z_p.
}
\]

---

## 14. Balls become p-adic balls

Under the history realization

\[
\iota_p:\mathbb Z_p\to Hist_\infty(A_\bullet),
\]

the causal depth condition is

\[
\iota_p(x)\sim_n\iota_p(y)
\iff
\|x-y\|_p
\le
p^{-(n+1)}.
\]

Equivalently,

\[
\iota_p^{-1}(B_n(\iota_p(x)))
=
\overline B
\left(
x,p^{-(n+1)}
\right).
\]

Thus p-adic closed balls are realizations of causal indistinguishability
classes.

---

## 15. Valuation is first separation depth

For \(x\ne y\),

\[
\boxed{
\iota_p(x)\sim_n\iota_p(y)
\iff
n<v_p(x-y).
}
\]

Therefore \(v_p(x-y)\) is precisely the first finite restriction level at which
the two histories separate.

They agree at every level

\[
0,\ldots,v_p(x-y)-1
\]

and fail at level

\[
v_p(x-y).
\]

The numerical metric is then

\[
\boxed{
\|x-y\|_p
=
p^{-v_p(x-y)}.
}
\]

This proves the intended interpretation:

\[
\text{valuation}
=
\text{causal separation depth},
\]

\[
\text{ultrametric}
=
\text{exponential shadow of separation depth}.
\]

---

## 16. What has actually been achieved

At source level the following CA-18 goals now have implementations or concrete
regression models:

- left/right divisibility preorders;
- canonical antisymmetrized divisor classes;
- left/right incidence Möbius functions;
- Möbius inversion;
- finite natural divisor-poset realization;
- exact comparison with classical arithmetic Möbius;
- Euler characteristic interpretation of \(\mu(n)\);
- product-channel multiplicativity;
- generic finite factorization convolution;
- causal arithmetic functions;
- exact Dirichlet realization;
- canonical-profile valuation additivity;
- classical factorization/valuation regression;
- finite causal depth quotients;
- coherent quotient tower;
- exact finite residue realization;
- full p-adic inverse-limit realization;
- causal balls and their nonarchimedean geometry;
- exact valuation/first-separation correspondence.

These statements are source-implemented but are not campaign-accredited until
Lean compilation and the complete evidence contract have been run.

---

## 17. Remaining mathematical frontier of CA-18

The main unresolved parts are no longer Möbius, Dirichlet or the standard
p-adic model.

The principal remaining source-theory questions are:

1. existence and uniqueness of primary decomposition in a genuinely
   nonclassical/noncommutative causal arithmetic domain;
2. comparison between compositional primality and cyclic primitivity outside
   the natural regression model;
3. localization and fraction constructions under precise commutative or Ore
   hypotheses;
4. general \(q=p^f\) residue towers;
5. reconstruction of arbitrary complete DVRs from causal restriction towers;
6. interaction of left/right Möbius theories under dagger or other dualities;
7. realization of primary towers as valuation-colored graph towers.

The next natural implementation layer is therefore

\[
\boxed{
q\text{-adic/DVR reconstruction}
\to
\text{valuation-colored graphs}
\to
\mathbf P^1(\mathcal O/\pi^n)
\to
\text{Bruhat--Tits}.
}
\]

That layer will consume, rather than redefine, the causal arithmetic developed
here.
