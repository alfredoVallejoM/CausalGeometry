# CausalGeometry

CausalGeometry is the independent Lean program for **causal diaries, causal
numbers, causal arithmetic, correlative restriction and causal calculus**,
together with typed realizations into arithmetic geometry, ECIA and later
scientific comparison programs.

The project is intentionally upstream of GenContinuum:

\[
\text{events}
\to
\text{histories}
\to
\text{bounded causal diaries}
\to
\text{causal numbers}
\to
\text{extension/restriction polarity}
\to
\text{derived causal arithmetic}
\to
\text{realizations}.
\]

A causal number over a boundary \(A\) is an admissible endodiary

\[
X:A\rightsquigarrow A.
\]

The ordinary integer attached to it is a decategorified shadow, not its
definition.

## Fundamental polarity

For a causal process \(h:A\rightsquigarrow B\), the source theory includes:

\[
h_!:\mathsf{Poss}(A)\to\mathsf{Poss}(B)
\]

and its **correlative restriction**

\[
h^*:\mathsf{Poss}(B)\to\mathsf{Poss}(A)
\]

with

\[
h_!P\le Q\iff P\le h^*Q.
\]

Correlative restriction is not the causal dagger and is not the linear dual.
A geometric pullback may realize \(h^*\) after a comparison theorem.

Inside ordered arithmetic sectors this becomes residuation:

\[
X\circ Y\preceq Z
\iff
Y\preceq X\backslash Z,
\]

\[
Y\circ X\preceq Z
\iff
Y\preceq Z/X.
\]

Thus causal arithmetic supports a notion of restriction/division before
invertibility or classical fractions.

## Program

The program currently has twenty-one gates:

- **CA-00--CA-10**: original autonomous causal kernel.
- **CA-11--CA-14**: typed ECIA derivations and realizations.
- **CA-15**: API/adversarial closure milestone for the original program.
- **CA-16**: generalized restriction/pullback geometry and Wilderber bridge.
- **CA-17**: causal extension and correlative restriction.
- **CA-18**: derived causal arithmetic and residuation.
- **CA-19**: realization synthesis from causal numbers.
- **CA-20**: RH--BSD--Langlands transformation program.

The original 300 rows are preserved. CA-17--CA-20 add 128 obligations, giving
**428 atomic obligations**.

The separate generative-dynamic motive campaign is deliberately outside this
repository program.

## Central derivation principle

For every mature external object \(Y\), CausalGeometry seeks a typed origin

\[
(X,R,\eta),
\qquad
X:\mathrm{CausalNumber},
\quad
R:\mathrm{Realization},
\quad
\eta:R(X)\simeq Y.
\]

The causal number is the source. Graphs, local fields, Tate data, Galois,
Hecke, dessins, ECIA structural numbers, Selmer data and spectral objects are
candidate realizations, completions, quotients or analytic upgrades of that
source.

## Arithmetic program

The intended derivation order is:

\[
\text{composition}
\to
\text{correlative residuals}
\to
\text{factorization}
\to
\text{primary directions}
\to
\text{valuations}
\to
\text{completions/localizations}
\to
\text{classical shadows}.
\]

Prime profiles are therefore targets of derivation, not the deepest primitive.

## ECIA

The existing ECIA definition of a structural number as an admissible
endocorrespondence is a realization target:

\[
\mathcal R:\mathbf{Cau}\to\mathbf{ECIA}_{corr}.
\]

The strong claim that every ECIA structural number has a causal presentation is
not assumed.

## Wilderber generalized restrictions

For a geometric probe \(\phi:Y\to X\), pullback

\[
\phi^*
\]

is treated as a concrete realization of correlative restriction whenever the
comparison theorem is proved.  Affine restriction

\[
R_{F,p,L}(t)=F(p+Lt)
\]

is one important realization, not the universal definition of \(h^*\).

## RH, BSD and Langlands

The scientific synthesis keeps all previously developed routes simultaneously.
It seeks common causal sources whose realizations include graph/Ihara,
\(p/q\)-adic and Bruhat--Tits, Tate, dessins, Wilderber, Galois/Weil--Deligne,
Hecke/automorphic, adeles, Mordell--Weil/Selmer, Green/Weil, Tomita and
spectral/\(L\)-function sectors.

No conjecture is promoted merely by belonging to this realization diagram.

## No workflows

This repository deliberately contains no GitHub Actions, workflows or CI
configuration.

## Toolchain

- Lean 4.32.1
- mathlib v4.32.1
