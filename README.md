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
\text{structural paired transport }(\Phi,\Psi)
\to
\text{optional adjunction/restriction bridges}
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

## Fundamental structural transport

For a typed causal transport between two derived carriers, the source theory
first keeps only an oppositely directed pair

\[
\Phi:A\to B,
\qquad
\Psi:B\to A.
\]

No inverse, adjunction, dagger, duality or state-space interpretation is part
of this primitive carrier.

On an ordered realization one may additionally prove an adjunction

\[
\Phi(a)\le b\iff a\le\Psi(b).
\]

That extra theorem packages the pair as the existing
`ExtensionRestriction` API and recovers closure/interior and residuation.
Thus the powerful CA-17/CA-18 adjoint arithmetic is retained without making
adjunction universal.

Correlative restriction, geometric pullback, algebraic dual and causal dagger
remain separately typed until comparison theorems relate them.

## Program

The historical CA-00--CA-20 ledger is retained. A 2026-09-24 foundation lift now sits beneath it and weakens the primitive transport carrier without deleting the stronger adjoint specialization:

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
