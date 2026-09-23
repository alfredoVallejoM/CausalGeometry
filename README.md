# CausalGeometry

CausalGeometry is the independent Lean program for **causal diaries, causal
numbers, causal arithmetic and causal calculus**, together with typed
realizations into arithmetic geometry and ECIA.

The project is intentionally upstream of GenContinuum:

[
	ext{events}
	o
	ext{histories}
	o
	ext{bounded causal diaries}
	o
	ext{causal numbers}
	o
	ext{realizations}
	o
	ext{ECIA structural numbers}
	o
	ext{classical arithmetic shadows}.
]

A causal number over a boundary (A) is an admissible endodiary

[
X:Aightsquigarrow A.
]

The ordinary integer attached to it is a decategorified shadow, not its
definition.

## Program

The frozen program has seventeen gates:

- **CA-00--CA-10**: autonomous causal kernel.
- **CA-11--CA-14**: typed ECIA derivations and realizations.
- **CA-15**: terminal API/audit.
- **CA-16**: generalized restriction/pullback geometry and the Wilderber bridge.

The original 280-row causal/ECIA program is preserved and CA-16 adds 20
restriction-geometry obligations, giving **300 atomic obligations**.

## Central derivation principle

For every mature external object (Y), CausalGeometry seeks a typed origin

[
(X,R,eta),
qquad
X:mathrm{CausalNumber},
quad
R:mathrm{Realization},
quad
eta:R(X)simeq Y.
]

This distinguishes:

- kernel consequences;
- functorial realizations;
- concrete models;
- analytic upgrades;
- genuinely open identifications.

## ECIA

The existing ECIA definition of a structural number as an admissible
endocorrespondence is treated as a realization target.  The main bridge is

[
mathcal R:mathbf{Cau}longrightarrowmathbf{ECIA}_{corr},
]

with preservation of composition, unit, dagger and cyclic shadow.  The strong
representability claim that every ECIA structural number comes from a causal
number is **not assumed**.

## Wilderber generalized restrictions

For a homogeneous/polynomial law (F),

[
R_{F,p,L}(t)=F(p+Lt)
]

is viewed as the affine-linear instance of pullback (phi^*F).  Causal
histories supply composable probes (phi), so restriction functoriality,
Hasse transport, orbit reduction and finite-field slicing become realizations
of causal observation.  See `docs/05_WILDERBER_RESTRICTIONS.md`.

## No workflows

This repository deliberately contains no GitHub Actions, workflows or CI
configuration.  Verification is mathematical and local/reproducible; adding a
workflow is outside the project contract.

## Toolchain

- Lean 4.32.1
- mathlib v4.32.1
