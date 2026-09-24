# CausalGeometry — closure map for causal calculus, CA-18 and ECIA consumption

Snapshot source head before this document: 05b152876e8843dbc93e45f190d9968860afad5d

Date: 2026-09-24

## 0. Architectural lock

The repository now follows the intended source direction:

[
	ext{primitive events}
	o
	ext{derived configurations/histories/diaries}
	o
(Phi,Psi)
	o
	ext{optional adjunctions}
	o
	ext{causal calculus and arithmetic}
	o
	ext{typed realizations}
	o
	ext{ECIA adapters}.
]

The foundational pair is

[
Phi:alpha	oeta,
qquad
Psi:eta	oalpha.
]

Neither inverse laws nor adjunction, dagger, linear duality or semantic
interpretation are built into the carrier.

Adjunction is an optional bridge

[
Phi(a)le b
iff
alePsi(b).
]

This preserves all existing extension/restriction and residuation mathematics
without making it ontologically primitive.

## 1. Adversarial correction to concurrency

The former ConcurrentAt definition admitted e=f.

That was inconsistent with sequential execution because executing e disables a
second execution of the same primitive event.

The current foundation:

- requires distinct concurrent events;
- proves each remains enabled after executing the other;
- derives both intermediate configurations;
- derives both two-step endpoints;
- proves equality of the two flat endpoints.

This correction is upstream of all second-order causal calculus.

## 2. Current calculus surface

Implemented source modules now include the following layers.

### First variation

- causal finite difference;
- constant-observable law;
- additive and subtractive rules;
- noncommutative finite product rule;
- naturality under linear maps.

### Event directions and linearization

- typed enabled event directions;
- event-direction evaluation of differences;
- first-order linearization;
- JVP/VJP-style transport interfaces where declared by the corresponding
  modules.

### Second variation

- square variation on concurrency diamonds;
- symmetry under swapping flat concurrent directions;
- exterior antisymmetrization;
- square-zero exterior second difference on flat concurrency diamonds;
- order curvature.

### Connections and transport

- constant-fiber causal connections;
- dependent configuration-indexed causal connections;
- linear causal connections;
- two ordered transports around a concurrency square;
- flatness;
- finite curvature;
- covariant finite differences;
- covariant square defects;
- exact relation between path dependence of the defect and curvature;
- parallel transport along a derived causal path;
- holonomy as a linear endomorphism, without assuming invertibility.

### Gauge layer

- configuration-indexed linear gauge automorphisms;
- gauge-conjugated connections;
- covariance of finite curvature;
- preservation of flatness under gauge transformation;
- covariance of path transport;
- conjugation law for holonomy.

### Local linearized curvature and Bianchi

A separate local gauge-potential layer defines curvature by endomorphism
commutators.

The local Bianchi law is proved from Jacobi.

This is intentionally not identified definitionally with finite transport
curvature. A finite/infinitesimal comparison theorem remains a separate future
obligation.

### Cube combinatorics

- causal cube frames;
- pairwise concurrency diamonds;
- codimension-one faces;
- injective reindexing.

### Path integration

The path layer and path-integral layer provide finite derived histories and the
discrete integration/Stokes surface already implemented in the repository.

### D = d_v + d_h + d_mu

Vertical, horizontal and restriction components remain separately typed.

Square-zero is a property under hypotheses, never a field hidden in the
definition.

## 3. Causality versus restriction

PairedDynamics formalizes dynamics on both sides of one structural pair.

The two naturality squares are independent:

[
Phicirc d_{m src}
stackrel{?}{=}
d_{m tgt}circPhi,
]

[
Psicirc d_{m tgt}
stackrel{?}{=}
d_{m src}circPsi.
]

The repository now contains explicit forward and backward defects.

A same-type discriminator proves that forward naturality can hold while
backward naturality fails.

Thus the noncommutation of causal evolution and correlative restriction is now
formal data rather than only an interpretation.

## 4. Jets, restrictions and variational duality

Finite jet/restriction towers now contain:

- a structural pair at every order;
- jet truncation;
- restriction truncation;
- independent forward compatibility;
- independent backward compatibility;
- round-trip compatibility;
- coherent inverse-limit sections.

The limit pair exists when both truncation compatibilities are proved; it still
does not acquire an inverse or adjunction by definition.

The variational layer contains:

- possibly singular Legendre correspondence;
- one-way Legendre selection;
- paired selection;
- Lagrangian;
- Hamiltonian;
- explicit pairing;
- conjugacy theorem;
- jet-level variational systems;
- optional truncation coherence.

This gives ECIA a future Hamiltonian/Lagrangian consumer without requiring an
invertible Legendre transform.

## 5. CA-18 arithmetic closure

Previously implemented and retained:

- residual arithmetic;
- exact left/right division;
- left/right divisibility;
- gcd/lcm;
- causal irreducibility;
- factorization;
- canonical atomic profiles;
- valuation additivity;
- CRT;
- primary decomposition;
- left/right incidence;
- Mobius inversion;
- factorization convolution;
- exact Dirichlet regression;
- inverse towers;
- finite primary towers;
- exact Z_p reconstruction;
- causal depth balls and p-adic ultrametric comparison.

New in this closure:

### Ore layer

The repository now separates:

- RightOreSquare;
- LeftOreSquare;
- RightOreCondition;
- LeftOreCondition;
- raw right fractions a*s^{-1};
- raw left fractions s^{-1}*a;
- multiplication only when the appropriate Ore witness is supplied.

The commutative sector proves both Ore conditions canonically.

### Genuine cancellative commutative quotient

For a cancellative commutative monoid and denominator submonoid:

[
(a,s)sim(b,t)
iff
at=bs.
]

The relation is proved reflexive, symmetric and transitive.

The quotient CommFraction is therefore a genuine fraction carrier rather than a
pair with notation.

Multiplication descends to the quotient and is packaged as a commutative
monoid.

### Group-target universal property

Every monoid morphism

[
f:alpha	o G
]

to a commutative group extends to

[
widetilde f:operatorname{CommFraction}(S)	o G
]

by

[
widetilde f(a/s)=f(a)f(s)^{-1}.
]

The extension:

- is well-defined under cross multiplication;
- preserves one and multiplication;
- extends the source map;
- sends denominator inverses to inverses;
- is unique among morphisms with the same source restriction.

This closes the commutative-group target version of the localization universal
property.

The noncommutative Ore quotient/universal property remains separate.

## 6. q = p^f residue structure

FinitePrimaryTower already carried the general residue cardinal q.

PrimePowerPrimary now separates:

- rational prime p;
- residue degree f;
- q=p^f;
- level cardinal
  [
  p^{f(n+1)}.
  ]

This prevents confusion among p, f, q and later Tate parameters.

## 7. Restriction graph

Every inverse tower canonically produces a depth-colored directed restriction
graph:

[
x_{n+1}	o x_n
iff
operatorname{drop}_n(x_{n+1})=x_n.
]

Every child has a unique parent.

Every compatible infinite history is an infinite ray through this graph.

For a primary tower the number of level-n vertices is q^(n+1); for a
prime-power tower it is p^(f(n+1)).

This is the source graph layer required before a Bruhat--Tits comparison.

No theorem currently identifies an arbitrary restriction graph with a
Bruhat--Tits tree.

## 8. Weak process composition, dagger and cyclic shadow

The process layer now distinguishes:

- witnessed diary composition;
- weak associative/unital enddiary composition up to explicit equivalence;
- boundary flip;
- genuine event-level dagger;
- dagger involution witnesses;
- cyclic shadow;
- cyclicity without source commutativity.

This prevents ECIA from receiving a falsely strict or commutative source.

## 9. CA-19 ECIA consumer boundary

The source now exposes the following independent contracts.

### Real(X)

RealizationAt X and typed comparison morphisms provide the objectwise
realization category skeleton.

Comparisons are classified explicitly as:

- equivalence;
- quotient/loss;
- completion;
- localization;
- analytic upgrade;
- conditional bridge.

### ECIA admissibility

ECIARealization transports causal numbers to a downstream target while proving
admissibility soundness.

ECIA is not a dependency of this repository.

### Process preservation

Separate predicates cover:

- selected composition witnesses;
- dagger witnesses;
- cyclic shadow;
- generic typed observables.

### Paired structural transport

ForwardPairedCompatibility and BackwardPairedCompatibility are separate.

PairedRealizationCompatibility requires both and then proves preservation of
source and target round trips.

This is the correct interface for transporting Phi/Psi without collapsing
their logical independence.

### Weak arithmetic shadow

EndDiaryNatShadow supplies a multiplicative natural shadow for a weak
composition system and requires invariance under the chosen source equivalence.

ECIA can separately prove:

- preservation of the source shadow;
- preservation of the chosen weak composition.

From these the target shadow multiplicativity is derived.

### Finite transfer layer

FiniteTransferSystem supplies:

- finite state space;
- weighted transfer matrix;
- trace sequence tr(T^n);
- determinant kernel det(I-uT).

No primitive-cycle Euler product or Ihara equality is assumed.

TransferTraceComparison is the explicit future boundary for proving that a
causal/cyclic trace sequence is realized by a chosen transfer operator.

## 10. Verification state

The local fail-closed runner is part of the repository.

It checks:

- complete root import closure;
- forbidden proof shortcuts;
- full lake build;
- root typecheck;
- isolated calculus typechecks;
- isolated realization/ECIA typechecks;
- arithmetic regression controls;
- adversarial same-type controls;
- mandatory manual review gates.

Manual required obligations yield INCOMPLETE, not PASS.

At the snapshot immediately before this document:

- 90 Lean modules existed;
- the root imported all 90;
- there were no stale root imports;
- no GitHub workflow existed;
- repository searches found no Lean-source use of sorry, admit,
  native_decide, unsafe or project-local axiom shortcuts.

The current ChatGPT execution environment still lacks Lean/lake, so these new
modules are not compilation-certified here.

No campaign row should be called accredited until the local runner has been
executed against the exact SHA and its manual obligations have been reviewed.

## 11. Next implementation frontier

The next source work should proceed in this order.

### CALC-CLOSE-1

- finite versus local-linearized curvature comparison;
- dependent linear connection;
- tensor-valued observables;
- covariant tensor operations;
- finite Bianchi comparison under explicit hypotheses.

### CA18-LOC-2

- genuine right Ore quotient;
- genuine left Ore quotient;
- equivalence only under an explicit two-sided Ore theorem;
- universal localization maps;
- comparison with residual exact division on the common domain.

### CA18-LOCAL-2

- complete principal/local residue interfaces;
- constant-fiber q-branching hypotheses;
- projective-line finite levels;
- lattice realization;
- Bruhat--Tits comparison.

### CA19-GRAPH-1

- finite graph/edge realization;
- non-backtracking Hashimoto operator;
- primitive closed-history counting;
- Mobius primitive/multiple separation;
- trace comparison;
- determinant/Euler-product theorem in the finite domain.

### CA19-ECIA-1

In the downstream ECIA/GenContinuum repository, instantiate the current source
contracts and prove independently:

- admissibility;
- weak composition preservation;
- dagger preservation;
- cyclic-shadow preservation;
- natural arithmetic shadow preservation;
- forward Phi compatibility;
- backward Psi compatibility;
- explicit information-loss matrix.

### CA20

Remain theorem-indexed and open where target mathematics is open.

RH, BSD and general Langlands are downstream comparison programs, not closure
criteria for the causal kernel.
