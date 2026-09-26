# CausalGeometry — current source status and continuation map

Snapshot date: 2026-09-26

Source head immediately before this document:
eec1bf984dd4b7f8bd44fcff7ba60fc912a8694e

This document supersedes docs/11 and docs/12 as the active forward status.
Those documents remain historical snapshots.

## 0. Executive state

The causal source is no longer only a first-difference plus arithmetic
prototype.

The current root contains a large formal stack spanning:

- primitive event systems and derived configurations;
- histories, causal paths and diaries;
- weak process composition, dagger and cyclic shadows;
- the primitive structural pair (Phi,Psi);
- optional adjunction/restriction bridges;
- finite and linear causal differential calculus;
- one- and two-form exterior calculus;
- dependent and linear connections;
- gauge covariance, finite curvature and finite/local comparison;
- tensor transport and covariant tensor differences;
- symplectic/Hamiltonian structures;
- causal H1/H2 and presentation invariance;
- algebraic and concrete event Hodge in degree one;
- causal arithmetic, residuals, localization interfaces and factorization;
- primary completions and exact p-adic regressions;
- general q=p^f projective/DVR branching contracts;
- Bruhat--Tits graph/lattice layers;
- Hashimoto, primitive conjugacy, Euler/Ihara and determinant layers;
- typed realization families and ECIA contracts.

The 2026-09-26 wave adds a new general layer rather than replacing those
constructions:

graded causal differential geometry.

## 1. Architectural invariant

The primitive source direction remains

events
→ derived configurations
→ histories/diaries
→ (Phi,Psi)
→ optional adjunctions
→ causal geometry/arithmetic
→ realizations
→ ECIA.

The pair

Phi : A → B
Psi : B → A

does not contain inverse laws.

It does not contain an adjunction.

It does not identify Psi with a dagger, dual, transpose, inverse, pullback or
restriction unless a separate theorem does so in a named realization.

This constraint is now propagated through differential, Hodge and metric
layers.

## 2. CA-21 implementation added in this wave

### 2.1 Arbitrary-degree causal cochains

CausalGeometry/Calculus/GradedComplex.lean introduces

GradedCausalCochainComplex K C

with

d_n : C^n → C^(n+1)

and

d_(n+1) d_n = 0.

It defines:

Closed^n = ker d_n,

Exact^(n+1) = im d_n,

H^0 = ker d_0,

H^(n+1)
  = Closed^(n+1) / Exact^(n+1).

The exact-to-closed inclusion is proved degreewise.

This is deliberately abstract.  It does not pretend that the existing
event/cube geometry has already been constructed in every degree.

That concrete realization is a remaining CA-21 obligation.

### 2.2 Differential Phi/Psi defects

CausalGeometry/Calculus/PairedCochainTransport.lean introduces a
degree-preserving linear transport F and its defect

D_d(F)_n
  = d_B,n F_n - F_(n+1) d_A,n.

Naturality is equivalent to vanishing of every defect.

Composition satisfies the exact law

D_d(GF)
  = D_d(G) F + G D_d(F).

A PairedCochainTransport contains independent forward and backward transports.

Therefore

D_d(Psi Phi)
  = D_d(Psi) Phi + Psi D_d(Phi),

D_d(Phi Psi)
  = D_d(Phi) Psi + Phi D_d(Psi).

These formulas are more informative than a binary commuting/not-commuting
flag: they attribute round-trip failure to the two directions.

### 2.3 Independence controls

CausalGeometry/Models/GradedPairedControls.lean contains same-type algebraic
controls.

One model has

D_d(Phi)=0
and
D_d(Psi) != 0.

A second model reverses the situation.

Hence neither naturality direction is derivable from the other.

### 2.4 Cohomology transport

CausalGeometry/Calculus/GradedCohomologyTransport.lean proves that a natural
graded transport maps

closed → closed
and
exact → exact.

It therefore induces:

H^0(A) → H^0(B),

H^(n+1)(A) → H^(n+1)(B).

Phi and Psi produce independent maps when their own defects vanish.

The two induced round trips remain endomorphisms; no identity law is assumed.

CausalGeometry/Calculus/GradedCohomologyFunctoriality.lean now proves:

- identity transport induces identity on H^0 and all H^(n+1);
- composition of transports induces composition on cohomology;
- source/target cohomological round trips agree with the cohomology map
  induced by the corresponding graded round-trip transport.

Thus the arbitrary-degree cohomology layer is actually functorial, not only
quotient-valued.

### 2.5 Graded Hodge

CausalGeometry/Calculus/GradedHodge.lean defines:

delta_n : C^(n+1) → C^n,

degreewise pairings,

the adjointness law between d_n and delta_n,

Delta_0 = delta_0 d_0,

Delta_(n+1)
  = d_n delta_n + delta_(n+1)d_(n+1).

Harmonic spaces are kernels of Delta.

Positive-degree Hodge representation is deliberately external data requiring:

1. harmonic implies closed;
2. every closed cochain decomposes as exact + harmonic;
3. exact and harmonic intersect trivially.

Under exactly those hypotheses:

Harmonic^(n+1) ≃ H^(n+1).

No positivity or finite-dimensional theorem is silently assumed.

### 2.6 Degree-zero Hodge

CausalGeometry/Calculus/GradedHodgeZero.lean treats degree zero separately.

Since there is no incoming negative differential, the exact hypothesis is an
equality of the harmonic and closed kernels.

Under the two inclusions

Harmonic^0 <= Closed^0
and
Closed^0 <= Harmonic^0

the source constructs

Harmonic^0 ≃ H^0.

### 2.7 Phi/Psi Hodge defects

CausalGeometry/Calculus/PairedHodgeTransport.lean defines independent defects

D_delta(Phi),
D_delta(Psi),
D_Delta(Phi),
D_Delta(Psi).

It proves

D_d(Phi)=0 and D_delta(Phi)=0
=> D_Delta(Phi)=0,

with a separate theorem for Psi.

Laplacian-intertwining transports harmonic states.

### 2.8 Hodge/cohomology coherence

CausalGeometry/Calculus/GradedHodgeCohomology.lean proves that harmonic
transport and cohomology transport commute with the Hodge identification.

For Phi, the square is

Harm_A^(n+1)  --Phi_Harm-->  Harm_B^(n+1)
      |                         |
      | Hodge_A                 | Hodge_B
      v                         v
H_A^(n+1)      --Phi_H---->   H_B^(n+1)

and the same theorem is proved independently for Psi.

Therefore the Hodge and cohomology APIs are not parallel unrelated structures.

### 2.9 General tensor interface

CausalGeometry/Calculus/GeneralTensor.lean introduces a typed arbitrary-rank
interface

T^(p,q)

with:

- tensor product;
- contraction;
- contravariant slot permutations;
- covariant slot permutations;
- transport naturality for tensor products;
- transport naturality for contraction.

The interface deliberately does not yet claim that one concrete Lean
TensorProduct implementation realizes all these operations.

That construction and its coherence laws remain an explicit obligation.

The earlier vacuous contraction predicate was removed.  Linearity is already
encoded by the LinearMap type; real contraction compatibility must be proved
in a concrete realization.

### 2.10 Metric causal geometry

CausalGeometry/Calculus/CausalMetric.lean introduces a symmetric nondegenerate
bilinear metric

g : V × V → K.

No positive-definite or Lorentzian signature assumption is built in.

Finite connection transport is metric-compatible when

g(T_e x,T_e y)=g(x,y)

for each enabled event.

The source proves such a primitive transport is injective.

It does not infer surjectivity/reversibility.

### 2.11 Metric Phi/Psi defects

CausalGeometry/Calculus/CausalMetricTransport.lean defines

D_g(Phi)(x,y)
  = g_B(Phi x,Phi y)-g_A(x,y),

D_g(Psi)(u,v)
  = g_A(Psi u,Psi v)-g_B(u,v).

The round-trip failure decomposes exactly:

D_g(Psi Phi)(x,y)
  =
D_g(Psi)(Phi x,Phi y)
+
D_g(Phi)(x,y).

The target formula is symmetric.

When both directional defects vanish, each round trip is metric preserving.

Again, no inverse law is inferred.

### 2.12 Discrete variational action

CausalGeometry/Variational/DiscreteAction.lean adds:

- concatenation of causal paths;
- length additivity;
- a local causal step Lagrangian;
- finite path action;
- action additivity under concatenation;
- action difference between same-endpoint histories;
- concurrency-square action-order defect.

The square defect changes sign under orientation reversal.

Its vanishing is exactly equality of the two local two-step actions.

### 2.13 Variational boundary gauge

CausalGeometry/Variational/ActionGauge.lean proves the discrete boundary law.

For

L' = L + B(C') - B(C),

one has

S_L'(p)
  =
S_L(p) + B(final)-B(initial).

Consequently same-endpoint action differences are invariant.

The local concurrency-square action defect is also invariant.

This is the correct precursor to a causal Euler--Lagrange/Noether layer:
boundary changes have already been factored out before stationarity is defined.

## 3. ECIA arbitrary-degree source contracts

CausalGeometry/Realization/ECIAGradedContract.lean adds two independent
source-side contracts.

PreservesGradedCausalCohomology supplies linear equivalences between all
supported source H^n groups and target ECIA cohomology carriers.

PreservesGradedCausalHodge supplies linear equivalences between source
positive-degree harmonic spaces and target harmonic carriers.

When source Hodge representation is available, the source derives

H_C^(n+1)(X)
  ≃
Harm_ECIA^(n+1)(R X).

This remains a contract.

It is not evidence that the real ECIA target has already instantiated it.

CA-23 exists precisely to prevent that confusion.

## 4. What is already stronger than the old roadmap

The 2026-09-24 roadmap listed several items as future that are now source
code:

- dependent linear connections;
- tensor transport;
- covariant tensor differences;
- finite/local curvature comparison;
- finite Bianchi;
- general q=p^f projective/DVR branching contracts;
- universal q+1 Bruhat--Tits regularity;
- extensive concrete p-adic lattice geometry;
- finite graph/Hashimoto/Ihara layers;
- primitive conjugacy spectra;
- H1/H2 presentation invariance and functoriality;
- Hodge H1 and concrete event-Hodge realization;
- ECIA cohomology/Hodge preservation contracts.

For this reason docs/12 is now explicitly marked historical.

## 5. Real CA-21 frontier

The main remaining source theorem chain is:

arbitrary event/cube k-cochains
→ full exterior d in every degree
→ concrete event realization of GradedCausalCochainComplex
→ wedge/cup and graded Leibniz
→ concrete higher H^n
→ finite-dimensional Hodge decomposition theorem
→ Hodge star / Green / spectrum where hypotheses permit
→ concrete arbitrary-rank TensorProduct realization
→ torsion / metric-compatible connection comparison
→ Levi-Civita-type uniqueness on a named causal domain
→ curvature contractions
→ discrete Euler--Lagrange / symmetry / Noether / singular constraints.

The abstract graded infrastructure is now present; the next hard step is the
concrete event/cubical realization.

## 6. Real CA-22 frontier

CA-22 does not need another abstract q=p^f cardinality layer.

The source already has:

- prime-power local-ring towers;
- DVR residue contracts;
- projective sphere cardinal (q+1)q^n;
- q-element projective reduction fibers;
- a universal q+1 regular Bruhat--Tits graph;
- a strong Q_p/F_p lattice regression.

The genuine remaining localization/local-field work is:

- derive a canonical right localization calculus from explicit Ore plus the
  necessary reversibility/cancellation hypotheses;
- derive the left calculus independently;
- prove the universal properties without supplying target coherence as data;
- construct the left/right bilateral comparison under exact two-sided
  hypotheses;
- develop a genuinely nonclassical factorization domain;
- construct general rank-two local-field lattices;
- compare their homothety tree with the existing abstract projective tree.

## 7. Real CA-23 frontier

CA-23 is downstream.

CausalGeometry has source contracts; it must remain independent of ECIA.

The ECIA/GenContinuum repository must instantiate:

- admissibility;
- weak composition;
- dagger;
- cyclic shadow;
- arithmetic shadow;
- Phi;
- Psi;
- differential defects;
- H^n;
- harmonic H^n;
- transfer signatures;
- primitive/Ihara signatures;
- Bruhat--Tits arithmetic provenance.

It must also publish an information-loss matrix.

Equality of a numerical shadow is never enough to conclude equality of causal
sources.

## 8. CA-24 and CA-25 boundaries

CA-24 is the typed realization expansion:

Frobenius, point counting, Hecke, Tate, adeles, Galois, Weil--Deligne,
Schreier, dessins, controlled F1 loss, p-adic Hodge, automorphic,
operatorial/KMS/Tomita and elliptic/local-global targets.

CA-25 is the analytic layer:

completed spaces, operator domains, closedness, adjoints, compactness,
trace-class/nuclear control, Fredholm determinants, convergence, regularizers,
local/global products, functional equations and positivity.

Finite Ihara identities are regressions for this layer, not proofs of it.

RH, general BSD and general Langlands remain explicitly open theorem endpoints.

## 9. Verification state

The root currently imports 232 modules at the pre-document snapshot plus the
new CA-21 modules added during this wave.

The runtime profile has dedicated required gates:

CA21-GRADED-TYPECHECK

and

CA23-GRADED-ECIA-TYPECHECK.

The CA-21 gate individually typechecks the new graded, Hodge, tensor, metric,
variational and mutation-control modules.

The static audit performed before this document found no occurrence in the new
Lean/program files of:

- sorry;
- admit;
- native_decide;
- unsafe;
- project-local axiom declarations.

All new source modules inspected by that audit were imported by the root.

However, this execution environment does not provide Lean/lake.

Therefore the correct status is:

SOURCE-IN-PROGRESS / STATICALLY-AUDITED / LOCAL-TYPECHECK-PENDING.

No CA-21 row is campaign-accredited merely from this development session.

## 10. Immediate execution order

The next exact source sequence should be:

CA21-CUBE-1:
construct arbitrary-degree event/cubical cochains and the concrete graded
complex.

CA21-ALG-1:
wedge/cup, permutations, graded Leibniz and relative cohomology.

CA21-HODGE-2:
derive Hodge representation from finite-dimensional/nondegenerate hypotheses
instead of supplying it.

CA21-TENSOR-2:
realize the abstract T^(p,q) interface concretely and add slot-aware
contractions.

CA21-GEOM-2:
torsion, metric compatibility, Levi-Civita-type theorem and contracted
curvatures.

CA21-VAR-2:
discrete variations, Euler--Lagrange, symmetry, momentum, Noether and
constraint systems.

Only after the CA-21 concrete graded geometry is stable should source work
move aggressively into the general Ore quotient construction in CA-22.

In parallel, CA-23 may proceed in the downstream ECIA repository because its
contracts are source-side independent.

## 11. Campaign ledger

The formal Program/Campaign and Program/Ledger modules now contain CA21--CA25.

Counts:

CA21 = 64
CA22 = 40
CA23 = 32
CA24 = 40
CA25 = 32

Second extension = 208.

Full program = 636 atomic obligations.

These counts are checked by Lean `decide` declarations in the ledger source;
their compilation still belongs to the exact-SHA local runner gate.
