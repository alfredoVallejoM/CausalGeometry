# Implementation status — causal arithmetic foundation

Snapshot: 2026-09-23

> **Foundation-lift note (2026-09-24).** The implementation below remains
> valid as the ordered **adjoint specialization**. The primitive structural
> carrier is now `PairedTransform (Phi,Psi)`, which assumes no adjunction.
> `AdjointBridge` recovers `ExtensionRestriction` when the adjunction is
> separately proved. Primitive ontology starts from events; configurations and
> histories remain derived.

This file records source implementation status only. A campaign row is not
accredited until compilation plus the positive/control/mutation/consumer/audit
contract in PROJECT_RULES has been satisfied.

## Event/history/process base

Implemented:
- Foundation/EventSystem.lean
- History/Trace.lean
- Process/Diary.lean
- Process/BoundarySemantics.lean

Boundary semantics remain separate from diary syntax and induce a relational
forward/restriction semantics when chosen.

## Extension and correlative restriction

Implemented:
- Foundation/ExtensionRestriction.lean
- Foundation/CorrelativeRestriction.lean

Available:
- abstract adjunction \(h_!\dashv h^*\);
- monotonicity;
- unit/counit;
- closure \(h^*h_!\) and realizable interior \(h_!h^*\);
- idempotence on partial orders;
- identity/composition;
- fixed-point predicates;
- canonical relation semantics;
- deterministic image/preimage specialization;
- composition of relational extension/restriction.

## Residual arithmetic

Implemented:
- Number/Residual.lean
- Number/Divisibility.lean
- Number/DivisibilityOrder.lean
- Number/DivisibilityClasses.lean
- Number/GCDLCM.lean
- Number/ArithmeticSector.lean
- Number/CanonicalIncidence.lean

Available:
- left/right residuals;
- left/right multiplication monotonicity derived from adjunction;
- residual monotonicity/antitonicity;
- exact division as counit saturation;
- exact division iff left/right divisibility;
- left/right divisibility preorders;
- canonical antisymmetrization by mutual divisibility;
- causal units collapse to the identity divisor class;
- separate left/right canonical Möbius theories whenever locally finite;
- causal units;
- universal left/right gcd and lcm;
- multiplication by a fixed causal element packaged as an
  ExtensionRestriction pair.

## Factorization, primary structure and valuation

Implemented:
- Number/Prime.lean
- Number/Factorization.lean
- Number/FactorizationProfile.lean
- Number/FactorizationPrimeRealization.lean
- Number/PrimaryDecomposition.lean
- Number/Valuation.lean
- Number/CanonicalAtomicDomain.lean
- Models/NatArithmetic.lean

Available:
- compositional irreducibility distinct from cyclic primitivity;
- ordered causal factorization words;
- concatenation of atomic factorizations;
- causal multiplicity Finsupp before classical prime labels;
- profile value at one factor equals list multiplicity/count;
- certified finite primary depth;
- canonical atomic domains with uniqueness of multiplicity profile;
- derived profile law
  \[
  \nu_C(XY)=\nu_C(X)+\nu_C(Y);
  \]
- derived valuation law
  \[
  v_P(XY)=v_P(X)+v_P(Y);
  \]
- natural-number regression:
  \[
  \operatorname{Irreducible}_C(n)\iff n\text{ prime};
  \]
- causal prime-factor profile equals Nat.factorization pointwise;
- classical prime multiplicities are additive on nonzero products.

Still open:
- existence/uniqueness of canonical primary factorization in a genuinely
  richer nonclassical/noncommutative causal arithmetic domain;
- comparison between compositional irreducibility and cyclic primitivity
  beyond regression models.

## Classical shadows and CRT

Implemented:
- Number/ArithmeticShadow.lean
- Number/NatShadow.lean
- Number/AdditiveEnvelope.lean
- Number/CRT.lean
- Number/PrimaryDecomposition.lean

Available:
- classical prime profile as a derived realization;
- multiplicativity of PrimeProfile.value;
- profile-from-factor-list;
- value of a derived prime profile equals the natural multiplicative shadow;
- finite causal primary decomposition with causal bases/exponents;
- separate injective realization of primary bases by classical primes;
- product reconstruction
  \[
  \chi(X)=\prod_i p_i^{e_i};
  \]
- pairwise coprimality of realized independent primary channels;
- CRT equivalence
  \[
  \mathbb Z/\chi(X)\mathbb Z
  \simeq
  \prod_i\mathbb Z/p_i^{e_i}\mathbb Z.
  \]

## Incidence and Möbius

Implemented:
- Number/Incidence.lean
- Number/CanonicalIncidence.lean
- Models/NatDivisorIncidence.lean
- Models/NatIncidenceMobiusComparison.lean
- Models/NatMobiusRegression.lean
- Models/ArithmeticCoreControls.lean

Available:
- explicit left/right finite divisor presentations;
- intrinsic left/right divisor-class antisymmetrizations;
- incidence zeta and Möbius;
- both inverse laws
  \[
  \mu_C*\zeta_C=1=\zeta_C*\mu_C;
  \]
- Möbius inversion on lower divisor intervals;
- product-channel factorization of Möbius;
- product-channel multiplicativity of incidence Euler characteristic;
- finite natural divisor poset ordered by divisibility rather than numerical
  order;
- exact identification of lower causal intervals with classical divisor
  finsets;
- exact comparison
  \[
  \mu_{D(n)}(1,d)=\mu_{\rm arith}(d);
  \]
- Euler characteristic identity
  \[
  \chi_{\rm Euler}(D(n))=\mu(n);
  \]
- discriminating controls:
  prime gives \(-1\), prime square gives \(0\);
- general prime-power cancellation;
- squarefree sign law.

This implements the source content of CA-18.25 and CA-18.26. Campaign closure
still requires actual Lean compilation and full evidence.

## Factorization convolution and Dirichlet realization

Implemented:
- Number/FactorizationConvolution.lean
- Models/NatMobiusRegression.lean

Available:
- generic finite ordered factorization systems;
- generic convolution
  \[
  (f\star_Cg)(X)=\sum_{AB=X}f(A)g(B);
  \]
- bundled causal arithmetic functions vanishing outside the admissible domain;
- closure of causal arithmetic functions under factorization convolution;
- natural-number factorization system from Nat.divisorsAntidiagonal;
- equivalence
  \[
  \operatorname{CAF}_{\mathbb N}(R)
  \simeq
  \operatorname{ArithmeticFunction}(R);
  \]
- exact transport of causal factorization convolution to Dirichlet
  convolution;
- classical Möbius/zeta inversion as a regression target.

This implements the source content of CA-18.27 while keeping incidence
convolution and factorization convolution separately typed.

## Primary completions and p-adic realization

Implemented:
- Completion/InverseTower.lean
- Completion/SharedDepth.lean
- Completion/FinitePrimaryTower.lean
- Completion/ZModPrimeTower.lean

Available:
- inverse towers and compatible infinite histories;
- extensionality by all finite observations;
- nested finite-depth equivalence relations;
- causal depth balls;
- deeper balls contained in shallower balls;
- equal-depth balls are equal or disjoint;
- finite truncation quotients;
- quotient maps form an inverse system;
- quotient evaluation into finite levels is injective;
- equivalence to a finite level whenever all finite states extend;
- concrete primary tower
  \[
  A_n=\mathbb Z/p^{n+1}\mathbb Z;
  \]
- cardinality \(p^{n+1}\);
- every finite residue extends to a completed p-adic history;
- exact finite quotient equivalence
  \[
  Hist/{\sim_n}\simeq\mathbb Z/p^{n+1}\mathbb Z;
  \]
- compatibility of these equivalences with modular reduction;
- full inverse-limit equivalence
  \[
  Hist_\infty(A_\bullet)\simeq\mathbb Z_p;
  \]
- exact ball realization
  \[
  x\sim_n y
  \iff
  \|x-y\|_p\le p^{-(n+1)};
  \]
- equality of causal depth balls with ordinary p-adic closed metric balls;
- exact first-separation theorem for \(x\ne y\):
  \[
  x\sim_ny\iff n<v_p(x-y);
  \]
- exact norm law
  \[
  \|x-y\|_p=p^{-v_p(x-y)}.
  \]

This now implements the standard p-adic content of CA-18.29, CA-18.30 and
CA-18.31 at source level.

Still open:
- general DVR tower \(\mathcal O_K/\pi^{n+1}\);
- general \(q=p^f\) local reconstruction;
- valuation-colored graph realization of these towers.

## Concrete noncommutative model

Implemented:
- Models/RelationArithmetic.lean
- Models/RelationArithmeticExample.lean

Binary relations under composition form a canonical residuated causal
arithmetic. A finite Bool example proves multiplication is genuinely
noncommutative before decategorification.

## Cyclic and realization interfaces

Implemented:
- Cyclic/PrimitiveSystem.lean
- Realization/Basic.lean
- Realization/Family.lean

Available:
- primitive-cycle interface independent of causal primality;
- heterogeneous target realizations over one common source;
- composable comparison maps;
- realization-induced information-loss relation;
- loss propagation through comparison;
- joint-conservativity predicate.

## Campaign interpretation

- CA-17: central extension/restriction producers and a canonical relational
  model exist. Rows remain unaccredited until compilation and the complete
  evidence contract are available.
- CA-18: source implementations now exist for residuation, divisibility,
  factorization, profile-derived valuation additivity, CRT, incidence/Möbius,
  factorization/Dirichlet convolution, finite restriction quotients, standard
  p-adic completion and exact ultrametric separation depth.
- CA-18 remaining mathematical source frontier is concentrated in general
  localization/Ore fractions, genuinely nonclassical primary uniqueness,
  general \(q=p^f\)/DVR reconstruction and the bridge to graph/Ihara geometry.
- CA-19: generic realization-family machinery exists; substantive ECIA,
  graph/Ihara, Galois, Hecke and automorphic adapters remain downstream.
- CA-20: specification only. RH/BSD/Langlands theorem code remains downstream
  of a mature source arithmetic.

## Verification boundary

Textual repository audit is required to remain free of:
- sorry;
- admit;
- project-local axioms;
- native_decide;
- unsafe proof shortcuts;
- GitHub workflows.

The current execution environment does not provide Lean/lake, so these source
modules are **not yet compilation-certified**.
