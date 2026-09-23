# Implementation status — causal arithmetic foundation

Snapshot: 2026-09-23

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
- canonical relation model;
- deterministic image/preimage specialization;
- compositional laws for relational extension/restriction.

## Residual arithmetic

Implemented:
- Number/Residual.lean
- Number/Divisibility.lean
- Number/DivisibilityOrder.lean
- Number/GCDLCM.lean
- Number/ArithmeticSector.lean

Available:
- left/right residuals;
- multiplication monotonicity derived from adjunction;
- residual monotonicity/antitonicity laws;
- exact left/right division as counit saturation;
- exact division iff left/right divisibility;
- left/right divisibility preorders;
- causal units;
- universal left/right gcd and lcm;
- multiplication by a fixed causal element packaged as an
  ExtensionRestriction pair.

## Factorization and classical shadow

Implemented:
- Number/Prime.lean
- Number/Factorization.lean
- Number/FactorizationProfile.lean
- Number/FactorizationPrimeRealization.lean
- Number/PrimaryDecomposition.lean
- Number/Valuation.lean
- Number/ArithmeticShadow.lean
- Number/NatShadow.lean
- Number/AdditiveEnvelope.lean
- Models/NatArithmetic.lean

Available:
- compositional irreducibility distinct from cyclic primitivity;
- ordered causal factorization words;
- atomic-factorization predicate;
- causal multiplicity profiles before classical prime labels;
- certified finite primary depth;
- classical prime profile derived from a causal atomic factorization plus a
  separate prime realization;
- value of the derived profile equals the multiplicative natural shadow;
- finite causal primary decompositions with causal bases and exponents;
- separate injective realization of primary bases by classical primes;
- classical product formula derived from that realization;
- pairwise coprimality of realized primary channels;
- CRT realization of those channels;
- natural-number regression model using Nat.primeFactorsList;
- every classical natural prime is compositionally irreducible in that model;
- the derived profile evaluates exactly to the original nonzero natural.

Still open:
- a non-classical theorem proving existence/uniqueness of primary
  decompositions in a genuinely richer causal arithmetic domain;
- comparison theorem among causal irreducibility, cyclic primitivity and
  classical primality beyond regression models;
- valuation additivity on a proved causal unique-primary domain;
- Möbius/incidence and Dirichlet-convolution layers.

## Primary completions

Implemented:
- Completion/InverseTower.lean
- Completion/SharedDepth.lean
- Completion/FinitePrimaryTower.lean
- Completion/ZModPrimeTower.lean
- Number/CRT.lean

Available:
- inverse towers and compatible infinite histories;
- explicit extensionality from all finite observations;
- finite restriction agreement;
- finite towers with certified cardinality law;
- concrete primary residue tower
  \[
  A_n=\mathbb Z/p^{n+1}\mathbb Z;
  \]
- native reduction maps via ZMod;
- finite-level cardinality \(p^{n+1}\);
- packaging as a primary FiniteInverseTower;
- map
  \[
  \mathbb Z_p\to \operatorname{CompatibleHistory}(A_\bullet)
  \]
  using PadicInt.toZModPow;
- reconstruction of a p-adic integer from an arbitrary compatible history via
  PadicInt.ofIntSeq;
- proof that the reconstructed integer has every prescribed finite
  restriction;
- two-sided inverse theorems;
- explicit equivalence
  \[
  \boxed{
  \operatorname{CompatibleHistory}(A_\bullet)\simeq\mathbb Z_p.
  }
  \]
- native two-channel and finite-family CRT targets.

Still open:
- general DVR tower \(\mathcal O_K/\pi^{n+1}\);
- general \(q=p^f\) local reconstruction;
- ultrametric reconstruction from maximal common restriction depth;
- causal derivation of the primary channel split before applying the native
  ZMod CRT target.

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

- CA-17: the central extension/restriction producers and a canonical relational
  model exist. Rows remain unaccredited until compilation and the full evidence
  contract are available.
- CA-18: residuation, divisibility, factorization, primary depth, natural
  regression, CRT and concrete p-adic completion producers now exist. The
  Möbius/Dirichlet layer, richer primary uniqueness and general local fields
  remain.
- CA-19: generic realization-family machinery exists; substantive ECIA,
  graph/Ihara, Galois, Hecke and automorphic adapters remain downstream.
- CA-20: specification only. RH/BSD/Langlands theorem code is intentionally
  downstream of a mature source arithmetic.

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
