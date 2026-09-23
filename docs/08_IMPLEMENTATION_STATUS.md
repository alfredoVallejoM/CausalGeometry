# Implementation status — causal arithmetic foundation

Snapshot: 2026-09-23

This file records code existence only.  It does not close campaign rows: no row
is accredited until compilation, positive/control/mutation models, consumers
and audits required by PROJECT_RULES are available.

## Implemented source producers

### Event/history/process base

Existing:
- \`Foundation/EventSystem.lean\`
- \`History/Trace.lean\`
- \`Process/Diary.lean\`
- \`Process/BoundarySemantics.lean\`

The new \`BoundarySemantics\` associates a causal boundary relation to a diary
without putting semantic choices into the diary carrier.

### Extension and correlative restriction

Implemented:
- \`Foundation/ExtensionRestriction.lean\`
- \`Foundation/CorrelativeRestriction.lean\`

Available laws:
- abstract adjunction \(h_!\dashv h^*\);
- monotonicity;
- unit/counit;
- closure/interior;
- idempotence in partial orders;
- identity and composition;
- fixed-point predicates;
- canonical relation semantics;
- deterministic-map image/preimage semantics;
- composition of relational extension/restriction.

### Residual arithmetic

Implemented:
- \`Number/Residual.lean\`
- \`Number/Divisibility.lean\`
- \`Number/GCDLCM.lean\`

Available:
- left/right residuals;
- left/right multiplication monotonicity derived from adjunction;
- residual monotonicity in target and antitonicity in divisor;
- exact division as counit saturation;
- exact division iff left/right divisibility;
- multiplication as an internal extension/restriction pair;
- causal units;
- universal left/right gcd and lcm predicates;
- uniqueness up to mutual divisibility.

### Factorization and primary structure

Implemented:
- \`Number/Prime.lean\`
- \`Number/Factorization.lean\`
- \`Number/FactorizationProfile.lean\`
- \`Number/Valuation.lean\`

Available:
- compositional irreducibility distinct from cyclic primitivity;
- ordered factorization words;
- atomic-factorization predicate;
- multiplicity Finsupp as an explicit order-forgetting step;
- finite certified primary depth and uniqueness.

Not yet implemented:
- existence of primary decompositions in a substantive model;
- equivalence/non-equivalence between causal irreducibility, primitive cycles
  and classical primes;
- additive valuation law from a proved unique-primary domain.

### Classical shadows

Implemented:
- \`Number/ArithmeticShadow.lean\`
- \`Number/NatShadow.lean\`
- \`Number/AdditiveEnvelope.lean\`
- \`Number/ArithmeticSector.lean\`

Available:
- prime-profile carrier;
- multiplicative natural shadow;
- preservation of one, multiplication and powers;
- causal divisibility implies natural divisibility;
- causal units map to one;
- free commutative additive envelope kept separate from sequential
  multiplication;
- minimal sector bundling only residual multiplication and natural shadow.

The prime profile is still present for compatibility but is no longer regarded
as the deepest primitive; CA-18 requires deriving it from primary
factorization/restriction data.

### Completions

Implemented:
- \`Completion/InverseTower.lean\`
- \`Completion/SharedDepth.lean\`
- \`Completion/FinitePrimaryTower.lean\`

Available:
- inverse towers;
- coherent infinite histories;
- finite truncation;
- agreement through finite depth;
- finite towers with certified cardinality;
- a primary \(q\)-tower interface with
  \(\#A_n=q^{n+1}\).

Not yet implemented:
- the concrete tower \(\mathbb Z/p^{n+1}\mathbb Z\);
- proof that its compatible histories are equivalent to \(\mathbb Z_p\);
- general DVR tower \(\mathcal O_K/\pi^{n+1}\);
- ultrametric reconstruction.

### Cyclic and realization interfaces

Implemented:
- \`Cyclic/PrimitiveSystem.lean\`
- \`Realization/Basic.lean\`
- \`Realization/Family.lean\`

Available:
- primitive-cycle interface independent of causal primality;
- heterogeneous realization target packaged over a common source;
- composable realization comparisons;
- induced information-loss relation;
- proof that loss propagates through a comparison;
- joint-conservativity predicate.

## Current campaign interpretation

- CA-17: core mathematical producers exist for many rows; no row is marked
  closed without compilation and discriminating finite models.
- CA-18: residuation/divisibility/factorization/shadow producers exist; primary
  decomposition, Möbius/Dirichlet, CRT and concrete completions remain.
- CA-19: generic realization-family machinery exists; substantive graph,
  local-field, ECIA, Galois and automorphic realizations remain downstream.
- CA-20: specification only; RH/BSD/Langlands code is intentionally not being
  introduced before the source arithmetic is mature.

## Verification boundary

Textual repository audit currently finds no:
- \`sorry\`;
- \`admit\`;
- project-local \`axiom\`;
- \`native_decide\`;
- \`unsafe\`;
- GitHub workflows.

The current environment does not provide Lean/lake execution, so the source is
**not yet compilation-certified**.
