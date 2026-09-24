# CausalGeometry development status — 2026-09-24

Current source head after this campaign: recorded by Git.

## What existed before this session

The repository already contained a substantial causal arithmetic source layer.

- CA-17: extension / correlative restriction source definitions.
- CA-18: residual arithmetic, divisibility, gcd/lcm, factorization, canonical
  profiles, valuation, CRT, incidence/Möbius, causal factorization convolution,
  Dirichlet regression, finite restriction quotients, standard p-adic inverse
  towers and ultrametric separation depth.
- CA-19: only a generic realization-family skeleton.
- CA-20: specification / research program only.

The calculus itself lagged behind the arithmetic: Difference.lean contained
only the first finite causal difference and its constant-observable law.

## Adversarial correction

The review found a real defect in ConcurrentAt: it did not require distinct
events. Consequently an event could be declared concurrent with itself even
though executing it once disables a second copy.

The correction now:

1. requires e != f in ConcurrentAt;
2. proves compatible enabled events remain enabled after executing the other;
3. derives concurrency-diamond intermediate and terminal configurations
   canonically instead of storing overridable fields;
4. proves both orders reach the same configuration.

## New causal-calculus source layer

Implemented during this session:

- Calculus/IteratedDifference.lean
  - causalSquareVariation;
  - constant square-variation law;
  - causalOrderCurvature;
  - flat concurrency implies zero order curvature.

- Calculus/Connection.lean
  - constant-fiber causal transport;
  - two path transports around a concurrency diamond;
  - FlatOn;
  - curvature;
  - flat iff curvature vanishes;
  - trivial flat connection.

- Calculus/Decomposition.lean
  - independently typed vertical, horizontal and restriction components;
  - total D = d_v + d_h + d_mu;
  - square-zero retained as an explicit property rather than an axiom.

This is still only the first closure of the calculus. Dependent fibers,
restriction-aware covariant derivatives, curvature beyond flat concurrency,
Bianchi-type identities and interaction with residual arithmetic remain to be
implemented with explicit hypotheses.

## New CA-19 realization boundary

Implemented:

- Realization/At.lean
  - RealizationAt X;
  - typed pointwise comparison morphisms;
  - identity/composition;
  - classification as equivalence, quotient/loss, completion, localization,
    analytic upgrade or conditional bridge.

- Realization/ECIAContract.lean
  - source-side ECIA target carrier contract;
  - source-to-ECIA realization map;
  - admissibility soundness;
  - separate observable-compatibility theorem interface.

CausalGeometry remains independent of ECIA/GenContinuum. The concrete ECIA
adapter belongs downstream.

## Verification infrastructure

The stale branch campaign/runtime-hydration-contracts is not merged wholesale:
it is far behind current main. Its fail-closed verification idea has instead
been ported to the current source architecture.

Added:

- runtime-profile.json;
- tools/project_runtime.py;
- tools/source_audit.py.

The runner records evidence under

verification/local-runner/by-sha/<git-sha>/

and distinguishes command failures from required manual obligations. Required
manual obligations produce an incomplete gate rather than a false PASS.

The executable gates cover:

- root import closure;
- proof-hygiene audit;
- full lake build;
- root typecheck;
- isolated calculus typecheck;
- isolated CA-19 / ECIA-contract typecheck;
- existing arithmetic-control typechecks.

## Certification boundary

The current ChatGPT execution environment has no Lean/lake installation and no
outbound network access, so the source changes made in this session have not
been compilation-certified here.

Therefore:

- source integration: yes;
- adversarial source review: partially performed;
- local Lean compilation: pending;
- full campaign accreditation: pending.

No CA row should be called closed until the local runner produces executable
evidence and the manual closure obligations have been reviewed.

## Next mathematical frontiers

Source-side order of work:

1. finish causal calculus with dependent transport, covariant/restriction
   derivatives and curvature identities;
2. finish CA-18 localization under commutative and Ore hypotheses;
3. generalize primary towers from Z/p^n to q=p^f and complete DVRs;
4. build valuation-colored graph towers and the Bruhat-Tits bridge;
5. build concrete graph/Ihara, Wilderber, local/Tate/adelic and finite-field
   CA-19 realizations;
6. instantiate the real ECIA downstream adapter;
7. keep CA-20 theorem-indexed and explicitly open wherever the target
   mathematics is open.
