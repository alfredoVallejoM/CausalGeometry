# Project rules

CausalGeometry is the independent Lean home of primitive causal events,
derived histories/diaries, structural forward/backward transport, causal
arithmetic, optional correlative adjunction bridges, causal calculus and typed
realizations.

## Hard architectural constraints

- The stable causal kernel depends on mathlib only.
- Primitive ontology starts from events and their causal/conflict relations.
  Configurations, executions, histories, fibers and geometric/state-space
  realizations are derived constructions.
- The foundational transport object is a structural pair
  `PairedTransform(α,β) = (Phi : α -> β, Psi : β -> α)`.
  No inverse, adjunction, dagger, duality or semantic reading is assumed by
  that carrier.
- An ordered adjunction `Phi(a) <= b <-> a <= Psi(b)` is an explicit
  `AdjointBridge` / `ExtensionRestriction` specialization. It is important
  but is not silently imposed on every causal/restriction pair.
- Relational possibility semantics and geometric pullback are realizations or
  models of the structural pair. They are not the ontology of primitive
  events.
- GenContinuum, ECIA, RenormCore and Wilderber are realization targets or
  comparison sources, never dependencies of the kernel.
- Do not create GitHub Actions, workflows, CI files or automation
  configuration.
- Do not use `sorry`, `admit`, project-local axioms, `unsafe` proof
  shortcuts or `native_decide` as substitutes for mathematical
  certification.
- Correlative restriction, causal dagger and algebraic dual remain distinct
  primitives/constructions until a theorem compares them.
- Sequential composition, parallel product, additive envelope, action, cyclic
  shadow, valuation, length and modular flow remain distinct.
- Prime profiles and classical valuations are derivation targets; do not make
  them hidden primitive fields of a causal number when the causal
  factorization/restriction layer can produce them.
- External realizations live over a causal source; do not add graph, Galois,
  Hecke, Selmer, ECIA or spectral data as optional fields of `CausalNumber`.
- Do not call a target-specific comparison a derivation until a typed
  realization theorem exists.
- The separate generative-dynamic motive campaign is out of scope for this
  repository program unless explicitly reopened by the user.
- RH, BSD, general Langlands, general Tomita--Takesaki, general Selmer,
  general Fredholm identification, Bloch--Kato, ETNC and strong ECIA
  unification remain open unless separately proved.

## Closure contract

A campaign row closes only when it has:
1. a mathematical declaration;
2. a positive model;
3. a same-type control;
4. a same-type mutation that fails;
5. a real consumer;
6. an adversarial review;
7. an axiomatic/import audit;
8. a resource audit when the construction can be expensive.

## Verification policy

Verification is local/reproducible. The absence of a GitHub workflow is
intentional and must not be “fixed” by adding one.
