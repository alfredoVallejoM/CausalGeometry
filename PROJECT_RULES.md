# Project rules

CausalGeometry is the independent Lean home of causal diaries, causal arithmetic,
causal calculus and their typed realizations.

## Hard architectural constraints

- The stable causal kernel depends on mathlib only.
- GenContinuum, ECIA, RenormCore and Wilderber are realization targets or
  comparison sources, never dependencies of the kernel.
- Do not create GitHub Actions, workflows, CI files or automation configuration.
- Do not use `sorry`, `admit`, project-local axioms, `unsafe` proof shortcuts
  or `native_decide` as substitutes for mathematical certification.
- Do not collapse sequential composition, parallel composition, additive
  envelope, action, cyclic shadow, dagger, valuation, length or modular flow.
- Do not call a target-specific comparison a derivation until a typed
  realization theorem exists.
- RH, BSD, general Tomita--Takesaki, general Selmer, general Fredholm
  identification and strong ECIA unification remain open unless separately
  proved.

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
