import CausalGeometry.Calculus.EventHodge
import CausalGeometry.Realization.ECIACohomologyContract

namespace CausalGeometry

universe u v w x

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- ECIA preservation of degree-one causal Hodge structure.

The source harmonic space is computed from the concrete event/configuration
cochain complex.  The target may use any internal representation of harmonic
states; only an additive equivalence is required. -/
structure PreservesCausalHodgeH1
    (R : ECIARealization A sourceAdmissible T)
    (K : Type w)
    [Field K]
    (sourceData :
      ∀ X : CausalNumber A,
        CausalEventHodgeData X.system K)
    (sourceRepresentation :
      ∀ X : CausalNumber A,
        CausalEventHodgeRepresentation
          (sourceData X))
    (TargetHarmonic1 :
      T.Target → Type x)
    [∀ Y, AddCommGroup (TargetHarmonic1 Y)] : Prop where

  harmonicEquiv :
    ∀ X : CausalNumber A,
      (sourceData X).Harmonic1 ≃+
        TargetHarmonic1 (R.realize X)

namespace PreservesCausalHodgeH1

variable
    {R : ECIARealization A sourceAdmissible T}
    {K : Type w} [Field K]
    {sourceData :
      ∀ X : CausalNumber A,
        CausalEventHodgeData X.system K}
    {sourceRepresentation :
      ∀ X : CausalNumber A,
        CausalEventHodgeRepresentation
          (sourceData X)}
    {TargetHarmonic1 :
      T.Target → Type x}
    [∀ Y, AddCommGroup (TargetHarmonic1 Y)]
    (h :
      R.PreservesCausalHodgeH1
        K sourceData sourceRepresentation
        TargetHarmonic1)

/-- The source causal H1 group is therefore equivalent directly to the target
harmonic degree-one space. -/
noncomputable def causalH1EquivTargetHarmonic
    (X : CausalNumber A) :
    CausalNumberH1 K X ≃+
      TargetHarmonic1 (R.realize X) :=
  (sourceRepresentation X)
    .harmonicAddEquivCausalH1.symm.trans
      (h.harmonicEquiv X)

/-- Triviality of source causal H1 is equivalent to triviality of the target
harmonic space. -/
theorem h1_subsingleton_iff_targetHarmonic
    (X : CausalNumber A) :
    Subsingleton (CausalNumberH1 K X) ↔
      Subsingleton
        (TargetHarmonic1 (R.realize X)) := by
  exact
    (h.causalH1EquivTargetHarmonic X)
      .toEquiv.subsingleton_congr

/-- Nontrivial harmonic content is preserved and reflected. -/
theorem h1_nontrivial_iff_targetHarmonic
    (X : CausalNumber A) :
    Nontrivial (CausalNumberH1 K X) ↔
      Nontrivial
        (TargetHarmonic1 (R.realize X)) := by
  constructor
  · intro hs
    exact
      Equiv.nontrivial
        (h.causalH1EquivTargetHarmonic X).toEquiv
  · intro ht
    exact
      Equiv.nontrivial
        (h.causalH1EquivTargetHarmonic X).symm.toEquiv

/-- Finite harmonic multiplicity is preserved exactly. -/
theorem harmonic_natCard_eq_h1
    (X : CausalNumber A)
    [Finite (CausalNumberH1 K X)]
    [Finite
      (TargetHarmonic1 (R.realize X))] :
    Nat.card
        (TargetHarmonic1 (R.realize X)) =
      Nat.card (CausalNumberH1 K X) := by
  exact
    Nat.card_congr
      (h.causalH1EquivTargetHarmonic X).toEquiv.symm

/-- A nonzero source harmonic representative maps to a nonzero target
harmonic state. -/
theorem harmonic_ne_zero
    (X : CausalNumber A)
    (z : (sourceData X).Harmonic1)
    (hz : z ≠ 0) :
    h.harmonicEquiv X z ≠ 0 := by
  intro hzero
  apply hz
  apply (h.harmonicEquiv X).injective
  simpa using hzero

end PreservesCausalHodgeH1
end ECIARealization
end CausalGeometry
