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

/-- Admissibility-scoped degree-one causal Hodge preservation.

The source Hodge data and representation are required only for admitted causal
numbers. This matches partial ECIA realizations and avoids forcing a Hodge
package on source objects outside the realization domain. -/
structure PreservesCausalHodgeH1OnAdmissible
    (R : ECIARealization A sourceAdmissible T)
    (K : Type w)
    [Field K]
    (sourceData :
      ∀ (X : CausalNumber A),
        sourceAdmissible X →
          CausalEventHodgeData X.system K)
    (sourceRepresentation :
      ∀ (X : CausalNumber A)
        (hX : sourceAdmissible X),
        CausalEventHodgeRepresentation
          (sourceData X hX))
    (TargetHarmonic1 :
      T.Target → Type x)
    [∀ Y, AddCommGroup (TargetHarmonic1 Y)] : Prop where

  harmonicEquiv :
    ∀ (X : CausalNumber A)
      (hX : sourceAdmissible X),
      (sourceData X hX).Harmonic1 ≃+
        TargetHarmonic1 (R.realize X)

/-- A global Hodge-preservation contract restricts canonically to any declared
admissible domain. -/
def PreservesCausalHodgeH1.toOnAdmissible
    {R : ECIARealization A sourceAdmissible T}
    {K : Type w}
    [Field K]
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
        TargetHarmonic1) :
    R.PreservesCausalHodgeH1OnAdmissible
      K
      (fun X _ => sourceData X)
      (fun X _ => sourceRepresentation X)
      TargetHarmonic1 where
  harmonicEquiv := fun X _ => h.harmonicEquiv X

namespace PreservesCausalHodgeH1OnAdmissible

variable
    {R : ECIARealization A sourceAdmissible T}
    {K : Type w} [Field K]
    {sourceData :
      ∀ (X : CausalNumber A),
        sourceAdmissible X →
          CausalEventHodgeData X.system K}
    {sourceRepresentation :
      ∀ (X : CausalNumber A)
        (hX : sourceAdmissible X),
        CausalEventHodgeRepresentation
          (sourceData X hX)}
    {TargetHarmonic1 :
      T.Target → Type x}
    [∀ Y, AddCommGroup (TargetHarmonic1 Y)]
    (h :
      R.PreservesCausalHodgeH1OnAdmissible
        K sourceData sourceRepresentation
        TargetHarmonic1)

/-- On an admitted source, causal H1 is equivalent to the target harmonic
carrier. -/
noncomputable def causalH1EquivTargetHarmonic
    (X : CausalNumber A)
    (hX : sourceAdmissible X) :
    CausalNumberH1 K X ≃+
      TargetHarmonic1 (R.realize X) :=
  (sourceRepresentation X hX)
    .harmonicAddEquivCausalH1.symm.trans
      (h.harmonicEquiv X hX)

/-- Triviality of H1 is preserved and reflected on the admitted Hodge
domain. -/
theorem h1_subsingleton_iff_targetHarmonic
    (X : CausalNumber A)
    (hX : sourceAdmissible X) :
    Subsingleton (CausalNumberH1 K X) ↔
      Subsingleton
        (TargetHarmonic1 (R.realize X)) :=
  (h.causalH1EquivTargetHarmonic X hX)
    .toEquiv.subsingleton_congr

/-- Nonzero harmonic classes remain nonzero under the admissible-domain
comparison. -/
theorem harmonic_ne_zero
    (X : CausalNumber A)
    (hX : sourceAdmissible X)
    (z : (sourceData X hX).Harmonic1)
    (hz : z ≠ 0) :
    h.harmonicEquiv X hX z ≠ 0 := by
  intro hzero
  apply hz
  apply (h.harmonicEquiv X hX).injective
  simpa using hzero

end PreservesCausalHodgeH1OnAdmissible

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
