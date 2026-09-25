import CausalGeometry.Calculus.SymplecticGeometry
import CausalGeometry.Models.BilinearHamiltonianControls
import Mathlib.Tactic

namespace CausalGeometry.Models

open EventSystem

/-- The already constructed standard alternating/nondegenerate field packaged
as an algebraic symplectic field. -/
def standardSymplecticStructure :
    CausalBilinear.SymplecticField
      (K := ℤ)
      (S := twoEventSystem)
      (Fiber := fun _ => ℤ × ℤ) where
  toField := standardSymplecticField
  alternating :=
    standardSymplecticField_alternating
  nondegenerate :=
    standardSymplecticField_nondegenerate

/-- Event directions false,true are represented by the standard basis vectors
e1,e2 respectively. -/
def standardSoldering :
    CausalSoldering
      twoEventSystem
      (fun _ => ℤ × ℤ) where
  vector := fun _ d =>
    if d.event then (0, 1) else (1, 0)

@[simp] theorem standardSoldering_false
    (C : Configuration twoEventSystem)
    (h : twoEventSystem.Enabled C false) :
    standardSoldering.vector C
      ⟨false, h⟩ =
      (1, 0) := by
  rfl

@[simp] theorem standardSoldering_true
    (C : Configuration twoEventSystem)
    (h : twoEventSystem.Enabled C true) :
    standardSoldering.vector C
      ⟨true, h⟩ =
      (0, 1) := by
  rfl

/-- Identity transport preserves the event-vector soldering. -/
theorem identity_preserves_standardSoldering :
    standardSoldering.PreservedBy
      identityDependentEquivConnection.toLinearConnection := by
  intro C e f d
  change
    (if f then (0, 1) else (1, 0)) =
      (LinearEquiv.refl ℤ (ℤ × ℤ))
        (if f then (0, 1) else (1, 0))
  simp

/-- Fully compatible causal symplectic connection. -/
def standardCausalSymplecticConnection :
    CausalSymplecticConnection
      ℤ twoEventSystem
      (fun _ => ℤ × ℤ) where
  connection :=
    identityDependentEquivConnection
  form :=
    standardSymplecticStructure
  soldering :=
    standardSoldering
  preservesForm :=
    identity_preserves_standardSymplectic
  preservesSoldering :=
    identity_preserves_standardSoldering

/-- The induced causal two-form is genuinely nonzero on the basic
false/true concurrency diamond. -/
theorem standard_eventTwoForm_basic :
    standardCausalSymplecticConnection.toGeometry.eventTwoForm.value
        twoEventDiamond =
      1 := by
  norm_num [
    CausalSymplecticConnection.toGeometry,
    CausalSymplecticGeometry.eventTwoForm,
    CausalSoldering.inducedTwoForm,
    standardCausalSymplecticConnection,
    standardSymplecticStructure,
    standardSymplecticField,
    standardSymplecticForm,
    standardSoldering,
    CausalOneForm.baseE,
    CausalOneForm.baseF,
    twoEventDiamond
  ]

/-- The same nonzero event two-form is nevertheless closed. -/
theorem standard_eventTwoForm_closed :
    standardCausalSymplecticConnection.toGeometry.eventTwoForm.Closed :=
  standardCausalSymplecticConnection.toGeometry.eventTwoForm_closed

/-- Same fiber type and invertible linear transport, but every vector is
negated at each event. -/
def negDependentEquivConnection :
    DependentLinearEquivConnection
      ℤ twoEventSystem
      (fun _ => ℤ × ℤ) where
  transport := fun _ _ _ =>
    LinearEquiv.neg ℤ

/-- Negating both vector arguments preserves the alternating bilinear form. -/
theorem neg_preserves_standardSymplectic :
    standardSymplecticField.PreservedByEquiv
      negDependentEquivConnection := by
  intro C e h x y
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp [
    CausalBilinear.PreservedByEquiv,
    CausalBilinear.Field.PreservedBy,
    standardSymplecticField,
    standardSymplecticForm,
    negDependentEquivConnection
  ]
  ring

/-- But negation does not preserve the soldering: the true direction remains
represented by e2, while transported e2 becomes -e2. -/
theorem neg_not_preserve_standardSoldering :
    ¬ standardSoldering.PreservedBy
        negDependentEquivConnection.toLinearConnection := by
  intro h
  have htest := h twoEventDiamond
  norm_num [
    standardSoldering,
    negDependentEquivConnection,
    DependentLinearEquivConnection.toLinearConnection,
    CausalOneForm.afterE_F,
    CausalOneForm.baseF,
    twoEventDiamond
  ] at htest

/-- Preservation of the algebraic symplectic form alone therefore does not
construct our compatible causal symplectic connection. -/
theorem form_preservation_does_not_imply_soldering :
    standardSymplecticField.PreservedByEquiv
        negDependentEquivConnection ∧
      ¬ standardSoldering.PreservedBy
        negDependentEquivConnection.toLinearConnection :=
  ⟨neg_preserves_standardSymplectic,
    neg_not_preserve_standardSoldering⟩

end CausalGeometry.Models
