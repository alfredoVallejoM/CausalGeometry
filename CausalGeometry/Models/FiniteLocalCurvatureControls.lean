import CausalGeometry.Calculus.FiniteLocalCurvature
import CausalGeometry.Models.CalculusControls
import Mathlib.Tactic

namespace CausalGeometry.Models

open EventSystem

/-- Constant local operator field using the same noncommuting generators as the
existing curvature mutation controls. -/
def noncommutingGaugePotential
    (C : Configuration twoEventSystem) :
    CausalGaugePotential
      ℤ twoEventSystem (ℤ × ℤ) C where
  operator := fun d =>
    match d.event with
    | false => transportA
    | true => transportB

/-- Finite transport obtained by the exact affine rule T_e=I+A_e. -/
def affineNoncommutingConnection :
    LinearCausalConnection
      ℤ twoEventSystem (ℤ × ℤ) where
  transport := fun _ e _ =>
    LinearMap.id +
      match e with
      | false => transportA
      | true => transportB

/-- Certified exact finite/local comparison for the affine model. -/
def affineNoncommutingComparison :
    FiniteLocalCurvatureComparison
      ℤ twoEventSystem (ℤ × ℤ) where
  finite :=
    affineNoncommutingConnection
  local :=
    noncommutingGaugePotential
  transport_eq_id_add := by
    intro C e h
    cases e <;> rfl
  local_parallel := by
    intro C e f d
    cases f <;> rfl

/-- The local reverse commutator on the basic false/true square is nonzero. -/
theorem local_reverse_curvature_test :
    (noncommutingGaugePotential
      twoEventSystem.empty).curvature
        (CausalOneForm.baseF twoEventDiamond)
        (CausalOneForm.baseE twoEventDiamond)
        (1, 0) =
      (-1, 0) := by
  norm_num [
    noncommutingGaugePotential,
    CausalGaugePotential.curvature,
    linearCommutator,
    CausalOneForm.baseE,
    CausalOneForm.baseF,
    transportA,
    transportB,
    twoEventDiamond
  ]

/-- The finite transport curvature has the same nonzero value. -/
theorem affine_finite_curvature_test :
    affineNoncommutingConnection.curvature
        twoEventDiamond (1, 0) =
      (-1, 0) := by
  rw [
    affineNoncommutingComparison.finite_curvature_eq_local_reverse
      twoEventDiamond
  ]
  exact local_reverse_curvature_test

/-- Concrete same-value comparison, not only equality of endomorphisms. -/
theorem affine_finite_local_curvature_agree :
    affineNoncommutingConnection.curvature
        twoEventDiamond =
      (noncommutingGaugePotential
        twoEventSystem.empty).curvature
          (CausalOneForm.baseF twoEventDiamond)
          (CausalOneForm.baseE twoEventDiamond) :=
  affineNoncommutingComparison.finite_curvature_eq_local_reverse
    twoEventDiamond

/-- Zero local potential with exactly the same type surface. -/
def zeroGaugePotential
    (C : Configuration twoEventSystem) :
    CausalGaugePotential
      ℤ twoEventSystem (ℤ × ℤ) C where
  operator := fun _ => 0

/-- The affine noncommuting finite connection cannot be reconstructed from the
mutated zero local potential. -/
theorem affine_not_reconstructed_by_zeroPotential :
    ¬ ∀ (C : Configuration twoEventSystem)
        (e : Bool)
        (h : twoEventSystem.Enabled C e),
      affineNoncommutingConnection.transport C e h =
        LinearMap.id +
          (zeroGaugePotential C).operator
            ⟨e, h⟩ := by
  intro h
  have hf :=
    h twoEventSystem.empty false
      (twoEvent_enabled_empty false)
  have hv :=
    LinearMap.congr_fun hf (0, 1)
  norm_num [
    affineNoncommutingConnection,
    zeroGaugePotential,
    transportA
  ] at hv

/-- The finite/local comparison theorem is genuinely discriminating: the
positive local potential reconstructs the finite transport while the
same-typed zero mutation does not. -/
theorem finiteLocal_comparison_discriminates :
    (∀ (C : Configuration twoEventSystem)
        (e : Bool)
        (h : twoEventSystem.Enabled C e),
      affineNoncommutingConnection.transport C e h =
        LinearMap.id +
          (noncommutingGaugePotential C).operator
            ⟨e, h⟩) ∧
      ¬ ∀ (C : Configuration twoEventSystem)
        (e : Bool)
        (h : twoEventSystem.Enabled C e),
      affineNoncommutingConnection.transport C e h =
        LinearMap.id +
          (zeroGaugePotential C).operator
            ⟨e, h⟩ := by
  constructor
  · intro C e h
    cases e <;> rfl
  · exact affine_not_reconstructed_by_zeroPotential

end CausalGeometry.Models
