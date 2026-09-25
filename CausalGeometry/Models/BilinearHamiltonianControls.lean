import CausalGeometry.Calculus.BilinearTransport
import CausalGeometry.Calculus.HamiltonianTransport
import CausalGeometry.Models.CalculusControls
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

namespace CausalGeometry.Models

open EventSystem

/-- Standard alternating form on Z^2. -/
def standardSymplecticForm :
    (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ
    (fun x y => x.1 * y.2 - x.2 * y.1)
    (by
      intro x y z
      simp
      ring)
    (by
      intro a x y
      simp
      ring)
    (by
      intro x y z
      simp
      ring)
    (by
      intro a x y
      simp
      ring)

/-- Constant causal bilinear field carrying the standard symplectic form. -/
def standardSymplecticField :
    CausalBilinear.Field
      (K := ℤ)
      (S := twoEventSystem)
      (Fiber := fun _ => ℤ × ℤ) where
  form := fun _ => standardSymplecticForm

theorem standardSymplecticField_alternating :
    standardSymplecticField.Alternating := by
  intro C x
  rcases x with ⟨a, b⟩
  simp [CausalBilinear.Field.Alternating,
    standardSymplecticField,
    standardSymplecticForm]

theorem standardSymplecticField_nondegenerate :
    standardSymplecticField.LeftNondegenerate := by
  intro C x h
  rcases x with ⟨a, b⟩
  have h10 := h (1, 0)
  have h01 := h (0, 1)
  norm_num [standardSymplecticField,
    standardSymplecticForm] at h10 h01
  ext <;> assumption

/-- Positive control: identity transport preserves the symplectic field. -/
def identityDependentEquivConnection :
    DependentLinearEquivConnection
      ℤ twoEventSystem
      (fun _ => ℤ × ℤ) where
  transport := fun _ _ _ =>
    LinearEquiv.refl ℤ (ℤ × ℤ)

theorem identity_preserves_standardSymplectic :
    standardSymplecticField.PreservedByEquiv
      identityDependentEquivConnection := by
  intro C e h x y
  rfl

/-- Same-type adversarial mutation: every event swaps the two coordinates. -/
def swapDependentEquivConnection :
    DependentLinearEquivConnection
      ℤ twoEventSystem
      (fun _ => ℤ × ℤ) where
  transport := fun _ _ _ =>
    LinearEquiv.prodComm ℤ ℤ ℤ

/-- Swapping both arguments reverses the sign of the standard symplectic
form, so this linear-equivalence connection is not symplectic. -/
theorem swap_not_preserve_standardSymplectic :
    ¬ standardSymplecticField.PreservedByEquiv
        swapDependentEquivConnection := by
  intro hpres
  have h :=
    hpres
      twoEventSystem.empty false
      (twoEvent_enabled_empty false)
      (1, 0) (0, 1)
  norm_num [standardSymplecticField,
    standardSymplecticForm,
    swapDependentEquivConnection] at h

/-- Explicit sharp map for the standard symplectic form:
omega(x,-)=alpha has solution x=(alpha(e2),-alpha(e1)). -/
def standardSymplecticSharp :
    Module.Dual ℤ (ℤ × ℤ) →ₗ[ℤ]
      (ℤ × ℤ) where
  toFun := fun ω =>
    (ω (0, 1), - ω (1, 0))
  map_add' := by
    intro ω η
    ext <;> simp
  map_smul' := by
    intro a ω
    ext <;> simp

/-- Concrete musical bridge: in this model flat and sharp really are inverse. -/
def standardSymplecticMusicalBridge :
    CausalBilinear.MusicalBridge
      standardSymplecticField where
  sharp := fun _ => standardSymplecticSharp
  sharp_flat := by
    intro C x
    rcases x with ⟨a, b⟩
    ext <;>
      simp [standardSymplecticSharp,
        CausalBilinear.Field.flat,
        standardSymplecticField,
        standardSymplecticForm]
  flat_sharp := by
    intro C ω
    ext x
    rcases x with ⟨a, b⟩
    have hx :
        (a, b) =
          a • (1, 0) + b • (0, 1) := by
      ext <;> simp
    rw [hx, map_add, map_zsmul, map_zsmul]
    simp [standardSymplecticSharp,
      CausalBilinear.Field.flat,
      standardSymplecticField,
      standardSymplecticForm]
    ring

/-- A simple constant Hamiltonian covector section. -/
def coordinateCovector :
    CausalHamiltonian.CovectorSection
      (K := ℤ)
      (S := twoEventSystem)
      (Fiber := fun _ => ℤ × ℤ) :=
  fun _ =>
    { toFun := fun x => x.1
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simp }

/-- The musical bridge produces a genuine Hamiltonian pair. -/
def coordinateHamiltonianPair :
    CausalHamiltonian.Pair
      standardSymplecticField :=
  CausalHamiltonian.Pair.ofMusical
    standardSymplecticMusicalBridge
    coordinateCovector

theorem coordinateHamiltonian_vector :
    coordinateHamiltonianPair.vector
        twoEventSystem.empty =
      (0, -1) := by
  rfl

/-- Identity causal transport preserves both sides of this Hamiltonian pair. -/
theorem coordinateHamiltonian_parallel :
    coordinateHamiltonianPair.VectorParallelAt
      identityDependentEquivConnection
      twoEventSystem.empty false
      (twoEvent_enabled_empty false) := by
  rfl

end CausalGeometry.Models
