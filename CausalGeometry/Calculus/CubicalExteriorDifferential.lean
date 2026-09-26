import CausalGeometry.Calculus.CubicalFaceEquivariance
import CausalGeometry.Calculus.CubicalDifferentialSquared
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- One face contribution of an alternating cochain transforms by the global
orientation sign and the corresponding reindexed face. -/
theorem faceContribution_permute_of_alternating
    {n : ℕ}
    {omega : CausalCubicalCochain S K n}
    (homega : Alternating omega)
    (Q : CausalEventCube S (n + 1))
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    faceContribution omega (Q.permute sigma) i
      =
    permutationSign (K := K) sigma *
      faceContribution omega Q (sigma i) := by

  unfold faceContribution

  rw [
    CausalEventCube.permute_upperFace,
    CausalEventCube.permute_lowerFace
  ]

  rw [
    alternating_permute homega,
    alternating_permute homega
  ]

  rw [
    faceSign_mul_residualSign
      (K := K) sigma i
  ]

  ring

/-- The cubical differential obeys the full orientation law whenever the
input cochain is alternating. -/
theorem differential_permute_of_alternating
    {n : ℕ}
    {omega : CausalCubicalCochain S K n}
    (homega : Alternating omega)
    (Q : CausalEventCube S (n + 1))
    (sigma : Equiv.Perm (Fin (n + 1))) :
    differential (S := S) (K := K) n omega
        (Q.permute sigma)
      =
    permutationSign (K := K) sigma *
      differential (S := S) (K := K) n omega Q := by

  rw [differential_apply]
  rw [differential_apply]

  calc
    (∑ i : Fin (n + 1),
        faceContribution omega (Q.permute sigma) i)
        =
      ∑ i : Fin (n + 1),
        permutationSign (K := K) sigma *
          faceContribution omega Q (sigma i) := by
            apply Fintype.sum_congr
            intro i
            exact
              faceContribution_permute_of_alternating
                homega Q sigma i

    _ =
      permutationSign (K := K) sigma *
        ∑ i : Fin (n + 1),
          faceContribution omega Q (sigma i) := by
            rw [Finset.mul_sum]

    _ =
      permutationSign (K := K) sigma *
        ∑ i : Fin (n + 1),
          faceContribution omega Q i := by
            rw [Equiv.sum_comp sigma]

/-- The arbitrary-degree cubical differential preserves the alternating
exterior submodule. -/
theorem differential_alternating
    {n : ℕ}
    {omega : CausalCubicalCochain S K n}
    (homega : Alternating omega) :
    Alternating
      (differential (S := S) (K := K) n omega) := by

  apply alternating_of_permutation_law

  intro Q sigma

  exact
    differential_permute_of_alternating
      homega Q sigma

/-- Full arbitrary-degree exterior differential on causal cubical forms. -/
def exteriorDifferential
    (n : ℕ) :
    CausalExteriorCochain
        (S := S) (K := K) n
      →ₗ[K]
    CausalExteriorCochain
        (S := S) (K := K) (n + 1) where

  toFun := fun omega =>
    ⟨differential (S := S) (K := K) n omega.1,
      differential_alternating omega.2⟩

  map_add' := by
    intro omega eta
    apply Subtype.ext
    exact map_add
      (differential (S := S) (K := K) n)
      omega.1 eta.1

  map_smul' := by
    intro a omega
    apply Subtype.ext
    exact map_smul
      (differential (S := S) (K := K) n)
      a omega.1

@[simp] theorem exteriorDifferential_val
    (n : ℕ)
    (omega :
      CausalExteriorCochain
        (S := S) (K := K) n) :
    ((exteriorDifferential
        (S := S) (K := K) n omega :
      CausalExteriorCochain
        (S := S) (K := K) (n + 1)) :
      CausalCubicalCochain S K (n + 1))
      =
    differential (S := S) (K := K) n omega.1 :=
  rfl

/-- The arbitrary-degree exterior differential squares to zero. -/
theorem exteriorDifferential_squared
    (n : ℕ) :
    (exteriorDifferential
        (S := S) (K := K) (n + 1)).comp
      (exteriorDifferential
        (S := S) (K := K) n)
      =
    0 := by

  apply LinearMap.ext
  intro omega

  apply Subtype.ext

  change
    differential (S := S) (K := K) (n + 1)
        (differential (S := S) (K := K) n omega.1)
      =
    0

  exact
    differential_squared
      (S := S) (K := K) n

/-- The full exterior complex obtained by restricting the raw cubical complex
to alternating cochains. -/
def exteriorGradedComplex :
    GradedCausalCochainComplex
      K
      (fun n =>
        CausalExteriorCochain
          (S := S) (K := K) n) where

  d :=
    exteriorDifferential
      (S := S) (K := K)

  d_sq :=
    exteriorDifferential_squared
      (S := S) (K := K)

end CausalCubicalCochain
end CausalGeometry
