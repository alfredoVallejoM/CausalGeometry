import CausalGeometry.Calculus.CubicalExterior
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Reindexing by the identity permutation does not change a cube. -/
@[simp] theorem permute_one
    {n : ℕ}
    (Q : CausalEventCube S n) :
    Q.permute (1 : Equiv.Perm (Fin n)) = Q := by
  apply CausalEventCube.ext
  · rfl
  · funext i
    rfl

/-- Successive coordinate reindexings compose according to permutation
multiplication. -/
theorem permute_mul
    {n : ℕ}
    (Q : CausalEventCube S n)
    (σ τ : Equiv.Perm (Fin n)) :
    (Q.permute σ).permute τ =
      Q.permute (σ * τ) := by
  apply CausalEventCube.ext
  · rfl
  · funext i
    rfl

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Sign of a finite coordinate permutation in the coefficient field. -/
def permutationSign
    {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : K :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)

@[simp] theorem permutationSign_one
    {n : ℕ} :
    permutationSign (K := K)
      (1 : Equiv.Perm (Fin n)) = 1 := by
  simp [permutationSign]

theorem permutationSign_mul
    {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    permutationSign (K := K) (σ * τ) =
      permutationSign (K := K) σ *
        permutationSign (K := K) τ := by
  simp [permutationSign,
    Equiv.Perm.sign_mul]

theorem permutationSign_swap
    {n : ℕ}
    {i j : Fin n}
    (hij : i ≠ j) :
    permutationSign (K := K)
        (Equiv.swap i j)
      =
    -1 := by
  simp [permutationSign,
    Equiv.Perm.sign_swap hij]

/-- The transposition definition of alternation implies the standard
orientation law for every coordinate permutation. -/
theorem alternating_permute
    {n : ℕ}
    {ω : CausalCubicalCochain S K n}
    (hω : Alternating ω)
    (Q : CausalEventCube S n)
    (σ : Equiv.Perm (Fin n)) :
    ω (Q.permute σ) =
      permutationSign (K := K) σ *
        ω Q := by

  induction σ using Equiv.Perm.swap_induction_on' with

  | one =>
      simp [permutationSign]

  | mul_swap σ i j hij ih =>
      rw [← CausalEventCube.permute_mul]
      rw [hω (Q.permute σ) i j hij]
      rw [ih]
      rw [permutationSign_mul]
      rw [permutationSign_swap hij]
      ring

/-- Conversely, the full permutation orientation law implies the original
transposition alternation predicate. -/
theorem alternating_of_permutation_law
    {n : ℕ}
    (ω : CausalCubicalCochain S K n)
    (h :
      ∀ (Q : CausalEventCube S n)
        (σ : Equiv.Perm (Fin n)),
        ω (Q.permute σ) =
          permutationSign (K := K) σ *
            ω Q) :
    Alternating ω := by
  intro Q i j hij
  rw [h Q (Equiv.swap i j)]
  rw [permutationSign_swap hij]
  ring

/-- Equivalent global characterization of exterior cubical cochains. -/
theorem alternating_iff_permutation_law
    {n : ℕ}
    (ω : CausalCubicalCochain S K n) :
    Alternating ω ↔
      ∀ (Q : CausalEventCube S n)
        (σ : Equiv.Perm (Fin n)),
        ω (Q.permute σ) =
          permutationSign (K := K) σ *
            ω Q := by
  constructor
  · exact fun h =>
      alternating_permute h
  · exact
      alternating_of_permutation_law ω

end CausalCubicalCochain
end CausalGeometry
