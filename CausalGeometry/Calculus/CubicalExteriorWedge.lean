import CausalGeometry.Calculus.CubicalSerrePresentationEquality
import CausalGeometry.Calculus.CubicalExteriorDifferential
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- The orientation sign is invariant under inversion. -/
theorem permutationSign_inv
    {n : ℕ}
    (sigma : Equiv.Perm (Fin n)) :
    permutationSign (K := K) sigma⁻¹ =
      permutationSign (K := K) sigma := by
  simp [permutationSign,
    Equiv.Perm.sign_inv]

/-- Unnormalized alternating projection of a raw degree-n cubical cochain.

We deliberately do not divide by n!: the construction therefore makes sense
over every field, including positive characteristic. -/
noncomputable def alternatize
    (n : ℕ) :
    CausalCubicalCochain S K n →ₗ[K]
      CausalCubicalCochain S K n where

  toFun := fun omega Q =>
    ∑ sigma : Equiv.Perm (Fin n),
      permutationSign (K := K) sigma *
        omega (Q.permute sigma)

  map_add' := by
    intro omega eta
    funext Q
    simp [Finset.sum_add_distrib,
      mul_add]

  map_smul' := by
    intro a omega
    funext Q
    simp [Finset.mul_sum,
      mul_assoc, mul_comm,
      mul_left_comm]

@[simp] theorem alternatize_apply
    (n : ℕ)
    (omega : CausalCubicalCochain S K n)
    (Q : CausalEventCube S n) :
    alternatize (S := S) (K := K) n omega Q
      =
    ∑ sigma : Equiv.Perm (Fin n),
      permutationSign (K := K) sigma *
        omega (Q.permute sigma) :=
  rfl

/-- The alternating sum transforms with the sign representation under every
coordinate permutation. -/
theorem alternatize_permute
    {n : ℕ}
    (omega : CausalCubicalCochain S K n)
    (Q : CausalEventCube S n)
    (tau : Equiv.Perm (Fin n)) :
    alternatize (S := S) (K := K) n omega
        (Q.permute tau)
      =
    permutationSign (K := K) tau *
      alternatize (S := S) (K := K) n omega Q := by

  rw [alternatize_apply,
    alternatize_apply]

  simp_rw [CausalEventCube.permute_mul]

  let f :
      Equiv.Perm (Fin n) → K :=
    fun rho =>
      permutationSign (K := K)
          (tau⁻¹ * rho) *
        omega (Q.permute rho)

  have hreindex :=
    Equiv.sum_comp
      (Equiv.mulLeft tau)
      f

  have hsum :
      (∑ sigma : Equiv.Perm (Fin n),
          permutationSign (K := K) sigma *
            omega (Q.permute (tau * sigma)))
        =
      ∑ rho : Equiv.Perm (Fin n),
        permutationSign (K := K) tau *
          (permutationSign (K := K) rho *
            omega (Q.permute rho)) := by
    simpa [f,
      permutationSign_mul,
      permutationSign_inv,
      mul_assoc] using hreindex

  rw [hsum]
  rw [Finset.mul_sum]

/-- Alternatization really lands in the exterior subspace. -/
theorem alternatize_alternating
    {n : ℕ}
    (omega : CausalCubicalCochain S K n) :
    Alternating
      (alternatize (S := S) (K := K) n omega) := by
  apply alternating_of_permutation_law
  intro Q sigma
  exact
    alternatize_permute
      (S := S) (K := K)
      omega Q sigma

/-- Exterior alternatization as a linear map into the alternating submodule. -/
noncomputable def exteriorAlternatize
    (n : ℕ) :
    CausalCubicalCochain S K n →ₗ[K]
      CausalExteriorCochain
        (S := S) (K := K) n where

  toFun := fun omega =>
    ⟨alternatize
        (S := S) (K := K) n omega,
      alternatize_alternating omega⟩

  map_add' := by
    intro omega eta
    apply Subtype.ext
    exact map_add
      (alternatize
        (S := S) (K := K) n)
      omega eta

  map_smul' := by
    intro a omega
    apply Subtype.ext
    exact map_smul
      (alternatize
        (S := S) (K := K) n)
      a omega

/-- The genuine exterior wedge product is the oriented alternatization of the
Serre cup.

This is unnormalized, avoiding factorial denominators. -/
noncomputable def wedge
    (p q : ℕ) :
    CausalExteriorCochain
        (S := S) (K := K) p
      →ₗ[K]
    CausalExteriorCochain
        (S := S) (K := K) q
      →ₗ[K]
    CausalExteriorCochain
        (S := S) (K := K) (p + q) where

  toFun := fun alpha =>
    { toFun := fun beta =>
        exteriorAlternatize
          (S := S) (K := K) (p + q)
          (serreCup p q alpha.1 beta.1)

      map_add' := by
        intro beta gamma
        apply Subtype.ext
        rw [serreCup_add_right]
        exact map_add
          (alternatize
            (S := S) (K := K) (p + q))
          _ _

      map_smul' := by
        intro a beta
        apply Subtype.ext
        rw [serreCup_smul_right]
        exact map_smul
          (alternatize
            (S := S) (K := K) (p + q))
          a _ }

  map_add' := by
    intro alpha gamma
    apply LinearMap.ext
    intro beta
    apply Subtype.ext
    rw [serreCup_add_left]
    exact map_add
      (alternatize
        (S := S) (K := K) (p + q))
      _ _

  map_smul' := by
    intro a alpha
    apply LinearMap.ext
    intro beta
    apply Subtype.ext
    rw [serreCup_smul_left]
    exact map_smul
      (alternatize
        (S := S) (K := K) (p + q))
      a _

/-- Underlying raw cochain of the wedge. -/
@[simp] theorem wedge_val
    (p q : ℕ)
    (alpha :
      CausalExteriorCochain
        (S := S) (K := K) p)
    (beta :
      CausalExteriorCochain
        (S := S) (K := K) q) :
    ((wedge (S := S) (K := K)
        p q alpha beta :
      CausalExteriorCochain
        (S := S) (K := K) (p + q)) :
      CausalCubicalCochain S K (p + q))
      =
    alternatize
      (S := S) (K := K) (p + q)
      (serreCup p q alpha.1 beta.1) :=
  rfl

/-- In degree 0+0 there is only the identity permutation, so wedge agrees
with ordinary multiplication of configuration observables. -/
theorem wedge_zero_zero_configuration
    (F G : Configuration S → K) :
    (wedge (S := S) (K := K)
      0 0
      (toExteriorZero
        (ofConfigurationObservable F))
      (toExteriorZero
        (ofConfigurationObservable G))).1
      =
    ofConfigurationObservable
      (fun C => F C * G C) := by
  rw [wedge_val]
  rw [serreCup_configuration_observables]
  funext Q
  simp [alternatize]

end CausalCubicalCochain
end CausalGeometry
