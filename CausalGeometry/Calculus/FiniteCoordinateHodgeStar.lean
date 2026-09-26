import Mathlib.Order.Hom.PowersetCard
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic

namespace CausalGeometry

noncomputable section

universe u

open Set

/-- Coefficients of a finite exterior p-form in the canonical ordered wedge
basis of an oriented orthonormal n-frame. -/
abbrev FiniteExteriorForm
    (K : Type u)
    (n p : ℕ) :=
  Set.powersetCard (Fin n) p → K

namespace FiniteExteriorForm

variable {K : Type u} [Field K]

/-- Complement equivalence between p-subsets and q-subsets when p+q=n. -/
noncomputable def complementEquiv
    {n p q : ℕ}
    (h : p + q = n) :
    Set.powersetCard (Fin n) p ≃
      Set.powersetCard (Fin n) q :=
  Set.powersetCard.compl
    (by
      simpa [Fintype.card_fin, Nat.add_comm]
        using h)

/-- Canonical orientation permutation attached to a p-subset: list its
elements increasingly first, then list its complement increasingly. -/
noncomputable def orientationPermutation
    {n p q : ℕ}
    (h : p + q = n)
    (A : Set.powersetCard (Fin n) p) :
    Equiv.Perm (Fin (p + q)) :=
  let B := complementEquiv h A
  Set.powersetCard.permOfDisjoint
    (s := A)
    (t := B)
    (by
      change Disjoint A.val A.valᶜ
      exact disjoint_compl_right)

/-- Orientation sign of one exterior basis element in the coefficient field. -/
noncomputable def orientationSign
    {n p q : ℕ}
    (h : p + q = n)
    (A : Set.powersetCard (Fin n) p) : K :=
  ((((Equiv.Perm.sign
      (orientationPermutation h A)) : ℤˣ) : ℤ) : K)

/-- Every orientation sign squares to one. -/
theorem orientationSign_sq
    {n p q : ℕ}
    (h : p + q = n)
    (A : Set.powersetCard (Fin n) p) :
    orientationSign (K := K) h A *
        orientationSign (K := K) h A
      =
    1 := by
  unfold orientationSign
  rcases
      Int.units_eq_one_or
        (Equiv.Perm.sign
          (orientationPermutation h A)) with
    hs | hs
  · rw [hs]
    simp
  · rw [hs]
    simp

/-- Hodge star in one oriented orthonormal finite frame.

The metric hypothesis is encoded by working in an orthonormal coordinate
frame; orientation is the canonical order of Fin n. -/
noncomputable def hodgeStar
    {n p q : ℕ}
    (h : p + q = n) :
    FiniteExteriorForm K n p →ₗ[K]
      FiniteExteriorForm K n q where

  toFun := fun omega B =>
    let A :=
      (complementEquiv h).symm B
    orientationSign (K := K) h A *
      omega A

  map_add' := by
    intro omega eta
    funext B
    simp [mul_add]

  map_smul' := by
    intro a omega
    funext B
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- Explicit inverse Hodge star using the same p-before-q orientation sign. -/
noncomputable def hodgeStarInv
    {n p q : ℕ}
    (h : p + q = n) :
    FiniteExteriorForm K n q →ₗ[K]
      FiniteExteriorForm K n p where

  toFun := fun eta A =>
    orientationSign (K := K) h A *
      eta (complementEquiv h A)

  map_add' := by
    intro eta theta
    funext A
    simp [mul_add]

  map_smul' := by
    intro a eta
    funext A
    simp [mul_assoc, mul_comm, mul_left_comm]

theorem hodgeStarInv_hodgeStar
    {n p q : ℕ}
    (h : p + q = n)
    (omega : FiniteExteriorForm K n p) :
    hodgeStarInv (K := K) h
        (hodgeStar (K := K) h omega)
      =
    omega := by
  funext A
  simp [hodgeStarInv, hodgeStar,
    orientationSign_sq (K := K) h A]

theorem hodgeStar_hodgeStarInv
    {n p q : ℕ}
    (h : p + q = n)
    (eta : FiniteExteriorForm K n q) :
    hodgeStar (K := K) h
        (hodgeStarInv (K := K) h eta)
      =
    eta := by
  funext B
  let A :=
    (complementEquiv h).symm B
  have hA :
      complementEquiv h A = B := by
    exact (complementEquiv h).apply_symm_apply B
  change
    orientationSign (K := K) h A *
        (orientationSign (K := K) h A *
          eta (complementEquiv h A))
      =
    eta B
  rw [← mul_assoc, orientationSign_sq]
  rw [one_mul, hA]

/-- The finite oriented orthonormal Hodge star is a linear equivalence between
complementary exterior degrees. -/
noncomputable def hodgeStarEquiv
    {n p q : ℕ}
    (h : p + q = n) :
    FiniteExteriorForm K n p ≃ₗ[K]
      FiniteExteriorForm K n q where

  toFun :=
    hodgeStar (K := K) h

  invFun :=
    hodgeStarInv (K := K) h

  left_inv :=
    hodgeStarInv_hodgeStar
      (K := K) h

  right_inv :=
    hodgeStar_hodgeStarInv
      (K := K) h

  map_add' := by
    intro x y
    exact map_add
      (hodgeStar (K := K) h) x y

  map_smul' := by
    intro a x
    exact map_smul
      (hodgeStar (K := K) h) a x

end FiniteExteriorForm
end

end CausalGeometry
