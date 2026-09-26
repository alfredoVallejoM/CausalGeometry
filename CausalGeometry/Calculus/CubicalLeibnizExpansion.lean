import CausalGeometry.Calculus.CubicalLeibnizSums
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Subset Serre term with an arbitrary ambient dimension n equipped with a
proof p+q=n. -/
noncomputable def subsetCupTermOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S n)
    (A : CausalEventCube.AxisSubset n p) : K :=
  subsetShuffleSign
      (K := K)
      (CausalEventCube.specializeAxisSubset h A)
    *
  alpha (Q.selectedCube A)
    *
  beta
    (CausalEventCube.complementCubeOfEq
      h Q A)

/-- Dimension-stable intrinsic subset Serre product. -/
noncomputable def subsetSerreCupOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q) :
    CausalCubicalCochain S K n :=
  fun Q =>
    ∑ A : CausalEventCube.AxisSubset n p,
      subsetCupTermOfEq h alpha beta Q A

@[simp] theorem subsetSerreCupOfEq_apply
    {n p q : ℕ}
    (h : p + q = n)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S n) :
    subsetSerreCupOfEq h alpha beta Q
      =
    ∑ A : CausalEventCube.AxisSubset n p,
      subsetCupTermOfEq h alpha beta Q A :=
  rfl

/-- The generalized presentation reduces to the original subset presentation
when dimensions are definitionally aligned. -/
theorem subsetSerreCupOfEq_rfl
    (p q : ℕ)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q) :
    subsetSerreCupOfEq
        (rfl : p + q = p + q)
        alpha beta
      =
    subsetSerreCup p q alpha beta := by
  rfl

/-- General dimension transport formula. -/
theorem subsetSerreCupOfEq_cast
    {n p q : ℕ}
    (h : p + q = n)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S n) :
    subsetSerreCupOfEq h alpha beta Q
      =
    subsetSerreCup p q alpha beta
      (CausalEventCube.castDim h.symm Q) := by
  cases h
  rfl

/-- The differential of the base subset product is exactly the common
incidence sum. -/
theorem differential_subsetSerreCup_eq_incidenceSum
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :
    differential (S := S) (K := K) (p + q)
        (subsetSerreCup p q alpha beta) Q
      =
    leibnizIncidenceSum alpha beta Q := by

  rw [differential_apply]

  unfold leibnizIncidenceSum

  rw [Fintype.sum_sigma]

  apply Fintype.sum_congr

  intro i

  unfold faceContribution

  rw [
    subsetSerreCup_apply,
    subsetSerreCup_apply
  ]

  rw [← Finset.sum_sub_distrib]

  rw [Finset.mul_sum]

  apply Fintype.sum_congr

  intro A

  unfold leibnizIncidenceTerm
    subsetCupTerm

  ring

/-- Expansion of (d alpha) cup beta into its left parent-index sum. -/
theorem subsetSerreCupOfEq_differential_left_eq_parentSum
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :

    let hL :
        (p + 1) + q = p + q + 1 := by
          omega

    subsetSerreCupOfEq hL
        (differential (S := S) (K := K) p alpha)
        beta Q
      =
    ∑ x :
        CausalEventCube.LeftLeibnizParentIndex
          p q,
      leibnizLeftParentTerm
        alpha beta Q x := by

  dsimp only

  let hL :
      (p + 1) + q = p + q + 1 := by
    omega

  rw [subsetSerreCupOfEq_apply]

  rw [Fintype.sum_sigma]

  apply Fintype.sum_congr

  intro B

  rw [differential_apply]

  unfold subsetCupTermOfEq

  rw [Finset.sum_mul]

  apply Fintype.sum_congr

  intro j

  unfold faceContribution
    leibnizLeftParentTerm

  dsimp only

  ring

/-- Expansion of the graded right term
(-1)^p alpha cup d beta into its right parent-index sum. -/
theorem graded_subsetSerreCupOfEq_differential_right_eq_parentSum
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :

    let hR :
        p + (q + 1) = p + q + 1 := by
          omega

    gradedSign (K := K) p *
      subsetSerreCupOfEq hR
        alpha
        (differential (S := S) (K := K) q beta)
        Q
      =
    ∑ x :
        CausalEventCube.RightLeibnizParentIndex
          p q,
      leibnizRightParentTerm
        alpha beta Q x := by

  dsimp only

  let hR :
      p + (q + 1) = p + q + 1 := by
    omega

  rw [subsetSerreCupOfEq_apply]

  rw [Finset.mul_sum]

  rw [Fintype.sum_sigma]

  apply Fintype.sum_congr

  intro LA

  rw [differential_apply]

  unfold subsetCupTermOfEq

  rw [Finset.mul_sum]

  apply Fintype.sum_congr

  intro j

  unfold faceContribution
    leibnizRightParentTerm

  dsimp only

  ring

end CausalCubicalCochain
end CausalGeometry
