import CausalGeometry.Calculus.CubicalLeibnizBlockIndices
import Mathlib.Tactic

namespace CausalGeometry

universe u v

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Deleting the newly inserted selected axis from the canonical (p+1,q)
shuffle recovers the canonical (p,q) shuffle of the face subset. -/
theorem faceResidual_insertedLeft_eq_faceSubsetPermutation
    {p q : ℕ}
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :

    let LA :=
      liftFaceSubset i A

    let hi :=
      removedAxis_not_mem_liftFaceSubset i A

    let B :=
      insertAxisSubset LA i hi

    let j :=
      insertedAxisPosition LA i hi

    let hdim :
        (p + 1) + q = p + q + 1 := by
          omega

    let sigma :=
      subsetPermutationOfEq hdim B

    let k :=
      leftBlockIndexOfEq hdim j

    faceResidualPermutation sigma k =
      subsetPermutation A := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let B :=
    insertAxisSubset LA i hi

  let j :=
    insertedAxisPosition LA i hi

  let hdim :
      (p + 1) + q = p + q + 1 := by
    omega

  let sigma :=
    subsetPermutationOfEq hdim B

  let k :=
    leftBlockIndexOfEq hdim j

  have hsigma_k :
      sigma k = i := by
    dsimp [sigma, k]
    rw [subsetPermutationOfEq_left]
    exact
      orderIso_insertedAxisPosition
        LA i hi

  have hcomp :
      complementAxisSubset hdim B =
        liftFaceSubset i
          (complementAxisSubset
            (rfl : p + q = p + q)
            A) := by
    simpa [LA, B, hdim, hi] using
      complement_insert_liftFaceSubset
        (h := (rfl : p + q = p + q))
        i A

  apply Equiv.ext

  intro t

  have hres :=
    faceResidual_succAbove
      sigma k t

  rw [hsigma_k] at hres

  have htarget :
      sigma (k.succAbove t) =
        i.succAbove
          (subsetPermutation A t) := by

    refine Fin.addCases ?_ ?_ t

    · intro a

      rw [
        succAbove_leftBlock_left
          (q := q) j a
      ]

      rw [
        subsetPermutationOfEq_left
          hdim B
          (j.succAbove a)
      ]

      rw [
        orderIso_insertAxis_succAbove
          LA i hi a
      ]

      rw [
        orderIso_liftFaceSubset
          i A a
      ]

      rw [
        subsetPermutation_left A a
      ]

    · intro b

      rw [
        succAbove_leftBlock_right
          (p := p) j b
      ]

      rw [
        subsetPermutationOfEq_right
          hdim B b
      ]

      rw [hcomp]

      rw [
        orderIso_liftFaceSubset
          i
          (complementAxisSubset
            (rfl : p + q = p + q)
            A)
          b
      ]

      rw [
        subsetPermutation_right A b
      ]

  apply i.succAbove_right_injective

  exact hres.symm.trans htarget

/-- Deleting an omitted axis from the complementary block of the canonical
(p,q+1) shuffle also recovers the canonical (p,q) face shuffle. -/
theorem faceResidual_complementRight_eq_faceSubsetPermutation
    {p q : ℕ}
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :

    let LA :=
      liftFaceSubset i A

    let hi :=
      removedAxis_not_mem_liftFaceSubset i A

    let hdim :
        p + (q + 1) = p + q + 1 := by
          omega

    let j :=
      complementAxisPosition
        hdim LA i hi

    let sigma :=
      subsetPermutationOfEq hdim LA

    let k :=
      rightBlockIndexOfEq hdim j

    faceResidualPermutation sigma k =
      subsetPermutation A := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let hdim :
      p + (q + 1) = p + q + 1 := by
    omega

  let j :=
    complementAxisPosition
      hdim LA i hi

  let sigma :=
    subsetPermutationOfEq hdim LA

  let k :=
    rightBlockIndexOfEq hdim j

  have hsigma_k :
      sigma k = i := by
    dsimp [sigma, k, j]
    rw [subsetPermutationOfEq_right]
    exact
      orderIso_complementAxisPosition
        hdim LA i hi

  apply Equiv.ext

  intro t

  have hres :=
    faceResidual_succAbove
      sigma k t

  rw [hsigma_k] at hres

  have htarget :
      sigma (k.succAbove t) =
        i.succAbove
          (subsetPermutation A t) := by

    refine Fin.addCases ?_ ?_ t

    · intro a

      rw [
        succAbove_rightBlock_left
          (q := q) j a
      ]

      rw [
        subsetPermutationOfEq_left
          hdim LA a
      ]

      rw [
        orderIso_liftFaceSubset
          i A a
      ]

      rw [
        subsetPermutation_left A a
      ]

    · intro b

      rw [
        succAbove_rightBlock_right
          (p := p) j b
      ]

      rw [
        subsetPermutationOfEq_right
          hdim LA
          (j.succAbove b)
      ]

      rw [
        orderIso_complement_lift_succAbove
          (h := (rfl : p + q = p + q))
          i A b
      ]

      rw [
        subsetPermutation_right A b
      ]

  apply i.succAbove_right_injective

  exact hres.symm.trans htarget

end CausalEventCube
end CausalGeometry
