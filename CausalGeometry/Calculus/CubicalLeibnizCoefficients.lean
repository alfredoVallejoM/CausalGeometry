import CausalGeometry.Calculus.CubicalLeibnizResidualPermutation
import CausalGeometry.Calculus.CubicalLeibnizSigns
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Coefficient identity for the d alpha part of the graded Leibniz rule.

The ambient face sign times the face-shuffle sign equals the enlarged
(p+1,q)-shuffle sign times the local face sign inside the selected block. -/
theorem leibniz_left_coefficient
    {p q : ℕ}
    (i : Fin (p + q + 1))
    (A : CausalEventCube.AxisSubset (p + q) p) :

    let LA :=
      CausalEventCube.liftFaceSubset i A

    let hi :=
      CausalEventCube.removedAxis_not_mem_liftFaceSubset i A

    let B :=
      CausalEventCube.insertAxisSubset LA i hi

    let j :=
      CausalEventCube.insertedAxisPosition LA i hi

    let hdim :
        (p + 1) + q = p + q + 1 := by
          omega

    faceSign (K := K) i *
        subsetShuffleSign (K := K) A
      =
    subsetShuffleSign
        (K := K)
        (CausalEventCube.specializeAxisSubset
          hdim B)
      *
    faceSign (K := K) j := by

  dsimp only

  let LA :=
    CausalEventCube.liftFaceSubset i A

  let hi :
      i ∉ LA :=
    CausalEventCube.removedAxis_not_mem_liftFaceSubset
      i A

  let B :=
    CausalEventCube.insertAxisSubset LA i hi

  let j :=
    CausalEventCube.insertedAxisPosition LA i hi

  let hdim :
      (p + 1) + q = p + q + 1 := by
    omega

  let sigma :=
    CausalEventCube.subsetPermutationOfEq
      hdim B

  let k :=
    CausalEventCube.leftBlockIndexOfEq
      hdim j

  have hsigma_k :
      sigma k = i := by
    dsimp [sigma, k]
    rw [CausalEventCube.subsetPermutationOfEq_left]
    exact
      CausalEventCube.orderIso_insertedAxisPosition
        LA i hi

  have hres :
      CausalEventCube.faceResidualPermutation
          sigma k
        =
      CausalEventCube.subsetPermutation A := by
    simpa [LA, hi, B, j, hdim, sigma, k]
      using
        CausalEventCube
          .faceResidual_insertedLeft_eq_faceSubsetPermutation
            (p := p) (q := q) i A

  have hcoef :=
    faceSign_image_mul_residualSign
      (K := K) sigma k

  rw [hsigma_k, hres] at hcoef

  rw [
    faceSign_leftBlockIndexOfEq
      (K := K) hdim j
  ] at hcoef

  rw [
    subsetShuffleSign_eq_permutationSign
      (K := K) A
  ]

  rw [
    subsetShuffleSign_specialize
      (K := K) hdim B
  ]

  exact hcoef

/-- Coefficient identity for the d beta part.

The local right-block face sign contributes the Koszul factor (-1)^p. -/
theorem leibniz_right_coefficient
    {p q : ℕ}
    (i : Fin (p + q + 1))
    (A : CausalEventCube.AxisSubset (p + q) p) :

    let LA :=
      CausalEventCube.liftFaceSubset i A

    let hi :=
      CausalEventCube.removedAxis_not_mem_liftFaceSubset i A

    let hdim :
        p + (q + 1) = p + q + 1 := by
          omega

    let j :=
      CausalEventCube.complementAxisPosition
        hdim LA i hi

    faceSign (K := K) i *
        subsetShuffleSign (K := K) A
      =
    gradedSign (K := K) p *
      subsetShuffleSign
        (K := K)
        (CausalEventCube.specializeAxisSubset
          hdim LA)
      *
      faceSign (K := K) j := by

  dsimp only

  let LA :=
    CausalEventCube.liftFaceSubset i A

  let hi :
      i ∉ LA :=
    CausalEventCube.removedAxis_not_mem_liftFaceSubset
      i A

  let hdim :
      p + (q + 1) = p + q + 1 := by
    omega

  let j :=
    CausalEventCube.complementAxisPosition
      hdim LA i hi

  let sigma :=
    CausalEventCube.subsetPermutationOfEq
      hdim LA

  let k :=
    CausalEventCube.rightBlockIndexOfEq
      hdim j

  have hsigma_k :
      sigma k = i := by
    dsimp [sigma, k, j]
    rw [CausalEventCube.subsetPermutationOfEq_right]
    exact
      CausalEventCube.orderIso_complementAxisPosition
        hdim LA i hi

  have hres :
      CausalEventCube.faceResidualPermutation
          sigma k
        =
      CausalEventCube.subsetPermutation A := by
    simpa [LA, hi, hdim, j, sigma, k]
      using
        CausalEventCube
          .faceResidual_complementRight_eq_faceSubsetPermutation
            (p := p) (q := q) i A

  have hcoef :=
    faceSign_image_mul_residualSign
      (K := K) sigma k

  rw [hsigma_k, hres] at hcoef

  rw [
    faceSign_rightBlockIndexOfEq
      (K := K) hdim j
  ] at hcoef

  rw [
    subsetShuffleSign_eq_permutationSign
      (K := K) A
  ]

  rw [
    subsetShuffleSign_specialize
      (K := K) hdim LA
  ]

  calc
    faceSign (K := K) i *
        permutationSign (K := K)
          (CausalEventCube.subsetPermutation A)
        =
      permutationSign (K := K) sigma *
        (gradedSign (K := K) p *
          faceSign (K := K) j) := hcoef
    _ =
      gradedSign (K := K) p *
        permutationSign (K := K) sigma *
        faceSign (K := K) j := by
          ring

end CausalCubicalCochain
end CausalGeometry
