import CausalGeometry.Calculus.CubicalLeibnizParentSubsets
import CausalGeometry.Calculus.CubicalFaceEquivariance
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Canonical subset permutation when the ambient cardinality is only
propositionally, rather than definitionally, p+q. -/
def subsetPermutationOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p) :
    Equiv.Perm (Fin n) := by
  subst n
  exact subsetPermutation A

/-- Left block index transported to an ambient Fin n. -/
def leftBlockIndexOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (i : Fin p) :
    Fin n :=
  Fin.cast h
    (leftBlockIndex p q i)

/-- Right block index transported to an ambient Fin n. -/
def rightBlockIndexOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (j : Fin q) :
    Fin n :=
  Fin.cast h
    (rightBlockIndex p q j)

theorem subsetPermutationOfEq_left
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p)
    (i : Fin p) :
    subsetPermutationOfEq h A
        (leftBlockIndexOfEq h i)
      =
    (Set.powersetCard.orderIsoOfFin A i).1 := by
  subst n
  exact subsetPermutation_left A i

theorem subsetPermutationOfEq_right
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p)
    (j : Fin q) :
    subsetPermutationOfEq h A
        (rightBlockIndexOfEq h j)
      =
    (Set.powersetCard.orderIsoOfFin
      (complementAxisSubset h A) j).1 := by
  subst n
  exact subsetPermutation_right A j

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- The cofactor identity in the form used by the Leibniz proof:
the face sign of the image axis multiplies the residual sign. -/
theorem faceSign_image_mul_residualSign
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    faceSign (K := K) (sigma i) *
        permutationSign (K := K)
          (CausalEventCube.faceResidualPermutation
            sigma i)
      =
    permutationSign (K := K) sigma *
      faceSign (K := K) i := by

  have h :=
    faceSign_mul_residualSign
      (K := K) sigma i

  have hi :=
    faceSign_square
      (K := K) i

  have hsi :=
    faceSign_square
      (K := K) (sigma i)

  calc
    faceSign (K := K) (sigma i) *
        permutationSign (K := K)
          (CausalEventCube.faceResidualPermutation
            sigma i)
        =
      (faceSign (K := K) i *
          faceSign (K := K) i) *
        (faceSign (K := K) (sigma i) *
          permutationSign (K := K)
            (CausalEventCube.faceResidualPermutation
              sigma i)) := by
            rw [hi]
            ring
    _ =
      (faceSign (K := K) i *
          faceSign (K := K) (sigma i)) *
        (faceSign (K := K) i *
          permutationSign (K := K)
            (CausalEventCube.faceResidualPermutation
              sigma i)) := by
            ring
    _ =
      (faceSign (K := K) i *
          faceSign (K := K) (sigma i)) *
        (permutationSign (K := K) sigma *
          faceSign (K := K) (sigma i)) := by
            rw [h]
    _ =
      permutationSign (K := K) sigma *
        faceSign (K := K) i *
        (faceSign (K := K) (sigma i) *
          faceSign (K := K) (sigma i)) := by
            ring
    _ =
      permutationSign (K := K) sigma *
        faceSign (K := K) i := by
          rw [hsi]
          ring

/-- Face sign of a left-block coordinate is its local face sign. -/
theorem faceSign_leftBlockIndexOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (i : Fin p) :
    faceSign (K := K)
        (CausalEventCube.leftBlockIndexOfEq
          h i)
      =
    faceSign (K := K) i := by
  subst n
  rfl

/-- A right-block coordinate contributes the Koszul factor (-1)^p in addition
to its local face sign. -/
theorem faceSign_rightBlockIndexOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (j : Fin q) :
    faceSign (K := K)
        (CausalEventCube.rightBlockIndexOfEq
          h j)
      =
    gradedSign (K := K) p *
      faceSign (K := K) j := by
  subst n
  unfold faceSign gradedSign
  rw [pow_add]
  rfl

end CausalCubicalCochain
end CausalGeometry
