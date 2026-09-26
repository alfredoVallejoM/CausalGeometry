import CausalGeometry.Calculus.CubicalLeibnizZeroLeft
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Full graded Leibniz theorem when the left factor has degree zero, with the
right factor in arbitrary degree. -/
theorem serreCup_leibniz_zero_left
    (q : ℕ)
    (alpha : CausalCubicalCochain S K 0)
    (beta : CausalCubicalCochain S K q) :
    differential (S := S) (K := K) q
        (serreCup 0 q alpha beta)
      =
    serreCup 1 q
        (differential (S := S) (K := K) 0 alpha)
        beta
      +
    serreCup 0 (q + 1)
        alpha
        (differential (S := S) (K := K) q beta) := by

  funext Q

  rw [differential_apply]

  simp_rw [faceContribution]

  simp_rw [serreCup_zero_left_apply]

  rw [serreCup_differential_zero_left_apply]

  rw [serreCup_zero_left_apply]

  rw [differential_apply]

  simp_rw [faceContribution]

  change
    (∑ i : Fin (q + 1),
      faceSign (K := K) i *
        (alpha
            (CausalEventCube.zeroCube
              (Q.upperFace i).base) *
            beta (Q.upperFace i)
          -
         alpha
            (CausalEventCube.zeroCube
              (Q.lowerFace i).base) *
            beta (Q.lowerFace i)))
      =
    (∑ i : Fin (1 + q),
      faceSign (K := K) i *
        (alpha
            (CausalEventCube.zeroCube
              (Q.upperFace i).base)
          -
         alpha
            (CausalEventCube.zeroCube Q.base))
        *
        beta (Q.upperFace i))
      +
    alpha (CausalEventCube.zeroCube Q.base) *
      (∑ i : Fin (q + 1),
        faceSign (K := K) i *
          (beta (Q.upperFace i) -
            beta (Q.lowerFace i)))

  have hdim : 1 + q = q + 1 := by omega

  subst hdim

  simp_rw [CausalEventCube.lowerFace_base]

  rw [Finset.mul_sum]

  rw [← Finset.sum_add_distrib]

  apply Fintype.sum_congr

  intro i

  ring

end CausalCubicalCochain
end CausalGeometry
