import CausalGeometry.Calculus.CubicalSingletonShuffle
import CausalGeometry.Calculus.CubicalSerrePresentationEquality
import CausalGeometry.Calculus.CubicalBackFaceStructure
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- The zero-dimensional front factor is the zero-cube at the original base. -/
theorem frontFace_zero
    (q : ℕ)
    (Q : CausalEventCube S q) :
    Q.frontFace 0 q =
      zeroCube Q.base := by
  apply CausalEventCube.ext
  · rw [frontFace_base]
  · funext i
    exact Fin.elim0 i

/-- Taking zero leading directions in the back factor changes nothing. -/
@[simp] theorem backFace_zero
    (q : ℕ)
    (Q : CausalEventCube S q) :
    Q.backFace 0 q = Q := by
  simpa [backFace, castDim]

/-- The selected cube of a singleton axis is the canonical one-cube for that
event over the original base. -/
theorem selectedCube_singleton
    {q : ℕ}
    (Q : CausalEventCube S (1 + q))
    (i : Fin (1 + q)) :
    Q.selectedCube
        (Set.powersetCard.ofSingleton i :
          AxisSubset (1 + q) 1)
      =
    oneCube Q.base
      (Q.frame.event i)
      (Q.frame.enabled i) := by

  apply CausalEventCube.ext
  · rfl
  · funext j
    have hj : j = (0 : Fin 1) :=
      Subsingleton.elim _ _
    subst j
    change
      Q.frame.event
          (Set.powersetCard.orderIsoOfFin
            (Set.powersetCard.ofSingleton i :
              AxisSubset (1 + q) 1)
            0).1
        =
      Q.frame.event i

    congr 1

    have hm :=
      (Set.powersetCard.orderIsoOfFin
        (Set.powersetCard.ofSingleton i :
          AxisSubset (1 + q) 1)
        0).2

    change
      (Set.powersetCard.orderIsoOfFin
        (Set.powersetCard.ofSingleton i :
          AxisSubset (1 + q) 1)
        0).1
        ∈
      ({i} : Finset (Fin (1 + q)))
      at hm

    simpa using hm

/-- One leading direction in backFace is just the upper zero-face. -/
theorem backFace_one
    (q : ℕ)
    (Q : CausalEventCube S (1 + q)) :
    Q.backFace 1 q =
      Q.upperFace (0 : Fin (1 + q)) := by
  unfold backFace
  simpa [castDim]

/-- The complementary cube of a singleton selected axis is exactly the upper
face obtained by executing that axis. -/
theorem complementCube_singleton
    {q : ℕ}
    (Q : CausalEventCube S (1 + q))
    (i : Fin (1 + q)) :
    Q.complementCube
        (Set.powersetCard.ofSingleton i :
          AxisSubset (1 + q) 1)
      =
    Q.upperFace i := by

  let A : AxisSubset (1 + q) 1 :=
    Set.powersetCard.ofSingleton i

  calc
    Q.complementCube A
        =
      (Q.permute (subsetPermutation A))
        .backFace 1 q :=
      complementCube_eq_backFace Q A

    _ =
      (Q.permute (subsetPermutation A))
        .upperFace (0 : Fin (1 + q)) := by
          rw [backFace_one]

    _ =
      Q.upperFace i := by
          rw [subsetPermutation_singleton i]
          rw [permute_upperFace]

          have hres :
              faceResidualPermutation
                  (i.cycleRange.symm)
                  (0 : Fin (1 + q))
                =
              1 := by
            apply Equiv.ext
            intro j
            rw [faceResidual_succAbove]
            simp

          rw [hres]
          simp

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Zero-cardinality axis subsets are unique. -/
instance axisSubsetZeroUnique
    (n : ℕ) :
    Unique (CausalEventCube.AxisSubset n 0) where
  default :=
    ⟨∅, by simp⟩
  uniq A := by
    apply Subtype.ext
    exact Finset.card_eq_zero.mp A.prop

/-- A (0,q)-shuffle is unique and is the identity shuffle. -/
instance cubicalShuffleZeroLeftUnique
    (q : ℕ) :
    Unique (CubicalShuffle 0 q) where

  default :=
    identityShuffle 0 q

  uniq sigma := by
    apply (shuffleSubsetEquiv 0 q).injective
    exact Subsingleton.elim _ _

/-- Serre cup with a degree-zero left factor has the expected direct formula. -/
theorem serreCup_zero_left_apply
    (q : ℕ)
    (alpha : CausalCubicalCochain S K 0)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S q) :
    serreCup 0 q alpha beta Q =
      alpha (CausalEventCube.zeroCube Q.base) *
        beta Q := by

  rw [serreCup_apply]

  simp [shuffleCupTerm,
    orderedCup_apply,
    shuffleSign,
    CausalEventCube.frontFace_zero,
    CausalEventCube.backFace_zero,
    identityShuffle]

/-- The subset term for a singleton selected axis is precisely the signed
degree-one differential value times beta on the corresponding upper face. -/
theorem singleton_subsetCupTerm_differential_zero
    {q : ℕ}
    (alpha : CausalCubicalCochain S K 0)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (1 + q))
    (i : Fin (1 + q)) :
    subsetCupTerm 1 q
        (differential (S := S) (K := K) 0 alpha)
        beta Q
        (Set.powersetCard.ofSingleton i :
          CausalEventCube.AxisSubset (1 + q) 1)
      =
    faceSign (K := K) i *
      (alpha
          (CausalEventCube.zeroCube
            (Q.upperFace i).base)
        -
       alpha
          (CausalEventCube.zeroCube Q.base))
      *
      beta (Q.upperFace i) := by

  unfold subsetCupTerm

  rw [subsetShuffleSign_singleton]

  rw [
    CausalEventCube.selectedCube_singleton,
    CausalEventCube.complementCube_singleton
  ]

  rw [
    differential_zero_recovers_causalDifference
  ]

  rfl

/-- The complete (1,q)-Serre term d alpha cup beta is the expected sum over
ambient causal axes. -/
theorem serreCup_differential_zero_left_apply
    {q : ℕ}
    (alpha : CausalCubicalCochain S K 0)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (1 + q)) :
    serreCup 1 q
        (differential (S := S) (K := K) 0 alpha)
        beta Q
      =
    ∑ i : Fin (1 + q),
      faceSign (K := K) i *
        (alpha
            (CausalEventCube.zeroCube
              (Q.upperFace i).base)
          -
         alpha
            (CausalEventCube.zeroCube Q.base))
        *
        beta (Q.upperFace i) := by

  rw [← subsetSerreCup_eq_serreCup]

  rw [subsetSerreCup_apply]

  have hreindex :=
    Equiv.sum_comp
      (Set.powersetCard.ofSingleton :
        Fin (1 + q) ≃
          CausalEventCube.AxisSubset
            (1 + q) 1)
      (fun A =>
        subsetCupTerm 1 q
          (differential
            (S := S) (K := K) 0 alpha)
          beta Q A)

  rw [← hreindex]

  apply Fintype.sum_congr
  intro i

  exact
    singleton_subsetCupTerm_differential_zero
      alpha beta Q i

end CausalCubicalCochain
end CausalGeometry
