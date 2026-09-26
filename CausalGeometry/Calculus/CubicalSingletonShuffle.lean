import CausalGeometry.Calculus.CubicalShuffleSubsetEquiv
import CausalGeometry.Calculus.CubicalFaceEquivariance
import Mathlib.Data.Set.PowersetCard
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

namespace CausalEventCube

/-- The canonical permutation of a singleton selected subset moves that axis
to the front and preserves the increasing order of the complement. -/
theorem subsetPermutation_singleton
    {q : ℕ}
    (i : Fin (1 + q)) :
    subsetPermutation
        (Set.powersetCard.ofSingleton i :
          AxisSubset (1 + q) 1)
      =
    i.cycleRange.symm := by

  let A : AxisSubset (1 + q) 1 :=
    Set.powersetCard.ofSingleton i

  have hleft :
      (Set.powersetCard.orderIsoOfFin A
        (0 : Fin 1)).1
        =
      i := by
    have hm :=
      (Set.powersetCard.orderIsoOfFin A
        (0 : Fin 1)).2
    change
      (Set.powersetCard.orderIsoOfFin A
        (0 : Fin 1)).1 ∈ ({i} : Finset (Fin (1 + q)))
        at hm
    simpa using hm

  have hrightEmb :
      Finset.orderEmbOfFin
          A.complementAxes.val
          A.complementAxes.prop
        =
      Fin.succAboveOrderEmb i := by

    symm

    apply Finset.orderEmbOfFin_unique'

    intro j

    change
      i.succAbove j ∈
        A.complementAxes.val

    simp [A, complementAxes,
      Fin.succAbove_ne]

  apply Equiv.ext
  intro k

  refine Fin.addCases ?_ ?_ k

  · intro j
    have hj : j = (0 : Fin 1) :=
      Subsingleton.elim _ _
    subst j

    rw [subsetPermutation_left]

    rw [hleft]

    have hzero :
        Fin.castAdd q (0 : Fin 1)
          =
        (0 : Fin (1 + q)) := by
      apply Fin.ext
      rfl

    rw [hzero]

    exact
      (Fin.cycleRange_symm_zero i).symm

  · intro j

    rw [subsetPermutation_right]

    have hj :
        (Set.powersetCard.orderIsoOfFin
          A.complementAxes j).1
          =
        i.succAbove j := by
      have h :=
        congrArg
          (fun f : Fin q ↪o Fin (1 + q) =>
            f j)
          hrightEmb
      exact h

    rw [hj]

    have hnat :
        Fin.natAdd 1 j =
          j.succ := by
      apply Fin.ext
      rfl

    rw [hnat]

    exact
      (Fin.cycleRange_symm_succ i j).symm

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Serre shuffle sign is the same canonical sign used by the orientation
layer. -/
theorem shuffleSign_eq_permutationSign
    {p q : ℕ}
    (sigma : CubicalShuffle p q) :
    shuffleSign (K := K) sigma =
      permutationSign (K := K) sigma.1 :=
  rfl

/-- A singleton selected axis has exactly the usual cubical face sign. -/
theorem subsetShuffleSign_singleton
    {q : ℕ}
    (i : Fin (1 + q)) :
    subsetShuffleSign
        (K := K)
        (Set.powersetCard.ofSingleton i :
          CausalEventCube.AxisSubset
            (1 + q) 1)
      =
    faceSign (K := K) i := by

  unfold subsetShuffleSign

  rw [shuffleSign_eq_permutationSign]

  change
    permutationSign (K := K)
      (CausalEventCube.subsetPermutation
        (Set.powersetCard.ofSingleton i :
          CausalEventCube.AxisSubset
            (1 + q) 1))
      =
    faceSign (K := K) i

  rw [CausalEventCube.subsetPermutation_singleton]

  rw [permutationSign_cycleRange_symm]

  rfl

end CausalCubicalCochain
end CausalGeometry
