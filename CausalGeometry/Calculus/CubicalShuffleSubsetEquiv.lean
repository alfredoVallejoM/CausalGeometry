import CausalGeometry.Calculus.CubicalSubsetCup
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

/-- Increasing embedding of the first p shuffle coordinates into the ambient
p+q coordinate set. -/
def shuffleLeftOrderEmbedding
    {p q : ℕ}
    (sigma : CubicalShuffle p q) :
    Fin p ↪o Fin (p + q) :=
  OrderEmbedding.ofStrictMono
    (fun i =>
      sigma.1
        (CausalEventCube.leftBlockIndex p q i))
    sigma.2.1

/-- Increasing embedding of the final q shuffle coordinates. -/
def shuffleRightOrderEmbedding
    {p q : ℕ}
    (sigma : CubicalShuffle p q) :
    Fin q ↪o Fin (p + q) :=
  OrderEmbedding.ofStrictMono
    (fun j =>
      sigma.1
        (CausalEventCube.rightBlockIndex p q j))
    sigma.2.2

/-- The intrinsic p-axis subset carried by the first block of one shuffle. -/
def shuffleAxisSubset
    {p q : ℕ}
    (sigma : CubicalShuffle p q) :
    CausalEventCube.AxisSubset (p + q) p :=
  Set.powersetCard.ofFinEmbEquiv
    (shuffleLeftOrderEmbedding sigma)

@[simp] theorem shuffleAxisSubset_mem_iff
    {p q : ℕ}
    (sigma : CubicalShuffle p q)
    (k : Fin (p + q)) :
    k ∈ shuffleAxisSubset sigma ↔
      ∃ i : Fin p,
        sigma.1
            (CausalEventCube.leftBlockIndex p q i)
          =
        k := by
  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  rfl

/-- The subset extracted from the canonical shuffle of A is exactly A. -/
@[simp] theorem shuffleAxisSubset_subsetShuffle
    {p q : ℕ}
    (A : CausalEventCube.AxisSubset (p + q) p) :
    shuffleAxisSubset
        (CausalEventCube.subsetShuffle A)
      =
    A := by

  apply Set.powersetCard.ofFinEmbEquiv.injective

  change
    shuffleLeftOrderEmbedding
        (CausalEventCube.subsetShuffle A)
      =
    Set.powersetCard.ofFinEmbEquiv.symm A

  apply OrderEmbedding.ext
  intro i

  change
    CausalEventCube.subsetPermutation A
        (CausalEventCube.leftBlockIndex p q i)
      =
    _

  rw [CausalEventCube.subsetPermutation_left]

  rfl

/-- A right-block shuffle coordinate never lies in the extracted left-axis
subset. -/
theorem shuffleRight_not_mem_leftSubset
    {p q : ℕ}
    (sigma : CubicalShuffle p q)
    (j : Fin q) :
    sigma.1
        (CausalEventCube.rightBlockIndex p q j)
      ∉
    shuffleAxisSubset sigma := by

  intro hmem

  rw [shuffleAxisSubset_mem_iff] at hmem
  rcases hmem with ⟨i, hi⟩

  have hidx :
      CausalEventCube.rightBlockIndex p q j =
        CausalEventCube.leftBlockIndex p q i :=
    sigma.1.injective hi

  have hval := congrArg Fin.val hidx

  simp [
    CausalEventCube.rightBlockIndex,
    CausalEventCube.leftBlockIndex
  ] at hval

  omega

/-- The increasing enumeration of the complement of the left shuffle block is
exactly the original right shuffle block. -/
theorem shuffleRightOrderEmbedding_eq_complement
    {p q : ℕ}
    (sigma : CubicalShuffle p q) :
    shuffleRightOrderEmbedding sigma
      =
    Finset.orderEmbOfFin
      (CausalEventCube.complementAxes
        (shuffleAxisSubset sigma)).val
      (CausalEventCube.complementAxes
        (shuffleAxisSubset sigma)).prop := by

  apply Finset.orderEmbOfFin_unique'

  intro j

  have hnot :=
    shuffleRight_not_mem_leftSubset sigma j

  simpa [
    CausalEventCube.complementAxes
  ] using hnot

/-- Rebuilding the canonical shuffle from its first-block subset recovers the
original shuffle. -/
@[simp] theorem subsetShuffle_shuffleAxisSubset
    {p q : ℕ}
    (sigma : CubicalShuffle p q) :
    CausalEventCube.subsetShuffle
        (shuffleAxisSubset sigma)
      =
    sigma := by

  apply Subtype.ext
  apply Equiv.ext
  intro k

  refine Fin.addCases ?_ ?_ k

  · intro i

    change
      CausalEventCube.subsetPermutation
          (shuffleAxisSubset sigma)
          (CausalEventCube.leftBlockIndex p q i)
        =
      sigma.1
        (CausalEventCube.leftBlockIndex p q i)

    rw [CausalEventCube.subsetPermutation_left]

    have h :=
      congrArg
        (fun f : Fin p ↪o Fin (p + q) => f i)
        (Set.powersetCard.ofFinEmbEquiv.symm_apply_apply
          (shuffleLeftOrderEmbedding sigma))

    exact h

  · intro j

    change
      CausalEventCube.subsetPermutation
          (shuffleAxisSubset sigma)
          (CausalEventCube.rightBlockIndex p q j)
        =
      sigma.1
        (CausalEventCube.rightBlockIndex p q j)

    rw [CausalEventCube.subsetPermutation_right]

    have h :=
      congrArg
        (fun f : Fin q ↪o Fin (p + q) => f j)
        (shuffleRightOrderEmbedding_eq_complement sigma)

    exact h.symm

/-- Canonical equivalence between shuffle permutations and fixed-cardinality
axis subsets. -/
def shuffleSubsetEquiv
    (p q : ℕ) :
    CubicalShuffle p q ≃
      CausalEventCube.AxisSubset (p + q) p where

  toFun :=
    shuffleAxisSubset

  invFun :=
    CausalEventCube.subsetShuffle

  left_inv :=
    subsetShuffle_shuffleAxisSubset

  right_inv :=
    shuffleAxisSubset_subsetShuffle

end CausalCubicalCochain
end CausalGeometry
