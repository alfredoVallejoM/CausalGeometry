import CausalGeometry.Calculus.CubicalCochain
import CausalGeometry.Calculus.EventCubeFaceLaws
import Mathlib.Data.Fin.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Reverse the order in which two different cubical coordinates are removed.

The first coordinate is an axis of the original (n+2)-cube; the second is an
axis of the first face. -/
def swapDeletionPair
    {n : ℕ}
    (ij : Fin (n + 2) × Fin (n + 1)) :
    Fin (n + 2) × Fin (n + 1) :=
  (ij.1.succAbove ij.2,
    ij.2.predAbove ij.1)

/-- Swapping the deletion order twice returns the original ordered pair. -/
theorem swapDeletionPair_involutive
    {n : ℕ}
    (ij : Fin (n + 2) × Fin (n + 1)) :
    swapDeletionPair
        (swapDeletionPair ij) =
      ij := by
  rcases ij with ⟨i, j⟩
  apply Prod.ext
  · exact
      CausalEventCube.swapped_removed_axis
        i j
  · exact
      Fin.predAbove_predAbove_succAbove
        i j

/-- The deletion-order involution has no fixed points. -/
theorem swapDeletionPair_ne
    {n : ℕ}
    (ij : Fin (n + 2) × Fin (n + 1)) :
    swapDeletionPair ij ≠ ij := by
  rcases ij with ⟨i, j⟩
  intro h
  have hfst :=
    congrArg Prod.fst h
  exact (Fin.succAbove_ne i j) hfst

/-- Product of the two alternating face signs attached to one ordered
two-face selection. -/
def deletionPairSign
    {n : ℕ}
    (ij : Fin (n + 2) × Fin (n + 1)) :
    K :=
  faceSign ij.1 * faceSign ij.2

/-- Reversing deletion order negates the total alternating sign. -/
theorem deletionPairSign_swap
    {n : ℕ}
    (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    deletionPairSign
        (swapDeletionPair (i, j)) =
      - deletionPairSign (i, j) := by
  unfold deletionPairSign swapDeletionPair
  unfold faceSign
  calc
    (-1 : K) ^ (i.succAbove j).val *
          (-1 : K) ^ (j.predAbove i).val
        =
      (-1 : K) ^
        ((i.succAbove j).val +
          (j.predAbove i).val) := by
            rw [pow_add]
    _ =
      - ((-1 : K) ^
        (i.val + j.val)) := by
          exact
            Fin.neg_one_pow_succAbove_add_predAbove
              (R := K) i j
    _ =
      - (((-1 : K) ^ i.val) *
          ((-1 : K) ^ j.val)) := by
            rw [pow_add]

/-- One summand in d_(n+1)d_n after the two sums have been flattened.

The four evaluations are the four choices of upper/lower face at the two
successive deleted axes. -/
def secondBoundaryTerm
    {n : ℕ}
    (ω : CausalCubicalCochain S K n)
    (Q : CausalEventCube S (n + 2))
    (ij : Fin (n + 2) × Fin (n + 1)) :
    K :=
  deletionPairSign ij *
    (ω ((Q.upperFace ij.1).upperFace ij.2)
      -
     ω ((Q.upperFace ij.1).lowerFace ij.2)
      -
     ω ((Q.lowerFace ij.1).upperFace ij.2)
      +
     ω ((Q.lowerFace ij.1).lowerFace ij.2))

/-- The geometric four-face expression is invariant under reversing deletion
order, while the alternating coefficient changes sign.  Therefore paired
second-boundary summands cancel. -/
theorem secondBoundaryTerm_swap
    {n : ℕ}
    (ω : CausalCubicalCochain S K n)
    (Q : CausalEventCube S (n + 2))
    (ij : Fin (n + 2) × Fin (n + 1)) :
    secondBoundaryTerm ω Q
        (swapDeletionPair ij)
      =
    - secondBoundaryTerm ω Q ij := by
  rcases ij with ⟨i, j⟩
  unfold secondBoundaryTerm
  rw [deletionPairSign_swap]
  rw [
    ← CausalEventCube.upperFace_upperFace
      Q i j,
    ← CausalEventCube.lowerFace_upperFace
      Q i j,
    ← CausalEventCube.upperFace_lowerFace
      Q i j,
    ← CausalEventCube.lowerFace_lowerFace
      Q i j
  ]
  ring

theorem secondBoundaryTerm_add_swap_eq_zero
    {n : ℕ}
    (ω : CausalCubicalCochain S K n)
    (Q : CausalEventCube S (n + 2))
    (ij : Fin (n + 2) × Fin (n + 1)) :
    secondBoundaryTerm ω Q ij +
      secondBoundaryTerm ω Q
        (swapDeletionPair ij)
      =
    0 := by
  rw [secondBoundaryTerm_swap]
  exact add_neg_cancel _

/-- Expand the composite cubical differential as one sum over ordered pairs of
deleted axes. -/
theorem differential_differential_eq_pairSum
    {n : ℕ}
    (ω : CausalCubicalCochain S K n)
    (Q : CausalEventCube S (n + 2)) :
    differential (S := S) (K := K) (n + 1)
        (differential (S := S) (K := K) n ω)
        Q
      =
    ∑ ij : Fin (n + 2) × Fin (n + 1),
      secondBoundaryTerm ω Q ij := by
  rw [Fintype.sum_prod_type]
  rw [differential_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [faceContribution]
  rw [
    differential_apply,
    differential_apply,
    ← Finset.sum_sub_distrib,
    Finset.mul_sum
  ]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- Arbitrary-degree cubical square-zero theorem.

No square-zero law is assumed in the carrier.  Cancellation follows from the
actual causal cube face identities plus the parity change under reversing two
face deletions. -/
theorem differential_squared
    (n : ℕ)
    (ω : CausalCubicalCochain S K n) :
    differential (S := S) (K := K) (n + 1)
        (differential (S := S) (K := K) n ω)
      =
    0 := by
  funext Q
  rw [differential_differential_eq_pairSum]
  let f :
      Fin (n + 2) × Fin (n + 1) → K :=
    fun ij => secondBoundaryTerm ω Q ij
  have hsum :
      ∑ ij ∈
          (Finset.univ :
            Finset (Fin (n + 2) × Fin (n + 1))),
          f ij
        =
      0 := by
    exact
      Finset.sum_involution
        (fun ij _ =>
          swapDeletionPair ij)
        (fun ij _ =>
          secondBoundaryTerm_add_swap_eq_zero
            ω Q ij)
        (fun ij _ _ =>
          swapDeletionPair_ne ij)
        (fun ij _ =>
          Finset.mem_univ _)
        (fun ij _ =>
          swapDeletionPair_involutive ij)
  simpa [f] using hsum

/-- The raw arbitrary-dimensional causal cubical cochains therefore form a
genuine graded causal cochain complex. -/
def gradedCubicalComplex :
    GradedCausalCochainComplex
      K
      (fun n =>
        CausalCubicalCochain S K n) where
  d :=
    differential
  d_sq := by
    intro n
    apply LinearMap.ext
    intro ω
    funext Q
    exact
      congrFun
        (differential_squared
          (S := S) (K := K) n ω)
        Q

end CausalCubicalCochain
end CausalGeometry
