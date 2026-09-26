import CausalGeometry.Calculus.CubicalSubsetGeometry
import CausalGeometry.Calculus.CubicalShuffleCup
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Canonical permutation associated to a p-subset of the p+q axes:
selected axes first in increasing order, then the complement in increasing
order. -/
noncomputable def subsetPermutation
    {p q : ℕ}
    (A : AxisSubset (p + q) p) :
    Equiv.Perm (Fin (p + q)) :=
  Set.powersetCard.permOfDisjoint
    (s := A)
    (t := A.complementAxes)
    (by
      change Disjoint A.val A.valᶜ
      exact disjoint_compl_right)

/-- The first p coordinates of the canonical subset permutation enumerate A
in increasing order. -/
theorem subsetPermutation_left
    {p q : ℕ}
    (A : AxisSubset (p + q) p)
    (i : Fin p) :
    A.subsetPermutation
        (leftBlockIndex p q i)
      =
    (Set.powersetCard.orderIsoOfFin A i).1 := by
  simp [subsetPermutation,
    Set.powersetCard.permOfDisjoint,
    leftBlockIndex,
    complementAxes]

/-- The final q coordinates enumerate the complement in increasing order. -/
theorem subsetPermutation_right
    {p q : ℕ}
    (A : AxisSubset (p + q) p)
    (j : Fin q) :
    A.subsetPermutation
        (rightBlockIndex p q j)
      =
    (Set.powersetCard.orderIsoOfFin
      A.complementAxes j).1 := by
  simp [subsetPermutation,
    Set.powersetCard.permOfDisjoint,
    rightBlockIndex,
    complementAxes]

/-- Every fixed-cardinality axis subset canonically determines a shuffle. -/
noncomputable def subsetShuffle
    {p q : ℕ}
    (A : AxisSubset (p + q) p) :
    CausalCubicalCochain.CubicalShuffle p q :=
  ⟨A.subsetPermutation, by
    constructor
    · intro i j hij
      rw [A.subsetPermutation_left i,
        A.subsetPermutation_left j]
      exact
        (Set.powersetCard.orderIsoOfFin A)
          .strictMono hij
    · intro i j hij
      rw [A.subsetPermutation_right i,
        A.subsetPermutation_right j]
      exact
        (Set.powersetCard.orderIsoOfFin
          A.complementAxes).strictMono hij⟩

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Sign of one p-axis subset, defined by the inversion parity of its canonical
shuffle permutation. -/
noncomputable def subsetShuffleSign
    {p q : ℕ}
    (A : CausalEventCube.AxisSubset (p + q) p) :
    K :=
  shuffleSign (K := K)
    (CausalEventCube.subsetShuffle A)

/-- One intrinsic subset term of the causal Serre product. -/
noncomputable def subsetCupTerm
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q))
    (A : CausalEventCube.AxisSubset (p + q) p) :
    K :=
  subsetShuffleSign (K := K) A *
    α (Q.selectedCube A) *
    β (Q.complementCube A)

/-- Intrinsic subset presentation of the full cubical product.

The sum is over p-element subsets of the p+q ambient axes.  It is designed to
be equivalent to the permutation/shuffle presentation serreCup, but its
indexing makes face deletion and Leibniz cancellation substantially cleaner. -/
noncomputable def subsetSerreCup
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) :
    CausalCubicalCochain S K (p + q) :=
  fun Q =>
    ∑ A :
        CausalEventCube.AxisSubset (p + q) p,
      subsetCupTerm p q α β Q A

@[simp] theorem subsetSerreCup_apply
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q)) :
    subsetSerreCup p q α β Q =
      ∑ A :
          CausalEventCube.AxisSubset (p + q) p,
        subsetCupTerm p q α β Q A :=
  rfl

theorem subsetSerreCup_add_left
    (p q : ℕ)
    (α γ : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) :
    subsetSerreCup p q (α + γ) β =
      subsetSerreCup p q α β +
        subsetSerreCup p q γ β := by
  funext Q
  simp [subsetSerreCup, subsetCupTerm,
    Finset.sum_add_distrib, add_mul]

theorem subsetSerreCup_add_right
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β γ : CausalCubicalCochain S K q) :
    subsetSerreCup p q α (β + γ) =
      subsetSerreCup p q α β +
        subsetSerreCup p q α γ := by
  funext Q
  simp [subsetSerreCup, subsetCupTerm,
    Finset.sum_add_distrib, mul_add,
    mul_assoc]

/-- Each subset term is literally the shuffle term of its canonical shuffle
once the two derived factor cubes are identified with the corresponding
ordered front/back cubes.  The two cube equalities are kept explicit as the
remaining geometric comparison obligation. -/
def SubsetTermMatchesShuffle
    (p q : ℕ)
    (Q : CausalEventCube S (p + q))
    (A : CausalEventCube.AxisSubset (p + q) p) : Prop :=
  Q.selectedCube A =
      (Q.permute
        (CausalEventCube.subsetPermutation A))
        .frontFace p q
    ∧
  Q.complementCube A =
      (Q.permute
        (CausalEventCube.subsetPermutation A))
        .backFace p q

end CausalCubicalCochain
end CausalGeometry
