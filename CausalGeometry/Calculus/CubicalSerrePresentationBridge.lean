import CausalGeometry.Calculus.CubicalShuffleSubsetEquiv
import CausalGeometry.Calculus.CubicalFrontFaceStructure
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Once the selected/complement cubes agree with the canonical front/back
faces, the intrinsic subset term is exactly the corresponding shuffle term. -/
theorem subsetCupTerm_eq_shuffleCupTerm
    (p q : ℕ)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q))
    (A : CausalEventCube.AxisSubset (p + q) p)
    (hmatch : SubsetTermMatchesShuffle p q Q A) :
    subsetCupTerm p q alpha beta Q A
      =
    shuffleCupTerm p q alpha beta Q
      (CausalEventCube.subsetShuffle A) := by

  rcases hmatch with ⟨hfront, hback⟩

  unfold subsetCupTerm
    subsetShuffleSign
    shuffleCupTerm
    orderedCup

  rw [hfront, hback]

/-- The only geometric obligation needed to identify the two global Serre-cup
presentations. -/
def AllSubsetTermsMatch
    (p q : ℕ) : Prop :=
  ∀ (Q : CausalEventCube S (p + q))
    (A : CausalEventCube.AxisSubset (p + q) p),
      SubsetTermMatchesShuffle p q Q A

/-- The subset-indexed and shuffle-indexed Serre products are equal as soon as
the factor-cube comparison is available.

All combinatorial reindexing is discharged here; future proofs only need the
geometric front/back equalities. -/
theorem subsetSerreCup_eq_serreCup_of_matches
    (p q : ℕ)
    (hmatch : AllSubsetTermsMatch
      (S := S) p q)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q) :
    subsetSerreCup p q alpha beta =
      serreCup p q alpha beta := by

  funext Q

  rw [subsetSerreCup_apply,
    serreCup_apply]

  let E :=
    shuffleSubsetEquiv p q

  calc
    (∑ A :
        CausalEventCube.AxisSubset (p + q) p,
        subsetCupTerm p q alpha beta Q A)
        =
      ∑ sigma : CubicalShuffle p q,
        subsetCupTerm p q alpha beta Q
          (E sigma) := by
            symm
            exact
              Equiv.sum_comp E
                (fun A =>
                  subsetCupTerm
                    p q alpha beta Q A)

    _ =
      ∑ sigma : CubicalShuffle p q,
        shuffleCupTerm
          p q alpha beta Q sigma := by
            apply Fintype.sum_congr
            intro sigma

            rw [
              subsetCupTerm_eq_shuffleCupTerm
                p q alpha beta Q
                (E sigma)
                (hmatch Q (E sigma))
            ]

            change
              shuffleCupTerm
                  p q alpha beta Q
                  (CausalEventCube.subsetShuffle
                    (shuffleAxisSubset sigma))
                =
              shuffleCupTerm
                p q alpha beta Q sigma

            rw [subsetShuffle_shuffleAxisSubset]

end CausalCubicalCochain
end CausalGeometry
