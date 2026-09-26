import CausalGeometry.Calculus.CubicalSerrePresentationBridge
import CausalGeometry.Calculus.CubicalBackFaceStructure
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- The selected and complementary intrinsic cubes are exactly the two
front/back factors of the canonical shuffle, for every axis subset. -/
theorem allSubsetTermsMatch
    (p q : ℕ) :
    AllSubsetTermsMatch (S := S) p q := by

  intro Q A

  exact
    ⟨
      CausalEventCube.selectedCube_eq_frontFace
        Q A,
      CausalEventCube.complementCube_eq_backFace
        Q A
    ⟩

/-- The intrinsic subset presentation and the shuffle presentation of the
causal Serre cup are exactly equal. -/
theorem subsetSerreCup_eq_serreCup
    (p q : ℕ)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q) :
    subsetSerreCup p q alpha beta =
      serreCup p q alpha beta :=
  subsetSerreCup_eq_serreCup_of_matches
    p q
    (allSubsetTermsMatch
      (S := S) p q)
    alpha beta

end CausalCubicalCochain
end CausalGeometry
