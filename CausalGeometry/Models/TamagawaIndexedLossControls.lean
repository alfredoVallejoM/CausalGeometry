import CausalGeometry.Models.TamagawaControls
import CausalGeometry.Realization.IndexedFamily

namespace CausalGeometry
namespace Models
namespace TamagawaIndexedLossControls

namespace TC := TamagawaControls

/-- Two source states select two genuinely different quotient maps. -/
abbrev Source := Bool

/-- One local place is enough for the strict-loss discriminator. -/
abbrev Place := PUnit

/-- Structural local observation: retain the quotient map itself.

The two maps have the same point carrier and same component carrier, but one
projects to the first Boolean coordinate and the other to the second. -/
def quotientMapFamily :
    IndexedRealizationFamily Source Place where
  Target := fun _ => (Bool × Bool) → Bool
  realize :=
    fun _ source =>
      if source then Prod.snd else Prod.fst

/-- Numerical Tamagawa observation: retain only the common index two. -/
def indexFamily :
    IndexedRealizationFamily Source Place where
  Target := fun _ => ℕ
  realize := fun _ _ => 2

/-- Forget the quotient map and retain only its common Tamagawa cardinal. -/
def quotientMapToIndex :
    IndexedRealizationFamily.Comparison
      quotientMapFamily indexFamily where
  map := fun _ _ => 2
  commutes := by
    intro source place
    rfl

/-- The two structural quotient maps are distinct. -/
theorem quotientMaps_distinct :
    quotientMapFamily.realize PUnit.unit false ≠
      quotientMapFamily.realize PUnit.unit true := by
  intro h
  have hp :=
    congrFun h (false, true)
  norm_num [quotientMapFamily] at hp

/-- The numerical index realization collapses the two source states. -/
theorem indices_collapse :
    indexFamily.CollapsesEverywhere
      false true := by
  intro place
  rfl

/-- The structural realization still separates them. -/
theorem quotientMaps_separate :
    ¬ quotientMapFamily.CollapsesEverywhere
      false true := by
  intro h
  exact quotientMaps_distinct (h PUnit.unit)

/-- Concrete strict information-loss witness:
quotient map -> Tamagawa index. -/
def strictLoss :
    IndexedRealizationFamily.StrictLossWitness
      quotientMapToIndex where
  source₁ := false
  source₂ := true
  distinct := by decide
  targetCollapse := indices_collapse
  sourceSeparated := quotientMaps_separate

/-- Bare Tamagawa index observations are not jointly conservative even though
the structural quotient-map family distinguishes the sources. -/
theorem indexFamily_not_jointlyConservative :
    ¬ indexFamily.JointlyConservative :=
  strictLoss.target_not_jointlyConservative

/-- Therefore no explicit reconstruction of the source can exist from the
bare local Tamagawa index family. -/
theorem indexFamily_noReconstruction :
    IsEmpty
      (IndexedRealizationFamily.Reconstruction
        indexFamily) :=
  strictLoss.target_noReconstruction

/-- The structural quotient-map family itself is jointly conservative in this
two-source control. -/
theorem quotientMapFamily_jointlyConservative :
    quotientMapFamily.JointlyConservative := by
  intro x y h
  cases x <;> cases y
  · rfl
  · exfalso
    exact quotientMaps_distinct (h PUnit.unit)
  · exfalso
    exact quotientMaps_distinct (h PUnit.unit).symm
  · rfl

/-- Stable positive/negative loss discriminator for the Tamagawa layer. -/
def Consumer : Prop :=
  quotientMapFamily.JointlyConservative ∧
    ¬ indexFamily.JointlyConservative ∧
    IsEmpty
      (IndexedRealizationFamily.Reconstruction
        indexFamily) ∧
    TC.firstCoordinateQuotient.tamagawaIndex =
      TC.secondCoordinateQuotient.tamagawaIndex ∧
    ¬ ∃ e :
        TC.firstCoordinateQuotient.Component ≃
          TC.secondCoordinateQuotient.Component,
      ∀ p : Bool × Bool,
        e (TC.firstCoordinateQuotient.componentOf p) =
          TC.secondCoordinateQuotient.componentOf p

theorem consumer : Consumer :=
  ⟨quotientMapFamily_jointlyConservative,
    indexFamily_not_jointlyConservative,
    indexFamily_noReconstruction,
    TC.coordinateQuotients_same_tamagawa,
    TC.coordinateQuotients_no_commuting_equiv_over_id⟩

end TamagawaIndexedLossControls
end Models
end CausalGeometry
