import CausalGeometry.Realization.ECIATamagawaContract
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace TamagawaControls

open Tamagawa

/-- Same local point carrier, with all points collapsed to the identity
component.  This is the finite control shape of good reduction. -/
def collapsedBool :
    LocalComponentQuotient Bool where
  Component := PUnit
  finiteComponent := inferInstance
  componentOf := fun _ => PUnit.unit
  basePoint := false
  baseComponent := PUnit.unit
  base_eq := rfl
  surjective := by
    intro y
    cases y
    exact ⟨false, rfl⟩

/-- Same local point carrier, but the two points remain in distinct
components. -/
def separatedBool :
    LocalComponentQuotient Bool where
  Component := Fin 2
  finiteComponent := inferInstance
  componentOf :=
    fun b =>
      match b with
      | false => 0
      | true => 1
  basePoint := false
  baseComponent := 0
  base_eq := by simp
  surjective := by
    intro y
    fin_cases y
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩

/-- The collapsed local quotient has Tamagawa index one. -/
theorem collapsedBool_tamagawa :
    collapsedBool.tamagawaIndex = 1 := by
  simp [
    collapsedBool,
    LocalComponentQuotient.tamagawaIndex
  ]

/-- The separated local quotient has Tamagawa index two. -/
theorem separatedBool_tamagawa :
    separatedBool.tamagawaIndex = 2 := by
  simp [
    separatedBool,
    LocalComponentQuotient.tamagawaIndex
  ]

/-- Mutation discriminator: local point count alone does not determine the
Tamagawa index.

Both models have exactly the same local point carrier `Bool`, hence the same
point count, while their component quotients have distinct cardinalities. -/
theorem same_local_points_different_tamagawa :
    collapsedBool.tamagawaIndex ≠
      separatedBool.tamagawaIndex := by
  rw [
    collapsedBool_tamagawa,
    separatedBool_tamagawa
  ]
  norm_num

/-- The control makes the information-loss statement explicit: recording only
the number of local points cannot reconstruct the component quotient. -/
theorem point_count_does_not_determine_tamagawa :
    Fintype.card Bool = Fintype.card Bool ∧
      collapsedBool.tamagawaIndex ≠
        separatedBool.tamagawaIndex := by
  exact
    ⟨rfl,
     same_local_points_different_tamagawa⟩

/-- Positive good-reduction-style comparison: the collapsed component carrier
is explicitly equivalent to the one-point carrier required by the structural
unit theorem. -/
def collapsedBoolPUnitEquiv :
    collapsedBool.Component ≃ PUnit :=
  Equiv.refl PUnit

/-- The generic unit theorem recovers the concrete control result. -/
theorem collapsedBool_from_component_equiv :
    collapsedBool.tamagawaIndex = 1 :=
  LocalComponentQuotient
    .tamagawaIndex_eq_one_of_punit_equiv
      collapsedBool
      collapsedBoolPUnitEquiv

/-- Type-I regression model with multiplicity two. -/
def separatedBoolTypeI :
    TateTypeIComparison separatedBool where
  multiplicity := 2
  positive := by norm_num
  componentEquiv :=
    Equiv.refl (Fin 2)

/-- The split-multiplicative/type-I comparison derives c=2 from the component
equivalence instead of taking the integer as an unrelated field. -/
theorem separatedBool_typeI_regression :
    separatedBool.tamagawaIndex =
      separatedBoolTypeI.multiplicity :=
  TateTypeIComparison
    .tamagawaIndex_eq_multiplicity
      separatedBoolTypeI

end TamagawaControls
end Models
end CausalGeometry
