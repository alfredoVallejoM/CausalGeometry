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
  componentNonempty := inferInstance
  componentOf := fun _ => PUnit.unit
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
  componentNonempty := inferInstance
  componentOf :=
    fun b =>
      match b with
      | false => 0
      | true => 1
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

/-! ## Same index, different quotient map over a fixed point map -/

/-- Projection to the first Boolean coordinate. -/
def firstCoordinateQuotient :
    LocalComponentQuotient (Bool × Bool) where
  Component := Bool
  finiteComponent := inferInstance
  componentNonempty := inferInstance
  componentOf := Prod.fst
  surjective := by
    intro b
    exact ⟨(b, false), rfl⟩

/-- Projection to the second Boolean coordinate. -/
def secondCoordinateQuotient :
    LocalComponentQuotient (Bool × Bool) where
  Component := Bool
  finiteComponent := inferInstance
  componentNonempty := inferInstance
  componentOf := Prod.snd
  surjective := by
    intro b
    exact ⟨(false, b), rfl⟩

/-- The two quotient maps have the same Tamagawa index. -/
theorem coordinateQuotients_same_tamagawa :
    firstCoordinateQuotient.tamagawaIndex =
      secondCoordinateQuotient.tamagawaIndex := by
  rfl

/-- Numerical equality does not make the quotient square commute over a fixed
identity map on local points.

There is no component equivalence sending the first-coordinate quotient to
the second-coordinate quotient while the point carrier itself is left
unchanged. -/
theorem coordinateQuotients_no_commuting_equiv_over_id :
    ¬ ∃ e :
        firstCoordinateQuotient.Component ≃
          secondCoordinateQuotient.Component,
      ∀ p : Bool × Bool,
        e (firstCoordinateQuotient.componentOf p) =
          secondCoordinateQuotient.componentOf p := by
  rintro ⟨e, he⟩
  have hfalse : e false = false := by
    simpa [
      firstCoordinateQuotient,
      secondCoordinateQuotient
    ] using he (false, false)
  have htrue : e false = true := by
    simpa [
      firstCoordinateQuotient,
      secondCoordinateQuotient
    ] using he (false, true)
  rw [hfalse] at htrue
  simp at htrue

/-- Native cyclic type-I control with multiplicity two.  This control is
separate from the point-count mutation above: here both the local point carrier
and the component carrier are the cyclic type required by the Tate
comparison. -/
def typeITwo :
    LocalComponentQuotient
      (Multiplicative (ZMod 2)) where
  Component := Multiplicative (ZMod 2)
  finiteComponent := inferInstance
  componentNonempty := inferInstance
  componentOf := id
  surjective := by
    intro y
    exact ⟨y, rfl⟩

/-- Type-I regression model with multiplicity two. -/
def typeITwoComparison :
    TateTypeIComparison typeITwo where
  multiplicity := 2
  positive := by norm_num
  componentEquiv :=
    Equiv.refl (Multiplicative (ZMod 2))

/-- The split-multiplicative/type-I comparison derives c=2 from the cyclic
component equivalence instead of taking the integer as an unrelated field. -/
theorem typeITwo_regression :
    typeITwo.tamagawaIndex =
      typeITwoComparison.multiplicity :=
  TateTypeIComparison
    .tamagawaIndex_eq_multiplicity
      typeITwoComparison

end TamagawaControls
end Models
end CausalGeometry
