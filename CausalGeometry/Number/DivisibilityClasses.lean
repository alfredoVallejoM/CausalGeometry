import CausalGeometry.Number.DivisibilityOrder
import Mathlib.Order.Antisymmetrization

namespace CausalGeometry

universe u

namespace CausalDivisibilityClasses

open CausalDivisibility

variable (α : Type u) [Monoid α]

/-- Canonical partial order obtained from left causal divisibility by
identifying mutually left-divisible elements. -/
abbrev Left :=
  Antisymmetrization (LeftDivOrder α) (· ≤ ·)

/-- Canonical partial order obtained from right causal divisibility by
identifying mutually right-divisible elements. -/
abbrev Right :=
  Antisymmetrization (RightDivOrder α) (· ≤ ·)

/-- Class of a causal number in the left-divisibility antisymmetrization. -/
def leftClass (x : α) : Left α :=
  toAntisymmetrization (· ≤ ·)
    (show LeftDivOrder α from x)

/-- Class of a causal number in the right-divisibility antisymmetrization. -/
def rightClass (x : α) : Right α :=
  toAntisymmetrization (· ≤ ·)
    (show RightDivOrder α from x)

theorem leftClass_eq_iff (x y : α) :
    leftClass α x = leftClass α y ↔
      LeftDivides x y ∧ LeftDivides y x := by
  rw [toAntisymmetrization_eq]
  rfl

theorem rightClass_eq_iff (x y : α) :
    rightClass α x = rightClass α y ↔
      RightDivides x y ∧ RightDivides y x := by
  rw [toAntisymmetrization_eq]
  rfl

theorem leftClass_le_iff (x y : α) :
    leftClass α x ≤ leftClass α y ↔
      LeftDivides x y := by
  exact
    toAntisymmetrization_le_toAntisymmetrization_iff

theorem rightClass_le_iff (x y : α) :
    rightClass α x ≤ rightClass α y ↔
      RightDivides x y := by
  exact
    toAntisymmetrization_le_toAntisymmetrization_iff

/-- A causal unit is left-divisibility equivalent to the multiplicative
identity. -/
theorem leftClass_eq_one_of_unit {u : α}
    (hu : IsCausalUnit u) :
    leftClass α u = leftClass α 1 := by
  apply (leftClass_eq_iff α u 1).2
  constructor
  · rcases hu with ⟨v, huv, hvu⟩
    exact ⟨v, huv⟩
  · exact unit_left_divides_all hu u

/-- A causal unit is right-divisibility equivalent to the multiplicative
identity. -/
theorem rightClass_eq_one_of_unit {u : α}
    (hu : IsCausalUnit u) :
    rightClass α u = rightClass α 1 := by
  apply (rightClass_eq_iff α u 1).2
  constructor
  · rcases hu with ⟨v, huv, hvu⟩
    exact ⟨v, hvu⟩
  · exact unit_right_divides_all hu u

end CausalDivisibilityClasses
end CausalGeometry
