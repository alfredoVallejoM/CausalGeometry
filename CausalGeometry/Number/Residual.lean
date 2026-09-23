import CausalGeometry.Foundation.ExtensionRestriction
import CausalGeometry.Number.Divisibility
import Mathlib.Order.Basic

namespace CausalGeometry

universe u

/-- Residuation of a possibly noncommutative causal multiplication.
The two residuals are kept distinct. -/
structure ResiduatedMultiplication
    (α : Type u) [Preorder α] [Mul α] where
  leftResidual : α → α → α
  rightResidual : α → α → α
  leftAdjunction :
    ∀ x y z, x * y ≤ z ↔ y ≤ leftResidual x z
  rightAdjunction :
    ∀ x y z, y * x ≤ z ↔ y ≤ rightResidual z x

namespace ResiduatedMultiplication

open CausalDivisibility

variable {α : Type u} [Preorder α] [Mul α]
variable (R : ResiduatedMultiplication α)

theorem leftUnit (x y : α) :
    y ≤ R.leftResidual x (x * y) :=
  (R.leftAdjunction x y (x * y)).mp le_rfl

theorem leftCounit (x z : α) :
    x * R.leftResidual x z ≤ z :=
  (R.leftAdjunction x (R.leftResidual x z) z).mpr le_rfl

theorem rightUnit (x y : α) :
    y ≤ R.rightResidual (y * x) x :=
  (R.rightAdjunction x y (y * x)).mp le_rfl

theorem rightCounit (z x : α) :
    R.rightResidual z x * x ≤ z :=
  (R.rightAdjunction x (R.rightResidual z x) z).mpr le_rfl

/-- Left multiplication is monotone because it is a left adjoint. -/
theorem monotone_leftMul (x : α) :
    Monotone (fun y => x * y) := by
  intro y y' hyy
  apply (R.leftAdjunction x y (x * y')).mpr
  exact hyy.trans (R.leftUnit x y')

/-- Right multiplication is monotone because it is a left adjoint. -/
theorem monotone_rightMul (x : α) :
    Monotone (fun y => y * x) := by
  intro y y' hyy
  apply (R.rightAdjunction x y (y' * x)).mpr
  exact hyy.trans (R.rightUnit x y')

/-- A left residual is monotone in its target. -/
theorem monotone_leftResidual (x : α) :
    Monotone (R.leftResidual x) := by
  intro z z' hzz
  apply (R.leftAdjunction x (R.leftResidual x z) z').mp
  exact (R.leftCounit x z).trans hzz

/-- A right residual is monotone in its target. -/
theorem monotone_rightResidual (x : α) :
    Monotone (fun z => R.rightResidual z x) := by
  intro z z' hzz
  apply (R.rightAdjunction x (R.rightResidual z x) z').mp
  exact (R.rightCounit z x).trans hzz

/-- Increasing the left divisor can only decrease the admissible residual. -/
theorem antitone_leftResidual_first (z : α) :
    Antitone (fun x => R.leftResidual x z) := by
  intro x x' hxx
  apply (R.leftAdjunction x (R.leftResidual x' z) z).mp
  exact (R.monotone_rightMul (R.leftResidual x' z) hxx).trans
    (R.leftCounit x' z)

/-- Increasing the right divisor can only decrease the admissible residual. -/
theorem antitone_rightResidual_second (z : α) :
    Antitone (fun x => R.rightResidual z x) := by
  intro x x' hxx
  apply (R.rightAdjunction x (R.rightResidual z x') z).mp
  exact (R.monotone_leftMul (R.rightResidual z x') hxx).trans
    (R.rightCounit z x')

/-- Exact left division is saturation of the residual counit. -/
def ExactLeftDivision [PartialOrder α] (x z : α) : Prop :=
  x * R.leftResidual x z = z

/-- Exact right division is saturation of the residual counit. -/
def ExactRightDivision [PartialOrder α] (z x : α) : Prop :=
  R.rightResidual z x * x = z

theorem exactLeftDivision_iff_leftDivides [PartialOrder α] (x z : α) :
    R.ExactLeftDivision x z ↔ LeftDivides x z := by
  constructor
  · intro h
    exact ⟨R.leftResidual x z, h⟩
  · rintro ⟨y, rfl⟩
    apply le_antisymm
    · exact R.leftCounit x (x * y)
    · exact R.monotone_leftMul x (R.leftUnit x y)

theorem exactRightDivision_iff_rightDivides [PartialOrder α] (z x : α) :
    R.ExactRightDivision z x ↔ RightDivides x z := by
  constructor
  · intro h
    exact ⟨R.rightResidual z x, h⟩
  · rintro ⟨y, rfl⟩
    apply le_antisymm
    · exact R.rightCounit (y * x) x
    · exact R.monotone_rightMul x (R.rightUnit x y)

/-- Multiplication on the left is an extension operation and left residual is
its correlative restriction. -/
def leftExtensionRestriction (x : α) :
    ExtensionRestriction α α where
  extend := fun y => x * y
  restrict := R.leftResidual x
  adjunction := R.leftAdjunction x

/-- Multiplication on the right is an extension operation and right residual
is its correlative restriction. -/
def rightExtensionRestriction (x : α) :
    ExtensionRestriction α α where
  extend := fun y => y * x
  restrict := fun z => R.rightResidual z x
  adjunction := by
    intro y z
    exact R.rightAdjunction x y z

end ResiduatedMultiplication
end CausalGeometry
