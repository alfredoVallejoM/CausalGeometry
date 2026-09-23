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

/-- Exact left division is saturation of the residual counit. -/
def ExactLeftDivision [PartialOrder α] (x z : α) : Prop :=
  x * R.leftResidual x z = z

/-- Exact right division is saturation of the residual counit. -/
def ExactRightDivision [PartialOrder α] (z x : α) : Prop :=
  R.rightResidual z x * x = z

end ResiduatedMultiplication
end CausalGeometry
