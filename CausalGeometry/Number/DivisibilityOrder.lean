import CausalGeometry.Number.Divisibility

namespace CausalGeometry

universe u

/-- Type synonym carrying the left-divisibility preorder. -/
def LeftDivOrder (α : Type u) :=
  α

/-- Type synonym carrying the right-divisibility preorder. -/
def RightDivOrder (α : Type u) :=
  α

namespace DivisibilityOrder

open CausalDivisibility

variable {α : Type u}

instance [Monoid α] : Preorder (LeftDivOrder α) where
  le x y := LeftDivides (show α from x) (show α from y)
  le_refl x := left_refl (show α from x)
  le_trans _ _ _ := left_trans

instance [Monoid α] : Preorder (RightDivOrder α) where
  le x y := RightDivides (show α from x) (show α from y)
  le_refl x := right_refl (show α from x)
  le_trans _ _ _ := right_trans

@[simp] theorem left_le_iff [Monoid α] (x y : α) :
    (show LeftDivOrder α from x) ≤ (show LeftDivOrder α from y) ↔
      LeftDivides x y :=
  Iff.rfl

@[simp] theorem right_le_iff [Monoid α] (x y : α) :
    (show RightDivOrder α from x) ≤ (show RightDivOrder α from y) ↔
      RightDivides x y :=
  Iff.rfl

end DivisibilityOrder
end CausalGeometry
