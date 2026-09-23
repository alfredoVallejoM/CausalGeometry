import Mathlib.Algebra.Group.Defs

namespace CausalGeometry

universe u

namespace CausalDivisibility

variable {α : Type u}

/-- Left divisibility for a possibly noncommutative multiplication. -/
def LeftDivides [Mul α] (x z : α) : Prop :=
  ∃ y, x * y = z

/-- Right divisibility for a possibly noncommutative multiplication. -/
def RightDivides [Mul α] (x z : α) : Prop :=
  ∃ y, y * x = z

theorem left_refl [Monoid α] (x : α) : LeftDivides x x :=
  ⟨1, by simp [LeftDivides]⟩

theorem right_refl [Monoid α] (x : α) : RightDivides x x :=
  ⟨1, by simp [RightDivides]⟩

theorem left_trans [Semigroup α] {x y z : α}
    (hxy : LeftDivides x y) (hyz : LeftDivides y z) :
    LeftDivides x z := by
  rcases hxy with ⟨a, rfl⟩
  rcases hyz with ⟨b, rfl⟩
  exact ⟨a * b, by simp [mul_assoc]⟩

theorem right_trans [Semigroup α] {x y z : α}
    (hxy : RightDivides x y) (hyz : RightDivides y z) :
    RightDivides x z := by
  rcases hxy with ⟨a, rfl⟩
  rcases hyz with ⟨b, rfl⟩
  exact ⟨b * a, by simp [mul_assoc]⟩

/-- Two-sided invertibility stated without introducing a separate group
structure on the full causal domain. -/
def IsCausalUnit [Monoid α] (x : α) : Prop :=
  ∃ y, x * y = 1 ∧ y * x = 1

theorem one_isCausalUnit [Monoid α] : IsCausalUnit (1 : α) :=
  ⟨1, by simp, by simp⟩

theorem unit_left_divides_all [Monoid α] {u : α}
    (hu : IsCausalUnit u) (z : α) :
    LeftDivides u z := by
  rcases hu with ⟨v, huv, hvu⟩
  exact ⟨v * z, by simp [mul_assoc, huv]⟩

theorem unit_right_divides_all [Monoid α] {u : α}
    (hu : IsCausalUnit u) (z : α) :
    RightDivides u z := by
  rcases hu with ⟨v, huv, hvu⟩
  exact ⟨z * v, by simp [mul_assoc, hvu]⟩

end CausalDivisibility
end CausalGeometry
