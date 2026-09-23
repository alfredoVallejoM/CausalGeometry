import CausalGeometry.Models.RelationArithmetic

namespace CausalGeometry

namespace RelationArithmeticExample

def up : CausalRelation Bool :=
  fun a b => a = false ∧ b = true

def down : CausalRelation Bool :=
  fun a b => a = true ∧ b = false

theorem up_down_false_loop :
    (up * down) false false := by
  exact ⟨true, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem down_up_no_false_loop :
    ¬ (down * up) false false := by
  rintro ⟨b, hb, hrest⟩
  cases hb.1

theorem noncommutative :
    up * down ≠ down * up := by
  intro h
  have hloop := up_down_false_loop
  rw [h] at hloop
  exact down_up_no_false_loop hloop

end RelationArithmeticExample
end CausalGeometry
