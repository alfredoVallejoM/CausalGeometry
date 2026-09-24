import CausalGeometry.Cyclic.Hashimoto
import Mathlib.Tactic

namespace CausalGeometry.Models

/-- One-vertex graph with two opposite oriented loop-edges.

The two Bool edges are reverses of each other. This is the smallest same-type
control that distinguishes continuing in one orientation from immediate
backtracking. -/
def twoOrientationLoop :
    FiniteDirectedEdgeSystem Unit Bool where
  source := fun _ => ()
  target := fun _ => ()
  reverse := not
  reverse_involutive := by
    intro e
    cases e <;> rfl
  source_reverse := by
    intro e
    rfl
  target_reverse := by
    intro e
    rfl
  reverse_ne := by
    intro e
    cases e <;> decide

theorem forward_repeat_nonbacktracking :
    twoOrientationLoop.Nonbacktracking false false := by
  constructor
  · rfl
  · decide

theorem forward_reverse_is_backtracking :
    ¬ twoOrientationLoop.Nonbacktracking false true := by
  intro h
  exact h.2 rfl

theorem reverse_repeat_nonbacktracking :
    twoOrientationLoop.Nonbacktracking true true := by
  constructor
  · rfl
  · decide

theorem reverse_forward_is_backtracking :
    ¬ twoOrientationLoop.Nonbacktracking true false := by
  intro h
  exact h.2 rfl

@[simp] theorem hashimoto_false_false :
    twoOrientationLoop.hashimotoWeight
      (R := ℤ) false false = 1 :=
  twoOrientationLoop.hashimotoWeight_eq_one
    forward_repeat_nonbacktracking

@[simp] theorem hashimoto_false_true :
    twoOrientationLoop.hashimotoWeight
      (R := ℤ) false true = 0 :=
  twoOrientationLoop.hashimotoWeight_eq_zero
    forward_reverse_is_backtracking

@[simp] theorem hashimoto_true_false :
    twoOrientationLoop.hashimotoWeight
      (R := ℤ) true false = 0 :=
  twoOrientationLoop.hashimotoWeight_eq_zero
    reverse_forward_is_backtracking

@[simp] theorem hashimoto_true_true :
    twoOrientationLoop.hashimotoWeight
      (R := ℤ) true true = 1 :=
  twoOrientationLoop.hashimotoWeight_eq_one
    reverse_repeat_nonbacktracking

/-- At one transition the closed-walk count is exactly the two allowed
orientation-preserving loops. -/
theorem hashimoto_closedWalkCount_one :
    twoOrientationLoop.closedWalkCount (R := ℤ) 1 = 2 := by
  simp [FiniteDirectedEdgeSystem.closedWalkCount,
    FiniteDirectedEdgeSystem.walkCount]

end CausalGeometry.Models
