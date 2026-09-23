import CausalGeometry.Number.Divisibility
import Mathlib.Algebra.GroupPower.Lemmas

namespace CausalGeometry

universe u

namespace CausalValuation

open CausalDivisibility

variable {α : Type u} [Monoid α]

/-- A prime/primary power divides a causal number on the left. -/
def PowerLeftDivides (p : α) (r : ℕ) (x : α) : Prop :=
  LeftDivides (p ^ r) x

/-- A certified finite primary depth.  Existence is a theorem obligation, not
an axiom of every causal number. -/
structure PrimaryDepth (p x : α) where
  depth : ℕ
  divides : PowerLeftDivides p depth x
  maximal : ∀ r, PowerLeftDivides p r x → r ≤ depth

theorem PrimaryDepth.unique {p x : α}
    (a b : PrimaryDepth p x) :
    a.depth = b.depth :=
  le_antisymm (b.maximal a.depth a.divides)
    (a.maximal b.depth b.divides)

/-- The valuation extracted from a certified primary depth. -/
def valuation {p x : α} (h : PrimaryDepth p x) : ℕ :=
  h.depth

@[simp] theorem valuation_eq_depth {p x : α} (h : PrimaryDepth p x) :
    valuation h = h.depth := rfl

/-- Depth zero is always an admissible divisor witness. -/
theorem power_zero_leftDivides (p x : α) :
    PowerLeftDivides p 0 x := by
  refine ⟨x, ?_⟩
  simp [PowerLeftDivides, LeftDivides]

end CausalValuation
end CausalGeometry
