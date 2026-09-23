import CausalGeometry.Number.Prime
import Mathlib.Data.List.Defs

namespace CausalGeometry

universe u

namespace CausalFactorization

open CausalDivisibility CausalPrime

variable {α : Type u} [Monoid α]

/-- Ordered factorization word.  Order is retained until an explicit quotient
or commutative realization removes it. -/
def eval (xs : List α) : α :=
  xs.prod

def IsFactorization (xs : List α) (x : α) : Prop :=
  eval xs = x

def IsAtomicFactorization (xs : List α) (x : α) : Prop :=
  IsFactorization xs x ∧ ∀ p ∈ xs, Irreducible p

@[simp] theorem eval_nil : eval ([] : List α) = 1 := by
  simp [eval]

@[simp] theorem eval_cons (x : α) (xs : List α) :
    eval (x :: xs) = x * eval xs := by
  simp [eval]

theorem eval_append (xs ys : List α) :
    eval (xs ++ ys) = eval xs * eval ys := by
  simp [eval]

theorem factorization_append {xs ys : List α} {x y : α}
    (hx : IsFactorization xs x) (hy : IsFactorization ys y) :
    IsFactorization (xs ++ ys) (x * y) := by
  simpa [IsFactorization, eval_append, hx, hy]

/-- Every nonempty factorization exposes a left divisor. -/
theorem head_leftDivides {p : α} {xs : List α} {x : α}
    (h : IsFactorization (p :: xs) x) :
    LeftDivides p x := by
  refine ⟨eval xs, ?_⟩
  simpa [IsFactorization, eval_cons] using h

end CausalFactorization
end CausalGeometry
