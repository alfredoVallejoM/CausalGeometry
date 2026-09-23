import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Divisors

namespace CausalGeometry

universe u v

namespace FactorizationConvolution

/-- A domain whose admissible elements have finitely many ordered
factorizations into two factors. -/
structure FiniteSystem (α : Type u) [Mul α] where
  admissible : α → Prop
  pairs : α → Finset (α × α)
  mem_pairs :
    ∀ {x a b}, (a, b) ∈ pairs x ↔ a * b = x ∧ admissible x

namespace FiniteSystem

variable {α : Type u} [Mul α]
variable (S : FiniteSystem α)

/-- Convolution over ordered two-factor decompositions. -/
def convolution {R : Type v} [Semiring R]
    (f g : α → R) (x : α) : R :=
  ∑ ab ∈ S.pairs x, f ab.1 * g ab.2

theorem convolution_eq_sum_factorizations
    {R : Type v} [Semiring R]
    (f g : α → R) {x : α}
    (hx : S.admissible x) :
    S.convolution f g x =
      ∑ ab ∈ S.pairs x, f ab.1 * g ab.2 := by
  rfl

theorem pair_product
    {x a b : α}
    (h : (a, b) ∈ S.pairs x) :
    a * b = x :=
  (S.mem_pairs.mp h).1

end FiniteSystem

/-- Natural numbers with nonzero target and their divisor antidiagonal form
the standard finite factorization system. -/
def natSystem : FiniteSystem ℕ where
  admissible n := n ≠ 0
  pairs n := n.divisorsAntidiagonal
  mem_pairs := by
    intro n a b
    exact Nat.mem_divisorsAntidiagonal

@[simp] theorem natSystem_pairs (n : ℕ) :
    natSystem.pairs n = n.divisorsAntidiagonal :=
  rfl

/-- Dirichlet convolution is exactly factorization convolution on natural
numbers. -/
theorem nat_convolution_eq_dirichlet
    {R : Type v} [Semiring R]
    (f g : ArithmeticFunction R) (n : ℕ) :
    natSystem.convolution f g n = (f * g) n := by
  rfl

/-- Explicit factorization-sum form of Dirichlet convolution. -/
theorem dirichlet_eq_factorization_sum
    {R : Type v} [Semiring R]
    (f g : ArithmeticFunction R) (n : ℕ) :
    (f * g) n =
      ∑ ab ∈ natSystem.pairs n, f ab.1 * g ab.2 := by
  rfl

end FactorizationConvolution
end CausalGeometry
