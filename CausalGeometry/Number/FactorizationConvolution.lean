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

/-- Arithmetic functions on a finite causal factorization system.  Values must
vanish outside the system's admissible domain. -/
structure CausalArithmeticFunction
    {α : Type u} [Mul α]
    (S : FiniteSystem α)
    (R : Type v) [Zero R] where
  toFun : α → R
  map_nonadmissible :
    ∀ x, ¬ S.admissible x → toFun x = 0

namespace CausalArithmeticFunction

variable {α : Type u} [Mul α]
variable {S : FiniteSystem α}
variable {R : Type v} [Zero R]

instance : CoeFun (CausalArithmeticFunction S R)
    (fun _ => α → R) :=
  ⟨CausalArithmeticFunction.toFun⟩

@[ext] theorem ext
    {f g : CausalArithmeticFunction S R}
    (h : ∀ x, f x = g x) :
    f = g := by
  cases f
  cases g
  simp_all

/-- Factorization convolution closes on causal arithmetic functions because a
nonadmissible target has no admitted factorization pairs. -/
def convolution [Semiring R]
    (f g : CausalArithmeticFunction S R) :
    CausalArithmeticFunction S R where
  toFun := S.convolution f g
  map_nonadmissible := by
    intro x hx
    have hempty : S.pairs x = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro ab hab
      exact hx ((S.mem_pairs.mp hab).2)
    simp [FiniteSystem.convolution, hempty]

@[simp] theorem convolution_apply [Semiring R]
    (f g : CausalArithmeticFunction S R) (x : α) :
    convolution f g x =
      ∑ ab ∈ S.pairs x, f ab.1 * g ab.2 :=
  rfl

end CausalArithmeticFunction

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

/-- Causal arithmetic functions for the natural factorization system are
exactly ordinary ArithmeticFunction objects. -/
def natArithmeticFunctionEquiv
    {R : Type v} [Zero R] :
    CausalArithmeticFunction natSystem R ≃
      ArithmeticFunction R where
  toFun f :=
    { toFun := f
      map_zero' := f.map_nonadmissible 0 (by simp [natSystem]) }
  invFun f :=
    { toFun := f
      map_nonadmissible := by
        intro n hn
        have hn0 : n = 0 := by
          by_contra hne
          exact hn hne
        subst n
        exact f.map_zero }
  left_inv f := by
    apply CausalArithmeticFunction.ext
    intro n
    rfl
  right_inv f := by
    apply ArithmeticFunction.ext
    intro n
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

/-- The bundled causal convolution is transported exactly to Dirichlet
convolution under the natural-number equivalence. -/
theorem natArithmeticFunctionEquiv_convolution
    {R : Type v} [Semiring R]
    (f g : CausalArithmeticFunction natSystem R) :
    natArithmeticFunctionEquiv
        (CausalArithmeticFunction.convolution f g) =
      natArithmeticFunctionEquiv f *
        natArithmeticFunctionEquiv g := by
  apply ArithmeticFunction.ext
  intro n
  rfl

end FactorizationConvolution
end CausalGeometry
