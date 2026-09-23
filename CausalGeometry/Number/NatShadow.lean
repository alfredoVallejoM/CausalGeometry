import CausalGeometry.Number.Divisibility

namespace CausalGeometry

universe u

/-- A multiplicative classical natural-number shadow of a causal arithmetic
domain.  It deliberately records only what is preserved. -/
structure NatShadow (α : Type u) [Monoid α] where
  toNat : α → ℕ
  map_one : toNat 1 = 1
  map_mul : ∀ x y, toNat (x * y) = toNat x * toNat y

namespace NatShadow

open CausalDivisibility

variable {α : Type u} [Monoid α]

instance : CoeFun (NatShadow α) (fun _ => α → ℕ) :=
  ⟨NatShadow.toNat⟩

@[simp] theorem one (S : NatShadow α) :
    S (1 : α) = 1 :=
  S.map_one

@[simp] theorem mul (S : NatShadow α) (x y : α) :
    S (x * y) = S x * S y :=
  S.map_mul x y

theorem leftDivides_sound (S : NatShadow α) {x z : α}
    (h : LeftDivides x z) :
    S x ∣ S z := by
  rcases h with ⟨y, hy⟩
  refine ⟨S y, ?_⟩
  calc
    S z = S (x * y) := congrArg S hy.symm
    _ = S x * S y := S.map_mul x y

theorem rightDivides_sound (S : NatShadow α) {x z : α}
    (h : RightDivides x z) :
    S x ∣ S z := by
  rcases h with ⟨y, hy⟩
  refine ⟨S y, ?_⟩
  calc
    S z = S (y * x) := congrArg S hy.symm
    _ = S y * S x := S.map_mul y x
    _ = S x * S y := Nat.mul_comm _ _

theorem pow (S : NatShadow α) (x : α) (n : ℕ) :
    S (x ^ n) = S x ^ n := by
  induction n with
  | zero =>
      simp [S.map_one]
  | succ n ih =>
      rw [pow_succ, S.map_mul, ih, pow_succ]

theorem causalUnit_maps_one (S : NatShadow α) {x : α}
    (hx : IsCausalUnit x) :
    S x = 1 := by
  rcases hx with ⟨y, hxy, hyx⟩
  have hprod : S x * S y = 1 := by
    calc
      S x * S y = S (x * y) := (S.map_mul x y).symm
      _ = S 1 := congrArg S hxy
      _ = 1 := S.map_one
  exact (Nat.mul_eq_one.mp hprod).1

theorem powerLeftDivides_sound (S : NatShadow α)
    {p x : α} {r : ℕ}
    (h : LeftDivides (p ^ r) x) :
    S p ^ r ∣ S x := by
  have hdiv : S (p ^ r) ∣ S x :=
    S.leftDivides_sound h
  simpa [S.pow p r] using hdiv

end NatShadow
end CausalGeometry
