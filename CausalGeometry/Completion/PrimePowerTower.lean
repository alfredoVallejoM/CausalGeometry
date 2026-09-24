import CausalGeometry.Completion.FinitePrimaryTower
import Mathlib.Data.Nat.Prime.Basic

namespace CausalGeometry

namespace FiniteInverseTower

/-- Primary finite tower whose residue cardinal is explicitly a prime power
q = p^f. This separates the rational prime, residue degree and residue
cardinality instead of conflating them. -/
structure PrimePowerPrimary
    (T : FiniteInverseTower)
    extends T.Primary where
  p : ℕ
  f : ℕ
  p_prime : p.Prime
  f_pos : 0 < f
  q_eq : q = p ^ f

namespace PrimePowerPrimary

variable {T : FiniteInverseTower}
variable (P : T.PrimePowerPrimary)

theorem p_ge_two : 2 ≤ P.p :=
  P.p_prime.two_le

theorem q_eq_primePower :
    P.toPrimary.q = P.p ^ P.f :=
  P.q_eq

/-- Level cardinality written directly in terms of p and the residue degree f. -/
theorem card_law_primePower (n : ℕ) :
    T.card n = P.p ^ (P.f * (n + 1)) := by
  calc
    T.card n = P.toPrimary.q ^ (n + 1) :=
      P.toPrimary.card_law n
    _ = (P.p ^ P.f) ^ (n + 1) := by
      rw [P.q_eq]
    _ = P.p ^ (P.f * (n + 1)) := by
      rw [pow_mul]

/-- The residue cardinal is at least two. -/
theorem q_ge_two :
    2 ≤ P.toPrimary.q :=
  P.toPrimary.q_ge_two

end PrimePowerPrimary
end FiniteInverseTower
end CausalGeometry
