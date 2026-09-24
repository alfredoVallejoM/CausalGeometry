import CausalGeometry.Completion.LocalProjectiveCharts
import CausalGeometry.Completion.ZModLocalTower
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace CausalGeometry

namespace zmodPrimeLocalTower

open LocalProjectivePair

variable (p : ℕ) [Fact p.Prime]

/-- The non-units modulo p^(n+1) are exactly p^n in number. -/
theorem nonunit_natCard (n : ℕ) :
    Nat.card
        (LocalProjectivePair.Nonunit
          (ZMod (p ^ (n + 1)))) =
      p ^ n := by
  letI : NeZero (p ^ (n + 1)) :=
    levelNeZero p n
  rw [LocalProjectivePair.natCard_nonunit]
  rw [ZMod.card]
  rw [Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]
  rw [Nat.totient_prime_pow_succ
    (Fact.out : Nat.Prime p) n]
  rw [pow_succ]
  rw [← Nat.mul_sub_left_distrib]
  rw [Nat.sub_sub_cancel
    (Fact.out : Nat.Prime p).one_le]
  simp

/-- Exact projective sphere cardinal:
|P¹(Z/p^(n+1)Z)| = (p+1) p^n. -/
theorem projectiveLine_natCard (n : ℕ) :
    Nat.card
        (LocalProjectivePair.Line
          (ZMod (p ^ (n + 1)))) =
      (p + 1) * p ^ n := by
  letI : NeZero (p ^ (n + 1)) :=
    levelNeZero p n
  calc
    Nat.card
        (LocalProjectivePair.Line
          (ZMod (p ^ (n + 1))))
        =
      Fintype.card (ZMod (p ^ (n + 1))) +
        Nat.card
          (LocalProjectivePair.Nonunit
            (ZMod (p ^ (n + 1)))) :=
      LocalProjectivePair.natCard_line
    _ = p ^ (n + 1) + p ^ n := by
      rw [ZMod.card, nonunit_natCard p n]
    _ = (p + 1) * p ^ n := by
      rw [pow_succ]
      ring

/-- The concrete local projective tower satisfies the sphere-cardinality half
of the Bruhat--Tits branching contract. -/
theorem projectiveLine_card_contract (n : ℕ) :
    Nat.card
        (LocalProjectivePair.Line
          (ZMod (p ^ (n + 1)))) =
      ((primePowerTower p).q + 1) *
        (primePowerTower p).q ^ n := by
  rw [primePowerTower_q]
  exact projectiveLine_natCard p n

end zmodPrimeLocalTower
end CausalGeometry
