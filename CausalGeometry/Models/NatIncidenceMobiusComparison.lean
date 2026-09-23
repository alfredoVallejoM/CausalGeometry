import CausalGeometry.Models.NatDivisorIncidence
import CausalGeometry.Models.NatMobiusRegression
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

namespace CausalGeometry

namespace NatIncidenceMobiusComparison

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Classical Mobius sums to the delta function over the divisors of a natural
number. -/
theorem sum_moebius_divisors (m : ℕ) :
    (∑ d ∈ m.divisors, μ d) =
      if m = 1 then 1 else 0 := by
  calc
    (∑ d ∈ m.divisors, μ d) =
        (μ * ζ : ArithmeticFunction ℤ) m := by
      symm
      exact ArithmeticFunction.coe_mul_zeta_apply
    _ = (1 : ArithmeticFunction ℤ) m := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = if m = 1 then 1 else 0 := rfl

/-- Summing classical Mobius over a causal lower divisor interval is the same
as summing it over the ordinary divisor finset. -/
theorem sum_Iic_eq_sum_divisors
    (n : ℕ) [NeZero n]
    (x : NatDivisorIncidence.Divisor n) :
    (∑ d ∈ Finset.Iic x, μ d.1) =
      ∑ m ∈ x.1.divisors, μ m := by
  rw [← NatDivisorIncidence.map_Iic_val n x]
  simp

/-- The incidence Mobius function of the finite causal divisor poset agrees
exactly with the classical arithmetic Mobius function when measured from the
unit divisor. -/
theorem mobius_from_bot_eq_arithmetic
    (n : ℕ) [NeZero n]
    (x : NatDivisorIncidence.Divisor n) :
    NatDivisorIncidence.mobius n
        (⊥ : NatDivisorIncidence.Divisor n) x =
      μ x.1 := by
  let f : NatDivisorIncidence.Divisor n → ℤ :=
    fun d => μ d.1
  let g : NatDivisorIncidence.Divisor n → ℤ :=
    fun d => if d = ⊥ then 1 else 0
  have hg :
      ∀ d, g d = ∑ e ∈ Finset.Iic d, f e := by
    intro d
    rw [show (∑ e ∈ Finset.Iic d, f e) =
        ∑ m ∈ d.1.divisors, μ m by
      simpa [f] using sum_Iic_eq_sum_divisors n d]
    rw [sum_moebius_divisors]
    by_cases hd : d = (⊥ : NatDivisorIncidence.Divisor n)
    · subst d
      simp [g]
    · have hd1 : d.1 ≠ 1 := by
        intro hval
        apply hd
        apply Subtype.ext
        simpa using hval
      simp [g, hd, hd1]
  have hinv :=
    (NatDivisorIncidence.presentation n).moebius_inversion
      f g hg x
  have hbot :
      (⊥ : NatDivisorIncidence.Divisor n) ∈
        Finset.Iic x :=
    Finset.mem_Iic.mpr bot_le
  have hsingle :
      (∑ y ∈ Finset.Iic x,
          (NatDivisorIncidence.presentation n).mobius y x *
            g y) =
        (NatDivisorIncidence.presentation n).mobius
          (⊥ : NatDivisorIncidence.Divisor n) x := by
    rw [Finset.sum_eq_single (⊥ : NatDivisorIncidence.Divisor n)]
    · simp [g]
    · intro b hb hne
      simp [g, hne]
    · intro hnot
      exact (hnot hbot).elim
  change
    (NatDivisorIncidence.presentation n).mobius
        (⊥ : NatDivisorIncidence.Divisor n) x =
      μ x.1
  symm
  calc
    μ x.1 = f x := rfl
    _ = ∑ y ∈ Finset.Iic x,
          (NatDivisorIncidence.presentation n).mobius y x *
            g y := hinv
    _ = (NatDivisorIncidence.presentation n).mobius
          (⊥ : NatDivisorIncidence.Divisor n) x := hsingle

/-- The Euler characteristic of the finite divisor poset is the classical
Mobius value of n. -/
theorem eulerChar_divisorPoset_eq_moebius
    (n : ℕ) [NeZero n] :
    IncidenceAlgebra.eulerChar ℤ
        (NatDivisorIncidence.Divisor n) =
      μ n := by
  change
    NatDivisorIncidence.mobius n
        (⊥ : NatDivisorIncidence.Divisor n)
        (⊤ : NatDivisorIncidence.Divisor n) =
      μ n
  simpa using
    mobius_from_bot_eq_arithmetic n
      (⊤ : NatDivisorIncidence.Divisor n)

end NatIncidenceMobiusComparison
end CausalGeometry
