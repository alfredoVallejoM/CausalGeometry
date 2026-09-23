import CausalGeometry.Completion.ZModPrimeTower
import CausalGeometry.Models.NatIncidenceMobiusComparison
import CausalGeometry.Models.NatArithmetic
import CausalGeometry.Models.NatMobiusRegression

namespace CausalGeometry

namespace ArithmeticCoreControls

/-- Positive Mobius control: a prime divisor poset has Euler characteristic
minus one. -/
theorem divisorEulerChar_prime
    {p : ℕ} (hp : p.Prime) :
    IncidenceAlgebra.eulerChar ℤ
        (NatDivisorIncidence.Divisor p) = -1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  calc
    IncidenceAlgebra.eulerChar ℤ
        (NatDivisorIncidence.Divisor p) =
      ArithmeticFunction.moebius p :=
        NatIncidenceMobiusComparison.eulerChar_divisorPoset_eq_moebius p
    _ = -1 := ArithmeticFunction.moebius_apply_prime hp

/-- Mutation/control: repeating a prime changes the incidence Euler
characteristic from minus one to zero. -/
theorem divisorEulerChar_primeSquare
    {p : ℕ} (hp : p.Prime) :
    IncidenceAlgebra.eulerChar ℤ
        (NatDivisorIncidence.Divisor (p ^ 2)) = 0 := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  calc
    IncidenceAlgebra.eulerChar ℤ
        (NatDivisorIncidence.Divisor (p ^ 2)) =
      ArithmeticFunction.moebius (p ^ 2) :=
        NatIncidenceMobiusComparison.eulerChar_divisorPoset_eq_moebius (p ^ 2)
    _ = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp
        (Nat.succ_ne_zero 1)]
      simp

/-- Classical regression: causal irreducibility and natural primality agree. -/
theorem nat_irreducible_exactly_prime (n : ℕ) :
    CausalPrime.Irreducible n ↔ n.Prime :=
  NatArithmeticModel.irreducible_iff_prime n

/-- Classical regression: the causal multiplicity profile of the prime word
is exactly the standard natural-number factorization. -/
theorem nat_profile_exactly_factorization (n : ℕ) :
    CausalFactorization.profile n.primeFactorsList =
      n.factorization :=
  NatArithmeticModel.primeFactors_profile_eq_factorization n

/-- Finite p-adic control: depth n exposes exactly p^(n+1) causal states. -/
theorem padic_observation_count
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nat.card ((zmodPrimeTower p).TruncationQuotient n) =
      p ^ (n + 1) :=
  zmodPrimeTower.truncationQuotient_natCard p n

/-- Metric control: finite causal indistinguishability is exactly a p-adic
closed ball condition. -/
theorem padic_depth_is_ball
    (p : ℕ) [Fact p.Prime]
    (x y : ℤ_[p]) (n : ℕ) :
    (zmodPrimeTower p).AgreeThrough
        (zmodPrimeTower.ofPadicInt p x)
        (zmodPrimeTower.ofPadicInt p y) n ↔
      dist x y ≤
        (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) :=
  zmodPrimeTower.agreeThrough_ofPadicInt_iff_dist_le p x y n

end ArithmeticCoreControls
end CausalGeometry
