import CausalGeometry.Number.FactorizationPrimeRealization
import Mathlib.Data.Nat.Factors

namespace CausalGeometry

namespace NatArithmeticModel

open CausalDivisibility CausalFactorization CausalPrime

/-- In the multiplicative monoid of natural numbers, the causal units are
exactly one. -/
theorem isCausalUnit_iff (n : ℕ) :
    IsCausalUnit n ↔ n = 1 := by
  constructor
  · rintro ⟨m, hnm, hmn⟩
    exact (Nat.mul_eq_one.mp hnm).1
  · rintro rfl
    exact one_isCausalUnit

/-- Every classical natural prime is compositionally irreducible in the causal
multiplicative sense. -/
theorem prime_irreducible {p : ℕ} (hp : p.Prime) :
    Irreducible p := by
  constructor
  · intro hu
    exact hp.ne_one ((isCausalUnit_iff p).mp hu)
  · intro a b hab
    have ha : a ∣ p := ⟨b, hab⟩
    rcases hp.eq_one_or_self_of_dvd a ha with ha1 | hap
    · exact Or.inl ((isCausalUnit_iff a).mpr ha1)
    · right
      apply (isCausalUnit_iff b).mpr
      subst a
      apply Nat.mul_left_cancel hp.pos
      simpa using hab

/-- In natural-number multiplication, causal irreducibility is exactly
classical primality. -/
theorem irreducible_iff_prime (n : ℕ) :
    Irreducible n ↔ n.Prime := by
  constructor
  · intro hn
    have hn1 : n ≠ 1 := by
      intro h1
      apply hn.1
      exact (isCausalUnit_iff n).mpr h1
    have hn0 : n ≠ 0 := by
      intro h0
      subst n
      have hfac := hn.2 0 0 (by simp)
      rcases hfac with hu | hu
      · exact zero_ne_one ((isCausalUnit_iff 0).mp hu)
      · exact zero_ne_one ((isCausalUnit_iff 0).mp hu)
    apply Nat.prime_def.mpr
    constructor
    · exact (Nat.two_le_iff n).mpr ⟨hn0, hn1⟩
    · intro m hm
      rcases hm with ⟨k, hk⟩
      rcases hn.2 m k hk.symm with hmUnit | hkUnit
      · exact Or.inl ((isCausalUnit_iff m).mp hmUnit)
      · right
        have hk1 : k = 1 := (isCausalUnit_iff k).mp hkUnit
        simpa [hk1] using hk.symm
  · exact prime_irreducible

/-- The identity multiplicative shadow on natural numbers. -/
def natShadow : NatShadow ℕ where
  toNat := id
  map_one := rfl
  map_mul := by
    intro x y
    rfl

@[simp] theorem natShadow_apply (n : ℕ) :
    natShadow n = n := rfl

/-- Turn every natural into a prime label when it is prime; outside primes use
the fixed harmless default two. Only factors occurring in a certified atomic
factorization are consumed by the realization theorem. -/
def primeLabel (n : ℕ) : Nat.Primes :=
  if h : n.Prime then ⟨n, h⟩ else ⟨2, Nat.prime_two⟩

theorem primeLabel_of_prime {p : ℕ} (hp : p.Prime) :
    (primeLabel p).1 = p := by
  simp [primeLabel, hp]

/-- The ordinary list of prime factors is an ordered atomic causal
factorization of every nonzero natural number. -/
theorem primeFactors_atomicFactorization
    {n : ℕ} (hn : n ≠ 0) :
    IsAtomicFactorization n.primeFactorsList n := by
  constructor
  · unfold IsFactorization eval
    exact Nat.prod_primeFactorsList hn
  · intro p hp
    exact prime_irreducible (Nat.prime_of_mem_primeFactorsList hp)

/-- The classical prime factor list is therefore a concrete realization of the
generic causal factorization-to-prime-profile interface. -/
def primeFactorsRealization
    {n : ℕ} (hn : n ≠ 0) :
    CausalFactorization.PrimeRealization
      n.primeFactorsList n natShadow where
  factorization := primeFactors_atomicFactorization hn
  primeOf := primeLabel
  factor_shadow := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactorsList hp
    simp [natShadow, primeLabel, hprime]

/-- Classical prime multiplicity is the regression target for intrinsic causal
valuation. -/
def primeMultiplicity (p n : ℕ) : ℕ :=
  n.factorization p

theorem primeMultiplicity_mul
    (p a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    primeMultiplicity p (a * b) =
      primeMultiplicity p a + primeMultiplicity p b := by
  change (a * b).factorization p =
    a.factorization p + b.factorization p
  rw [Nat.factorization_mul ha hb]
  rfl

theorem primeMultiplicity_eq_factorList_count
    (p n : ℕ) :
    primeMultiplicity p n =
      n.primeFactorsList.count p := by
  exact (Nat.primeFactorsList_count_eq).symm

/-- The intrinsic causal multiplicity profile of the classical prime-factor
word is exactly the standard Nat.factorization finsupp. -/
theorem primeFactors_profile_eq_factorization (n : ℕ) :
    CausalFactorization.profile n.primeFactorsList =
      n.factorization := by
  ext p
  rw [CausalFactorization.profile_apply_eq_count]
  exact Nat.primeFactorsList_count_eq

/-- Regression theorem: the derived causal prime profile evaluates back to the
original natural number. -/
theorem derivedPrimeProfile_value
    {n : ℕ} (hn : n ≠ 0) :
    PrimeProfile.value
      (primeFactorsRealization hn).primeProfile = n := by
  simpa [natShadow] using
    (primeFactorsRealization hn).primeProfile_value_eq_shadow

end NatArithmeticModel
end CausalGeometry
