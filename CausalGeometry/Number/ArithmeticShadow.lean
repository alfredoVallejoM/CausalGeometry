import CausalGeometry.Number.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace CausalGeometry

/-- Finitely supported prime profile: the commutative arithmetic shadow. -/
structure PrimeProfile where
  exponents : Nat.Primes →₀ ℕ

namespace PrimeProfile

/-- Classical positive integer recovered from a finite prime profile. -/
def value (ν : PrimeProfile) : ℕ :=
  ν.exponents.prod fun p e => p.1 ^ e

@[simp] theorem value_zero : value ⟨0⟩ = 1 := by
  simp [value]

end PrimeProfile

end CausalGeometry
