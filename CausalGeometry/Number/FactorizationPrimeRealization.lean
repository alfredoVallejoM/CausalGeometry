import CausalGeometry.Number.ArithmeticShadow
import CausalGeometry.Number.Factorization
import CausalGeometry.Number.NatShadow

namespace CausalGeometry

universe u

namespace CausalFactorization

open CausalPrime

variable {α : Type u} [Monoid α]

/-- A classical prime labeling of one concrete atomic causal factorization.
The factorization exists first; the prime labels are realization data. -/
structure PrimeRealization
    (xs : List α) (x : α) (S : NatShadow α) where
  factorization : IsAtomicFactorization xs x
  primeOf : α → Nat.Primes
  factor_shadow :
    ∀ p, p ∈ xs → S p = (primeOf p).1

namespace PrimeRealization

variable {xs : List α} {x : α} {S : NatShadow α}
variable (R : PrimeRealization xs x S)

/-- Prime profile obtained only after forgetting the ordering of the realized
atomic causal factorization. -/
def primeProfile : PrimeProfile :=
  PrimeProfile.fromFactorList R.primeOf xs

/-- Product of the classical prime labels along the original ordered causal
factorization. -/
def primeWordValue : ℕ :=
  (xs.map (fun p => (R.primeOf p).1)).prod

/-- The multiplicative shadow of a causal factorization is the product of the
shadows of its ordered factors. -/
theorem shadow_eval :
    S (eval xs) = (xs.map S).prod := by
  induction xs with
  | nil =>
      simp [eval, S.map_one]
  | cons p ps ih =>
      simp [eval, S.map_mul, ih]

/-- Once every atomic factor is realized by its classical prime, the shadow of
the represented causal number is exactly the corresponding prime word
product. -/
theorem shadow_eq_primeWordValue :
    S x = R.primeWordValue := by
  have heval : eval xs = x := R.factorization.1
  calc
    S x = S (eval xs) := congrArg S heval.symm
    _ = (xs.map S).prod := R.shadow_eval
    _ = (xs.map (fun p => (R.primeOf p).1)).prod := by
      apply List.prod_congr
      intro p hp
      exact R.factor_shadow p hp
    _ = R.primeWordValue := rfl

/-- The prime profile is therefore explicitly downstream of the causal
factorization and its prime realization. -/
theorem primeProfile_is_derived :
    R.primeProfile =
      PrimeProfile.fromFactorList R.primeOf xs :=
  rfl

/-- The classical value of the derived prime profile equals the multiplicative
shadow of the causal number represented by the factorization. -/
theorem primeProfile_value_eq_shadow :
    PrimeProfile.value R.primeProfile = S x := by
  rw [R.primeProfile_is_derived, PrimeProfile.value_fromFactorList]
  exact R.shadow_eq_primeWordValue.symm

end PrimeRealization
end CausalFactorization
end CausalGeometry
