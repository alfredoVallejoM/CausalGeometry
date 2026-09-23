import CausalGeometry.Number.FactorizationProfile

namespace CausalGeometry

universe u

namespace CausalFactorization

variable {α : Type u} [CommMonoid α] [DecidableEq α]

/-- A causal arithmetic domain with a canonical atomic factorization profile.

The chosen list is only a producer.  The uniqueness law says every atomic
factorization of the same causal number has the same multiplicity profile, so
all arithmetic consequences below depend on the intrinsic profile rather than
on the chosen ordering. -/
structure CanonicalAtomicDomain where
  factors : α → List α
  factors_spec : ∀ x, IsAtomicFactorization (factors x) x
  profile_unique :
    ∀ {x : α} {xs : List α},
      IsAtomicFactorization xs x →
      profile xs = profile (factors x)

namespace CanonicalAtomicDomain

variable (D : CanonicalAtomicDomain (α := α))

/-- Intrinsic multiplicity profile extracted from canonical atomic
factorization. -/
def canonicalProfile (x : α) : α →₀ ℕ :=
  profile (D.factors x)

/-- Intrinsic valuation/multiplicity of a causal atom. -/
def valuation (p x : α) : ℕ :=
  D.canonicalProfile x p

theorem profile_of_atomicFactorization
    {x : α} {xs : List α}
    (h : IsAtomicFactorization xs x) :
    profile xs = D.canonicalProfile x := by
  exact D.profile_unique h

/-- The intrinsic profile is multiplicative-additive: composition of causal
numbers adds atomic multiplicities. -/
theorem canonicalProfile_mul (x y : α) :
    D.canonicalProfile (x * y) =
      D.canonicalProfile x + D.canonicalProfile y := by
  have hxy :
      IsAtomicFactorization
        (D.factors x ++ D.factors y) (x * y) :=
    atomicFactorization_append (D.factors_spec x) (D.factors_spec y)
  calc
    D.canonicalProfile (x * y)
        = profile (D.factors x ++ D.factors y) :=
      (D.profile_unique hxy).symm
    _ = profile (D.factors x) + profile (D.factors y) :=
      profile_append _ _
    _ = D.canonicalProfile x + D.canonicalProfile y := rfl

/-- Valuation additivity is derived from uniqueness of the causal atomic
profile; it is not an independent axiom. -/
theorem valuation_mul (p x y : α) :
    D.valuation p (x * y) =
      D.valuation p x + D.valuation p y := by
  change D.canonicalProfile (x * y) p =
    D.canonicalProfile x p + D.canonicalProfile y p
  rw [D.canonicalProfile_mul]
  rfl

/-- Any atom not occurring in the intrinsic profile has valuation zero. -/
theorem valuation_eq_zero_of_not_mem_support
    {p x : α}
    (h : p ∉ (D.canonicalProfile x).support) :
    D.valuation p x = 0 := by
  exact Finsupp.notMem_support_iff.mp h

/-- Positive valuation is equivalent to membership in the finite primary
support. -/
theorem valuation_pos_iff_mem_support
    {p x : α} :
    0 < D.valuation p x ↔
      p ∈ (D.canonicalProfile x).support := by
  rw [Finsupp.mem_support_iff]
  exact Nat.pos_iff_ne_zero

end CanonicalAtomicDomain
end CausalFactorization
end CausalGeometry
