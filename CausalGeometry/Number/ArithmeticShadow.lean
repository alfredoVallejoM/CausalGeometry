import CausalGeometry.Number.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace CausalGeometry

/-- Finitely supported classical prime profile.  It is an arithmetic shadow,
not a primitive field of a causal number. -/
structure PrimeProfile where
  exponents : Nat.Primes →₀ ℕ

namespace PrimeProfile

instance : Zero PrimeProfile where
  zero := ⟨0⟩

instance : Add PrimeProfile where
  add a b := ⟨a.exponents + b.exponents⟩

@[ext] theorem ext {a b : PrimeProfile}
    (h : a.exponents = b.exponents) : a = b := by
  cases a
  cases b
  simp_all

@[simp] theorem zero_exponents :
    (0 : PrimeProfile).exponents = 0 := rfl

@[simp] theorem add_exponents (a b : PrimeProfile) :
    (a + b).exponents = a.exponents + b.exponents := rfl

/-- Classical positive integer recovered from a finite prime profile. -/
def value (ν : PrimeProfile) : ℕ :=
  ν.exponents.prod fun p e => p.1 ^ e

@[simp] theorem value_zero : value 0 = 1 := by
  simp [value]

/-- One classical prime occurrence. -/
def atom (p : Nat.Primes) : PrimeProfile :=
  ⟨Finsupp.single p 1⟩

@[simp] theorem atom_exponents (p : Nat.Primes) :
    (atom p).exponents = Finsupp.single p 1 := rfl

/-- Derive a classical prime profile from an ordered list of causal factors
once a target realization has assigned each factor a classical prime.  The
factor order is forgotten explicitly at this step. -/
def fromFactorList {α : Type*}
    (primeOf : α → Nat.Primes) : List α → PrimeProfile
  | [] => 0
  | x :: xs => atom (primeOf x) + fromFactorList primeOf xs

@[simp] theorem fromFactorList_nil {α : Type*}
    (primeOf : α → Nat.Primes) :
    fromFactorList primeOf [] = 0 := rfl

@[simp] theorem fromFactorList_cons {α : Type*}
    (primeOf : α → Nat.Primes) (x : α) (xs : List α) :
    fromFactorList primeOf (x :: xs) =
      atom (primeOf x) + fromFactorList primeOf xs := rfl

theorem fromFactorList_append {α : Type*}
    (primeOf : α → Nat.Primes) (xs ys : List α) :
    fromFactorList primeOf (xs ++ ys) =
      fromFactorList primeOf xs + fromFactorList primeOf ys := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.cons_append, fromFactorList_cons, ih]
      apply PrimeProfile.ext
      simp [add_assoc]

end PrimeProfile
end CausalGeometry
