import CausalGeometry.Cyclic.PrimitiveConjugacy
import CausalGeometry.Cyclic.PrimitiveTrace

namespace CausalGeometry

universe g

namespace PrimitiveConjugacy

variable {Γ : Type g} [Group Γ]

/-- Translation-length spectrum on conjugacy classes.

The length is defined on the conjugacy class itself, so conjugacy invariance is
built into the type rather than reproved at every use. -/
structure Spectrum where
  translationLength :
    ConjClasses Γ → ℕ

  positive_of_primitive :
    ∀ C,
      IsPrimitiveClass C →
        0 < translationLength C

  finiteLevel :
    ∀ n,
      Finite
        {C : ConjClasses Γ //
          IsPrimitiveClass C ∧
            translationLength C = n}

namespace Spectrum

variable (S : Spectrum (Γ := Γ))

/-- Primitive conjugacy classes of exact translation length n. -/
abbrev Level (n : ℕ) :=
  {C : ConjClasses Γ //
    IsPrimitiveClass C ∧
      S.translationLength C = n}

/-- Number of primitive conjugacy classes at exact length n. -/
noncomputable def count (n : ℕ) : ℕ := by
  letI : Finite (S.Level n) :=
    S.finiteLevel n
  exact Nat.card (S.Level n)

theorem count_zero :
    S.count 0 = 0 := by
  classical
  letI : Finite (S.Level 0) :=
    S.finiteLevel 0
  apply Nat.card_eq_zero.mpr
  intro hnonempty
  rcases hnonempty with ⟨C⟩
  exact
    (Nat.not_lt_zero _
      (S.positive_of_primitive C.1 C.2.1))
    (C.2.2 ▸ Nat.lt_add_one_iff.mpr
      (Nat.zero_le 0))

end Spectrum
end PrimitiveConjugacy

/-- Certified identification between a primitive Hashimoto trace spectrum and
primitive conjugacy classes in a deck group. -/
structure PrimitiveTraceConjugacyComparison
    {Γ : Type g} [Group Γ]
    (P : PrimitiveTraceCounts) where

  spectrum :
    PrimitiveConjugacy.Spectrum (Γ := Γ)

  count_matches :
    ∀ n,
      P.primitive n =
        (spectrum.count n : ℤ)

namespace PrimitiveTraceConjugacyComparison

variable
    {Γ : Type g} [Group Γ]
    {P : PrimitiveTraceCounts}
    (C : PrimitiveTraceConjugacyComparison
      (Γ := Γ) P)

theorem primitive_nonnegative
    (n : ℕ) :
    0 ≤ P.primitive n := by
  rw [C.count_matches n]
  exact Int.natCast_nonneg _

theorem primitive_zero :
    P.primitive 0 = 0 := by
  rw [C.count_matches 0,
    C.spectrum.count_zero]
  rfl

/-- Primitive trace multiplicity is exactly the finite cardinality of the
corresponding primitive conjugacy spectrum. -/
theorem primitive_eq_natCard
    (n : ℕ) :
    P.primitive n =
      (Nat.card
        (C.spectrum.Level n) : ℤ) := by
  simpa [PrimitiveConjugacy.Spectrum.count] using
    C.count_matches n

end PrimitiveTraceConjugacyComparison
end CausalGeometry
