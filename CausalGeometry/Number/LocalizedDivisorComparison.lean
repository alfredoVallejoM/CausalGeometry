import CausalGeometry.Number.CanonicalAtomicDomain
import CausalGeometry.Number.LocalizedValuation
import CausalGeometry.Number.CommutativeLocalizationMonoid
import CausalGeometry.Number.Incidence

namespace CausalGeometry

universe u

namespace CausalFactorization
namespace CanonicalAtomicDomain

variable
    {α : Type u}
    [CancelCommMonoid α]
    [DecidableEq α]
    (D : CanonicalAtomicDomain (α := α))

/-- Divisibility in the source can only increase every intrinsic atomic
multiplicity. -/
theorem valuation_le_of_leftDivides
    {x z : α}
    (h : CausalDivisibility.LeftDivides x z)
    (p : α) :
    D.valuation p x ≤ D.valuation p z := by
  rcases h with ⟨y, rfl⟩
  rw [D.valuation_mul]
  exact Nat.le_add_right _ _

/-- In the commutative source the same statement holds for right divisibility. -/
theorem valuation_le_of_rightDivides
    {x z : α}
    (h : CausalDivisibility.RightDivides x z)
    (p : α) :
    D.valuation p x ≤ D.valuation p z := by
  rcases h with ⟨y, rfl⟩
  rw [mul_comm]
  rw [D.valuation_mul]
  exact Nat.le_add_right _ _

/-- Pointwise profile order induced by intrinsic atomic multiplicities. -/
def ProfileLE
    (x z : α) : Prop :=
  ∀ p : α,
    D.valuation p x ≤ D.valuation p z

theorem leftDivides_profileLE
    {x z : α}
    (h : CausalDivisibility.LeftDivides x z) :
    D.ProfileLE x z :=
  fun p => D.valuation_le_of_leftDivides h p

theorem rightDivides_profileLE
    {x z : α}
    (h : CausalDivisibility.RightDivides x z) :
    D.ProfileLE x z :=
  fun p => D.valuation_le_of_rightDivides h p

/-- A source divisibility witness gives the exact nonnegative valuation
increment. -/
theorem valuation_increment_of_leftDivides
    {x z : α}
    (h : CausalDivisibility.LeftDivides x z) :
    ∃ y : α,
      x * y = z ∧
      ∀ p : α,
        D.valuation p z =
          D.valuation p x +
            D.valuation p y := by
  rcases h with ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  intro p
  rw [← hy]
  exact D.valuation_mul p x y

end CanonicalAtomicDomain
end CausalFactorization

namespace CausalLocalization

open CausalFactorization

variable
    {α : Type u}
    [CancelCommMonoid α]
    [DecidableEq α]
    {S : Submonoid α}

/-- The source embedding into commutative localization preserves causal
divisibility. -/
theorem commFraction_ofElement_preserves_leftDivides
    {x z : α}
    (h : CausalDivisibility.LeftDivides x z) :
    CausalDivisibility.LeftDivides
      (CommFraction.ofElement (S := S) x)
      (CommFraction.ofElement (S := S) z) := by
  rcases h with ⟨y, rfl⟩
  refine
    ⟨CommFraction.ofElement (S := S) y, ?_⟩
  exact CommFraction.ofElement_mul x y

/-- Symmetrically for right divisibility. -/
theorem commFraction_ofElement_preserves_rightDivides
    {x z : α}
    (h : CausalDivisibility.RightDivides x z) :
    CausalDivisibility.RightDivides
      (CommFraction.ofElement (S := S) x)
      (CommFraction.ofElement (S := S) z) := by
  rcases h with ⟨y, rfl⟩
  refine
    ⟨CommFraction.ofElement (S := S) y, ?_⟩
  rw [mul_comm]
  exact CommFraction.ofElement_mul x y

namespace LocalizedDivisorComparison

variable
    (D : CanonicalAtomicDomain (α := α))

/-- Signed localized p-depth. -/
def depth
    (p : α) :
    CommFraction S → ℤ :=
  (D.integerValuation p).fractionValue

@[simp] theorem depth_source
    (p x : α) :
    depth (S := S) D p
        (CommFraction.ofElement
          (S := S) x)
      =
    Int.ofNat (D.valuation p x) := by
  exact
    CausalLocalization.MultiplicativeZValuation
      .fractionValue_ofElement
        (D.integerValuation p) x

@[simp] theorem depth_denominatorInverse
    (p : α)
    (s : S) :
    depth (S := S) D p
        (CommFraction.denominatorInverse s)
      =
    - Int.ofNat
        (D.valuation p (s : α)) := by
  exact
    D.localizedIntegerValuation_denominatorInverse
      p s

/-- A source divisibility witness becomes a nonnegative signed displacement in
every localized atomic depth. -/
theorem depth_difference_of_leftDivides
    {x z : α}
    (h : CausalDivisibility.LeftDivides x z)
    (p : α) :
    0 ≤
      depth (S := S) D p
          (CommFraction.ofElement
            (S := S) z)
        -
      depth (S := S) D p
          (CommFraction.ofElement
            (S := S) x) := by

  rw [depth_source, depth_source]

  exact
    Int.ofNat_le.mpr
      (D.valuation_le_of_leftDivides h p)

/-- More strongly, the signed localized displacement is exactly the valuation
of the source quotient witness. -/
theorem depth_difference_eq_quotient
    {x z : α}
    (h : CausalDivisibility.LeftDivides x z)
    (p : α) :
    ∃ y : α,
      x * y = z ∧
      depth (S := S) D p
          (CommFraction.ofElement
            (S := S) z)
        -
      depth (S := S) D p
          (CommFraction.ofElement
            (S := S) x)
      =
      Int.ofNat (D.valuation p y) := by

  rcases h with ⟨y, hy⟩

  refine ⟨y, hy, ?_⟩

  rw [depth_source, depth_source]

  rw [← hy, D.valuation_mul]

  omega

/-- Localization extends the positive source divisor profile to signed depths:
inverting a selected denominator reverses all of its atomic multiplicities. -/
theorem depth_source_mul_denominatorInverse
    (p x : α)
    (s : S) :
    depth (S := S) D p
      (CommFraction.ofElement
          (S := S) x *
        CommFraction.denominatorInverse s)
      =
    Int.ofNat (D.valuation p x) -
      Int.ofNat (D.valuation p (s : α)) := by

  rw [
    CausalLocalization.MultiplicativeZValuation
      .fractionValue_mul,
    depth_source,
    depth_denominatorInverse
  ]

  ring

/-- Hence the localized signed-depth geometry is not the same as the positive
source incidence order whenever an inverted denominator has positive
p-valuation. -/
theorem denominatorInverse_has_negative_depth
    (p : α)
    (s : S)
    (hpos :
      0 < D.valuation p (s : α)) :
    depth (S := S) D p
        (CommFraction.denominatorInverse s)
      <
    0 := by

  rw [depth_denominatorInverse]

  exact
    neg_neg_of_pos
      (Int.ofNat_pos.mpr hpos)

end LocalizedDivisorComparison
end CausalLocalization
end CausalGeometry
