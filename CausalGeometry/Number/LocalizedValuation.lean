import CausalGeometry.Number.CanonicalAtomicDomain
import CausalGeometry.Number.CommutativeLocalizationMonoid
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace CausalLocalization

/-- Integer-valued multiplicative valuation data.

The multiplicative source is not required to be a field or a group.  The
valuation laws needed for localization are exactly v(1)=0 and
v(xy)=v(x)+v(y). -/
structure MultiplicativeZValuation
    (α : Type u)
    [Monoid α] where

  value : α → ℤ

  one_eq_zero :
    value 1 = 0

  mul_eq_add :
    ∀ x y,
      value (x * y) =
        value x + value y

namespace MultiplicativeZValuation

variable
    {α : Type u}
    [CancelCommMonoid α]
    {S : Submonoid α}
    (v : MultiplicativeZValuation α)

/-- Raw value of a commutative fraction presentation. -/
def rawFractionValue
    (x : RightFraction S) : ℤ :=
  v.value x.numerator -
    v.value (x.denominator : α)

/-- Cross-equivalent presentations have the same integer valuation. -/
theorem rawFractionValue_eq_of_rel
    {x y : RightFraction S}
    (h : FractionRel S x y) :
    v.rawFractionValue x =
      v.rawFractionValue y := by
  unfold rawFractionValue FractionRel at *
  have hv :=
    congrArg v.value h
  rw [v.mul_eq_add, v.mul_eq_add] at hv
  omega

/-- Localized integer valuation on the genuine commutative fraction quotient. -/
def fractionValue :
    CommFraction S → ℤ :=
  Quotient.lift
    v.rawFractionValue
    (by
      intro x y h
      exact v.rawFractionValue_eq_of_rel h)

@[simp] theorem fractionValue_mk
    (a : α)
    (s : S) :
    v.fractionValue (CommFraction.mk a s) =
      v.value a - v.value (s : α) :=
  rfl

@[simp] theorem fractionValue_ofElement
    (a : α) :
    v.fractionValue
        (CommFraction.ofElement
          (S := S) a)
      =
    v.value a := by
  simp [CommFraction.ofElement,
    fractionValue_mk,
    v.one_eq_zero]

@[simp] theorem fractionValue_one :
    v.fractionValue (1 : CommFraction S) = 0 := by
  rw [CommFraction.one_eq_mk]
  simp [fractionValue_mk, v.one_eq_zero]

/-- Valuation remains additive after localization. -/
theorem fractionValue_mul
    (x y : CommFraction S) :
    v.fractionValue (x * y) =
      v.fractionValue x +
        v.fractionValue y := by
  refine Quotient.inductionOn x ?_
  intro x
  rcases x with ⟨a, s⟩
  refine Quotient.inductionOn y ?_
  intro y
  rcases y with ⟨b, t⟩
  change
    v.fractionValue
        (CommFraction.mk (S := S) a s *
          CommFraction.mk b t)
      =
    _
  rw [CommFraction.mk_mul_mk]
  simp only [fractionValue_mk]
  rw [v.mul_eq_add, v.mul_eq_add]
  omega

/-- Selected denominator inverses have the expected negative valuation. -/
@[simp] theorem fractionValue_denominatorInverse
    (s : S) :
    v.fractionValue
        (CommFraction.denominatorInverse s)
      =
    - v.value (s : α) := by
  simp [CommFraction.denominatorInverse,
    fractionValue_mk,
    v.one_eq_zero]

/-- General fraction law in the familiar numerator-minus-denominator form. -/
theorem fractionValue_eq_source_sub_denominator
    (a : α)
    (s : S) :
    v.fractionValue (CommFraction.mk a s) =
      v.fractionValue
          (CommFraction.ofElement
            (S := S) a)
        -
      v.value (s : α) := by
  simp

end MultiplicativeZValuation
end CausalLocalization

namespace CausalFactorization
namespace CanonicalAtomicDomain

universe u

variable
    {α : Type u}
    [CancelCommMonoid α]
    [DecidableEq α]

/-- Canonical atomic valuation vanishes at one.

This is derived from multiplicative additivity:
v(1)=v(1*1)=v(1)+v(1). -/
theorem valuation_one
    (D : CanonicalAtomicDomain (α := α))
    (p : α) :
    D.valuation p 1 = 0 := by
  have h :=
    D.valuation_mul p 1 1
  simp only [mul_one] at h
  omega

/-- Integer lift of one intrinsic atomic valuation.

No new valuation axiom is introduced: both laws are inherited from the
canonical factorization profile. -/
def integerValuation
    (D : CanonicalAtomicDomain (α := α))
    (p : α) :
    CausalLocalization.MultiplicativeZValuation α where

  value := fun x =>
    Int.ofNat (D.valuation p x)

  one_eq_zero := by
    simp [D.valuation_one p]

  mul_eq_add := by
    intro x y
    rw [D.valuation_mul p x y]
    simp

/-- The localized atomic valuation of a causal fraction is the difference of
the source multiplicities. -/
@[simp] theorem localizedIntegerValuation_mk
    (D : CanonicalAtomicDomain (α := α))
    (p : α)
    {S : Submonoid α}
    (a : α)
    (s : S) :
    (D.integerValuation p).fractionValue
        (CausalLocalization.CommFraction.mk a s)
      =
    Int.ofNat (D.valuation p a) -
      Int.ofNat (D.valuation p (s : α)) :=
  rfl

/-- In particular denominator inversion negates the intrinsic primary depth. -/
@[simp] theorem localizedIntegerValuation_denominatorInverse
    (D : CanonicalAtomicDomain (α := α))
    (p : α)
    {S : Submonoid α}
    (s : S) :
    (D.integerValuation p).fractionValue
        (CausalLocalization.CommFraction.denominatorInverse s)
      =
    - Int.ofNat (D.valuation p (s : α)) := by
  exact
    CausalLocalization.MultiplicativeZValuation
      .fractionValue_denominatorInverse
        (D.integerValuation p) s

end CanonicalAtomicDomain
end CausalFactorization
end CausalGeometry
