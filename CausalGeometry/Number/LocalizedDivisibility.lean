import CausalGeometry.Number.CommutativeLocalizationUniversal
import CausalGeometry.Number.LocalizedValuation
import CausalGeometry.Number.Divisibility
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [CancelCommMonoid α]
variable {S : Submonoid α}

/-- Source divisibility after saturation by the selected denominator system.

a divides_S b means that a divides b after multiplication of b by one selected
denominator.  This is the exact source relation seen by the commutative
localization. -/
def SaturatedDivides
    (S : Submonoid α)
    (a b : α) : Prop :=
  ∃ c : α, ∃ s : S,
    a * c = b * (s : α)

namespace CommFraction

/-- Equality of two presented commutative fractions is exactly cross
multiplication. -/
theorem mk_eq_mk_iff_cross
    {a b : α}
    {s t : S} :
    mk (S := S) a s = mk b t ↔
      a * (t : α) =
        b * (s : α) := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact mk_eq_mk_of_cross h

/-- Divisibility between embedded source elements is exactly S-saturated
source divisibility. -/
theorem ofElement_leftDivides_iff_saturatedDivides
    (a b : α) :
    CausalDivisibility.LeftDivides
        (ofElement (S := S) a)
        (ofElement b)
      ↔
    SaturatedDivides S a b := by

  constructor

  · rintro ⟨x, hx⟩

    refine Quotient.inductionOn x ?_

    intro r
    rcases r with ⟨c, s⟩

    change
      ofElement (S := S) a *
          mk c s
        =
      ofElement b at hx

    change
      mk (S := S) (a * c) s =
        mk b 1 at hx

    have hcross :=
      (mk_eq_mk_iff_cross
        (S := S)).1 hx

    refine ⟨c, s, ?_⟩

    simpa using hcross

  · rintro ⟨c, s, hsat⟩

    refine
      ⟨mk (S := S) c s, ?_⟩

    change
      mk (S := S) (a * c) s =
        mk b 1

    apply mk_eq_mk_of_cross

    simpa using hsat

/-- Commutativity makes right localized divisibility equivalent to the same
saturated source relation. -/
theorem ofElement_rightDivides_iff_saturatedDivides
    (a b : α) :
    CausalDivisibility.RightDivides
        (ofElement (S := S) a)
        (ofElement b)
      ↔
    SaturatedDivides S a b := by

  constructor

  · rintro ⟨x, hx⟩

    have hleft :
        CausalDivisibility.LeftDivides
          (ofElement (S := S) a)
          (ofElement b) := by
      exact ⟨x, by
        simpa [mul_comm] using hx⟩

    exact
      (ofElement_leftDivides_iff_saturatedDivides
        (S := S) a b).1 hleft

  · intro hsat

    have hleft :=
      (ofElement_leftDivides_iff_saturatedDivides
        (S := S) a b).2 hsat

    rcases hleft with ⟨x, hx⟩

    exact
      ⟨x, by
        simpa [mul_comm] using hx⟩

/-- Ordinary source divisibility always survives localization. -/
theorem sourceLeftDivides_implies_localized
    {a b : α}
    (h :
      CausalDivisibility.LeftDivides a b) :
    CausalDivisibility.LeftDivides
      (ofElement (S := S) a)
      (ofElement b) := by

  rcases h with ⟨c, hc⟩

  apply
    (ofElement_leftDivides_iff_saturatedDivides
      (S := S) a b).2

  refine ⟨c, 1, ?_⟩

  simpa using hc

/-- Every selected denominator becomes divisibility-equivalent to one. -/
theorem denominator_leftDivides_one
    (s : S) :
    CausalDivisibility.LeftDivides
      (ofElement (S := S) (s : α))
      1 := by

  refine
    ⟨denominatorInverse s, ?_⟩

  simpa [ofElement] using
    denominator_mul_inverse s

theorem one_leftDivides_denominator
    (s : S) :
    CausalDivisibility.LeftDivides
      (1 : CommFraction S)
      (ofElement (s : α)) := by

  exact
    ⟨ofElement (s : α), by simp⟩

/-- Thus localization deliberately collapses every selected denominator into
the same mutual-divisibility class as the unit. -/
theorem denominator_mutuallyDivides_one
    (s : S) :
    CausalDivisibility.LeftDivides
        (ofElement (S := S) (s : α)) 1
      ∧
    CausalDivisibility.LeftDivides
        (1 : CommFraction S)
        (ofElement (s : α)) :=
  ⟨denominator_leftDivides_one s,
    one_leftDivides_denominator s⟩

end CommFraction

namespace SaturatedDivides

/-- Ordinary divisibility is contained in saturated divisibility. -/
theorem of_leftDivides
    {a b : α}
    (h : CausalDivisibility.LeftDivides a b) :
    SaturatedDivides S a b := by

  rcases h with ⟨c, hc⟩

  refine ⟨c, 1, ?_⟩

  simpa using hc

end SaturatedDivides

end CausalLocalization

namespace CausalFactorization
namespace CanonicalAtomicDomain

variable
    {α : Type u}
    [CancelCommMonoid α]
    [DecidableEq α]

variable
    (D : CanonicalAtomicDomain (α := α))

/-- S-saturated divisibility imposes the corresponding valuation inequality:
the divisor valuation can exceed the target valuation only by valuation
already present in an inverted denominator. -/
theorem valuation_le_target_add_denominator_of_saturatedDivides
    {S : Submonoid α}
    {a b : α}
    (h :
      CausalLocalization.SaturatedDivides
        S a b)
    (p : α) :
    ∃ s : S,
      D.valuation p a ≤
        D.valuation p b +
          D.valuation p (s : α) := by

  rcases h with ⟨c, s, hEq⟩

  refine ⟨s, ?_⟩

  have hv :=
    congrArg (D.valuation p) hEq

  rw [
    D.valuation_mul,
    D.valuation_mul
  ] at hv

  omega

/-- If an atom p is invisible to every selected denominator, localized
divisibility between source elements still forces the ordinary valuation
inequality v_p(a) <= v_p(b). -/
theorem valuation_le_of_localizedDivides_of_denominatorInvisible
    {S : Submonoid α}
    {a b : α}
    (hdiv :
      CausalDivisibility.LeftDivides
        (CausalLocalization.CommFraction.ofElement
          (S := S) a)
        (CausalLocalization.CommFraction.ofElement b))
    (p : α)
    (hinvisible :
      ∀ s : S,
        D.valuation p (s : α) = 0) :
    D.valuation p a ≤
      D.valuation p b := by

  have hsat :
      CausalLocalization.SaturatedDivides
        S a b :=
    (CausalLocalization.CommFraction
      .ofElement_leftDivides_iff_saturatedDivides
        (S := S) a b).1 hdiv

  rcases
      D.valuation_le_target_add_denominator_of_saturatedDivides
        hsat p with
    ⟨s, hs⟩

  rw [hinvisible s, Nat.add_zero] at hs

  exact hs

/-- Localized valuation makes the same information loss quantitative:
inverting s subtracts exactly its source multiplicity. -/
theorem localized_valuation_shift
    {S : Submonoid α}
    (p a : α)
    (s : S) :
    (D.integerValuation p).fractionValue
        (CausalLocalization.CommFraction.mk a s)
      =
    Int.ofNat (D.valuation p a) -
      Int.ofNat (D.valuation p (s : α)) :=
  D.localizedIntegerValuation_mk p a s

/-- Atoms invisible to S retain their source valuation on every fraction with
selected denominator. -/
theorem localized_valuation_eq_numerator_of_denominatorInvisible
    {S : Submonoid α}
    (p a : α)
    (s : S)
    (hinvisible :
      ∀ t : S,
        D.valuation p (t : α) = 0) :
    (D.integerValuation p).fractionValue
        (CausalLocalization.CommFraction.mk a s)
      =
    Int.ofNat (D.valuation p a) := by

  rw [D.localized_valuation_shift p a s]
  rw [hinvisible s]
  simp

end CanonicalAtomicDomain
end CausalFactorization
end CausalGeometry
