import CausalGeometry.Number.MathlibRightOreBridge

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

/-- The extra reversibility law needed in addition to the raw left Ore
condition.

If two source elements become equal after multiplication by one selected
denominator on the right, another selected denominator can equalize them on
the left.  This is the cancellation/reversibility ingredient carried by
mathlib's OreSet but deliberately absent from LeftOreCondition. -/
def LeftOreReversible (S : Submonoid α) : Prop :=
  ∀ a b (s : S),
    a * (s : α) = b * (s : α) →
      ∃ t : S,
        (t : α) * a = (t : α) * b

/-- Intrinsic left-localization hypotheses in the terminology of this
repository. -/
def LeftOreLocalizationHypotheses
    (S : Submonoid α) : Prop :=
  LeftOreCondition S ∧ LeftOreReversible S

/-- Choose one raw left Ore square.  Choice is used only to instantiate the
canonical quotient construction; the resulting localization is quotient-level
and does not make the chosen witness part of its semantics. -/
noncomputable def chosenLeftOreSquare
    (hOre : LeftOreCondition S)
    (a : α) (s : S) :
    LeftOreSquare S a s :=
  Classical.choice (hOre a s)

/-- Our intrinsic left Ore + reversibility hypotheses construct the canonical
mathlib OreSet. -/
noncomputable def leftMathlibOreSetOfHypotheses
    (h : LeftOreLocalizationHypotheses S) :
    OreLocalization.OreSet S where

  ore_right_cancel := by
    intro a b s hab
    exact h.2 a b s hab

  oreNum := fun a s =>
    (chosenLeftOreSquare h.1 a s).numerator

  oreDenom := fun a s =>
    (chosenLeftOreSquare h.1 a s).denominator

  ore_eq := by
    intro a s
    exact (chosenLeftOreSquare h.1 a s).cross

/-- Conversely a canonical mathlib OreSet provides exactly the two intrinsic
left hypotheses. -/
theorem leftHypotheses_of_mathlibOreSet
    [OreLocalization.OreSet S] :
    LeftOreLocalizationHypotheses S := by
  constructor
  · exact leftOreCondition_of_mathlib
  · intro a b s hab
    exact leftOre_reversibility a b s hab

/-- Exact equivalence between the repository's intrinsic left localization
hypotheses and existence of a canonical mathlib OreSet structure.

This theorem is the conceptual boundary: raw LeftOreCondition alone is weaker;
the missing datum is precisely LeftOreReversible. -/
theorem leftOreLocalizationHypotheses_iff :
    LeftOreLocalizationHypotheses S ↔
      Nonempty (OreLocalization.OreSet S) := by
  constructor
  · intro h
    exact ⟨leftMathlibOreSetOfHypotheses h⟩
  · rintro ⟨h⟩
    letI : OreLocalization.OreSet S := h
    exact leftHypotheses_of_mathlibOreSet

/-- Right-handed reversibility.

If multiplication by a selected denominator on the left equalizes two source
elements, some selected denominator on the right equalizes them. -/
def RightOreReversible (S : Submonoid α) : Prop :=
  ∀ a b (s : S),
    (s : α) * a = (s : α) * b →
      ∃ t : S,
        a * (t : α) = b * (t : α)

/-- Intrinsic right-localization hypotheses. -/
def RightOreLocalizationHypotheses
    (S : Submonoid α) : Prop :=
  RightOreCondition S ∧ RightOreReversible S

noncomputable def chosenRightOreSquare
    (hOre : RightOreCondition S)
    (a : α) (s : S) :
    RightOreSquare S a s :=
  Classical.choice (hOre a s)

/-- A right Ore square in α becomes a left Ore square in αᵐᵒᵖ. -/
noncomputable def rightMathlibOreSetOfHypotheses
    (h : RightOreLocalizationHypotheses S) :
    OreLocalization.OreSet S.op where

  ore_right_cancel := by
    intro a b s hab
    have habUnop :
        (unopDenominator s : α) *
            MulOpposite.unop a
          =
        (unopDenominator s : α) *
            MulOpposite.unop b := by
      have hu := congrArg MulOpposite.unop hab
      simpa [unopDenominator] using hu
    rcases h.2
        (MulOpposite.unop a)
        (MulOpposite.unop b)
        (unopDenominator s)
        habUnop with
      ⟨t, ht⟩
    refine ⟨opDenominator t, ?_⟩
    have hop := congrArg MulOpposite.op ht
    simpa [opDenominator] using hop

  oreNum := fun a s =>
    MulOpposite.op
      ((chosenRightOreSquare
        h.1
        (MulOpposite.unop a)
        (unopDenominator s)).numerator)

  oreDenom := fun a s =>
    opDenominator
      ((chosenRightOreSquare
        h.1
        (MulOpposite.unop a)
        (unopDenominator s)).denominator)

  ore_eq := by
    intro a s
    let w :=
      chosenRightOreSquare
        h.1
        (MulOpposite.unop a)
        (unopDenominator s)
    have hw := w.cross
    have hop := congrArg MulOpposite.op hw
    simpa [w, opDenominator,
      unopDenominator] using hop

/-- A canonical OreSet on the opposite monoid provides exactly the intrinsic
right hypotheses. -/
theorem rightHypotheses_of_mathlibOpposite
    [OreLocalization.OreSet S.op] :
    RightOreLocalizationHypotheses S := by
  constructor
  · exact rightOreCondition_of_mathlibOpposite
  · intro a b s hab
    exact rightOre_reversibility a b s hab

/-- Exact right-handed counterpart of leftOreLocalizationHypotheses_iff. -/
theorem rightOreLocalizationHypotheses_iff :
    RightOreLocalizationHypotheses S ↔
      Nonempty
        (OreLocalization.OreSet S.op) := by
  constructor
  · intro h
    exact ⟨rightMathlibOreSetOfHypotheses h⟩
  · rintro ⟨h⟩
    letI : OreLocalization.OreSet S.op := h
    exact rightHypotheses_of_mathlibOpposite

end CausalLocalization
end CausalGeometry
