import CausalGeometry.Number.MathlibOreBridge
import Mathlib.Algebra.Group.Submonoid.MulOpposite

namespace CausalGeometry

universe u v

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

/-- Send a selected denominator to the opposite denominator submonoid. -/
def opDenominator
    (s : S) : S.op :=
  ⟨MulOpposite.op (s : α), by simp⟩

/-- Recover the original denominator from the opposite submonoid. -/
def unopDenominator
    (s : S.op) : S :=
  ⟨MulOpposite.unop (s : αᵐᵒᵖ), by
    simpa using s.property⟩

@[simp] theorem unop_opDenominator
    (s : S) :
    unopDenominator (opDenominator s) = s := by
  apply Subtype.ext
  simp [opDenominator, unopDenominator]

section RightViaOpposite

variable [OreLocalization.OreSet S.op]

/-- A left Ore square in the opposite monoid is exactly a right Ore square in
the original monoid. -/
def mathlibRightOreSquare
    (a : α) (s : S) :
    RightOreSquare S a s where
  numerator :=
    MulOpposite.unop
      (OreLocalization.oreNum
        (MulOpposite.op a)
        (opDenominator s))
  denominator :=
    unopDenominator
      (OreLocalization.oreDenom
        (MulOpposite.op a)
        (opDenominator s))
  cross := by
    have h :=
      OreLocalization.ore_eq
        (MulOpposite.op a)
        (opDenominator s)
    have hu := congrArg MulOpposite.unop h
    simpa [opDenominator, unopDenominator] using hu

/-- The opposite OreSet supplies our raw right Ore condition. -/
theorem rightOreCondition_of_mathlibOpposite :
    RightOreCondition S := by
  intro a s
  exact ⟨mathlibRightOreSquare a s⟩

/-- The extra reversibility law for the right-oriented theory.

A common selected factor on the left may be moved to a common selected factor
on the right. -/
theorem rightOre_reversibility
    (a b : α) (s : S)
    (h : (s : α) * a =
      (s : α) * b) :
    ∃ s' : S,
      a * (s' : α) =
        b * (s' : α) := by
  have hop :
      MulOpposite.op a *
          (opDenominator s : αᵐᵒᵖ)
        =
      MulOpposite.op b *
          (opDenominator s : αᵐᵒᵖ) := by
    simpa [opDenominator] using
      congrArg MulOpposite.op h
  rcases
      OreLocalization.ore_right_cancel
        (MulOpposite.op a)
        (MulOpposite.op b)
        (opDenominator s)
        hop with
    ⟨t, ht⟩
  refine ⟨unopDenominator t, ?_⟩
  have hu := congrArg MulOpposite.unop ht
  simpa [unopDenominator] using hu

/-- Canonical right localization: the opposite of the canonical left
localization of the opposite monoid. -/
abbrev CanonicalRightLocalization :=
  (OreLocalization S.op αᵐᵒᵖ)ᵐᵒᵖ

/-- Map a raw right-fraction presentation a*s^{-1} into the canonical right
localization. -/
def RightFraction.toCanonical
    (x : RightFraction S) :
    CanonicalRightLocalization
      (α := α) (S := S) :=
  MulOpposite.op
    (OreLocalization.oreDiv
      (MulOpposite.op x.numerator)
      (opDenominator x.denominator))

/-- Canonical right source embedding. -/
def canonicalRightSourceHom :
    α →*
      CanonicalRightLocalization
        (α := α) (S := S) where
  toFun := fun a =>
    MulOpposite.op
      (OreLocalization.numeratorHom
        (MulOpposite.op a))
  map_one' := by
    simp
  map_mul' := by
    intro a b
    simp

@[simp] theorem rightFraction_toCanonical_ofElement
    (a : α) :
    (RightFraction.ofElement
      (S := S) a).toCanonical =
      canonicalRightSourceHom
        (α := α) (S := S) a := by
  rfl

/-- Chosen right denominator inverse. -/
def canonicalRightDenominatorInverse
    (s : S) :
    CanonicalRightLocalization
      (α := α) (S := S) :=
  MulOpposite.op
    (OreLocalization.oreDiv
      (1 : αᵐᵒᵖ)
      (opDenominator s))

@[simp] theorem canonicalRight_source_mul_denominatorInverse
    (s : S) :
    canonicalRightSourceHom
        (α := α) (S := S) (s : α) *
      canonicalRightDenominatorInverse
        (α := α) (S := S) s =
    1 := by
  have h :=
    canonical_denominatorInverse_mul_source
      (α := αᵐᵒᵖ)
      (S := S.op)
      (opDenominator s)
  have hop := congrArg MulOpposite.op h
  simpa [canonicalRightSourceHom,
    canonicalRightDenominatorInverse,
    canonicalLeftSourceHom,
    canonicalLeftDenominatorInverse] using hop

@[simp] theorem canonicalRight_denominatorInverse_mul_source
    (s : S) :
    canonicalRightDenominatorInverse
        (α := α) (S := S) s *
      canonicalRightSourceHom
        (α := α) (S := S) (s : α) =
    1 := by
  have h :=
    canonical_source_mul_denominatorInverse
      (α := αᵐᵒᵖ)
      (S := S.op)
      (opDenominator s)
  have hop := congrArg MulOpposite.op h
  simpa [canonicalRightSourceHom,
    canonicalRightDenominatorInverse,
    canonicalLeftSourceHom,
    canonicalLeftDenominatorInverse] using hop

/-- Turn a homomorphism into the corresponding homomorphism of opposite
monoids.  The two order reversals make this multiplicative. -/
def oppositeMonoidHom
    {G : Type v} [Monoid G]
    (f : α →* G) :
    αᵐᵒᵖ →* Gᵐᵒᵖ where
  toFun := fun a =>
    MulOpposite.op
      (f (MulOpposite.unop a))
  map_one' := by
    simp
  map_mul' := by
    intro a b
    simp

section GroupTarget

variable {G : Type v} [Group G]

/-- Universal group realization of the right Ore localization, obtained by
applying the left universal property in the opposite monoid and reversing
back. -/
def canonicalRightUniversalHom
    (f : α →* G) :
    CanonicalRightLocalization
        (α := α) (S := S) →* G where
  toFun := fun q =>
    MulOpposite.unop
      (canonicalLeftUniversalHom
        (S := S.op)
        (oppositeMonoidHom f)
        (MulOpposite.unop q))
  map_one' := by
    simp [canonicalLeftUniversalHom,
      oppositeMonoidHom]
  map_mul' := by
    intro x y
    simp [canonicalLeftUniversalHom,
      oppositeMonoidHom]

@[simp] theorem canonicalRightUniversalHom_source
    (f : α →* G)
    (a : α) :
    canonicalRightUniversalHom
        (S := S) f
        (canonicalRightSourceHom
          (α := α) (S := S) a)
      =
    f a := by
  simp [canonicalRightUniversalHom,
    canonicalRightSourceHom,
    oppositeMonoidHom]

@[simp] theorem canonicalRightUniversalHom_fraction
    (f : α →* G)
    (a : α)
    (s : S) :
    canonicalRightUniversalHom
        (S := S) f
        (MulOpposite.op
          (OreLocalization.oreDiv
            (MulOpposite.op a)
            (opDenominator s)))
      =
    f a * (f (s : α))⁻¹ := by
  change
    MulOpposite.unop
      (canonicalLeftUniversalHom
        (S := S.op)
        (oppositeMonoidHom f)
        (OreLocalization.oreDiv
          (MulOpposite.op a)
          (opDenominator s)))
      =
    _
  rw [canonicalLeftUniversalHom_fraction]
  simp [oppositeMonoidHom, opDenominator]

end GroupTarget
end RightViaOpposite

end CausalLocalization
end CausalGeometry
