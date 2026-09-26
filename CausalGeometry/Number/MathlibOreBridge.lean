import CausalGeometry.Number.OreLocalization
import Mathlib.GroupTheory.OreLocalization.Basic

namespace CausalGeometry

universe u v

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

/-- Mathlib's OreSet is the strengthened left-Ore hypothesis needed for a
canonical localization: besides common left Ore multiples it contains the
weak right-cancellation/reversibility law required by the quotient. -/
def MathlibLeftOreCertified (S : Submonoid α) : Prop :=
  Nonempty (OreLocalization.OreSet S)

section MathlibOre

variable [OreLocalization.OreSet S]

/-- The chosen Ore witnesses from mathlib instantiate our left Ore square
orientation exactly:
u*a = b*s. -/
def mathlibLeftOreSquare
    (a : α) (s : S) :
    LeftOreSquare S a s where
  numerator :=
    OreLocalization.oreNum a s
  denominator :=
    OreLocalization.oreDenom a s
  cross :=
    OreLocalization.ore_eq a s

/-- A mathlib OreSet is therefore strictly stronger than our raw
LeftOreCondition. -/
theorem leftOreCondition_of_mathlib :
    LeftOreCondition S := by
  intro a s
  exact ⟨mathlibLeftOreSquare a s⟩

/-- The additional reversibility/cancellation ingredient absent from the raw
LeftOreCondition interface. -/
theorem leftOre_reversibility
    (a b : α) (s : S)
    (h : a * (s : α) = b * (s : α)) :
    ∃ s' : S,
      (s' : α) * a =
        (s' : α) * b :=
  OreLocalization.ore_right_cancel a b s h

/-- Canonical left localization supplied by mathlib.  Its normal form is the
same orientation as our LeftFraction: s^{-1}*a. -/
abbrev CanonicalLeftLocalization :=
  OreLocalization S α

/-- Map one of our raw left-fraction presentations into the canonical
mathlib Ore quotient. -/
def LeftFraction.toCanonical
    (x : LeftFraction S) :
    CanonicalLeftLocalization (α := α) (S := S) :=
  OreLocalization.oreDiv x.numerator x.denominator

/-- Canonical source embedding a |-> a/1. -/
abbrev canonicalLeftSourceHom :
    α →* CanonicalLeftLocalization
      (α := α) (S := S) :=
  OreLocalization.numeratorHom

@[simp] theorem leftFraction_toCanonical_ofElement
    (a : α) :
    (LeftFraction.ofElement
      (S := S) a).toCanonical =
      canonicalLeftSourceHom
        (α := α) (S := S) a := by
  rfl

/-- Selected inverse of one denominator in the canonical localization. -/
def canonicalLeftDenominatorInverse
    (s : S) :
    CanonicalLeftLocalization
      (α := α) (S := S) :=
  OreLocalization.oreDiv (1 : α) s

@[simp] theorem canonical_source_mul_denominatorInverse
    (s : S) :
    canonicalLeftSourceHom
        (α := α) (S := S) (s : α) *
      canonicalLeftDenominatorInverse
        (α := α) (S := S) s =
    1 := by
  exact OreLocalization.mul_inv s 1

@[simp] theorem canonical_denominatorInverse_mul_source
    (s : S) :
    canonicalLeftDenominatorInverse
        (α := α) (S := S) s *
      canonicalLeftSourceHom
        (α := α) (S := S) (s : α) =
    1 := by
  exact OreLocalization.mul_inv 1 s

/-- Every selected denominator is a unit in the canonical localization. -/
theorem canonical_source_denominator_isUnit
    (s : S) :
    IsUnit
      (canonicalLeftSourceHom
        (α := α) (S := S) (s : α)) :=
  OreLocalization.numerator_isUnit s

section GroupTarget

variable {G : Type v} [Group G]

/-- Any monoid map into a group sends every denominator canonically to a unit. -/
def denominatorUnitsHom
    (f : α →* G) :
    S →* Gˣ where
  toFun := fun s =>
    { val := f (s : α)
      inv := (f (s : α))⁻¹
      val_inv := mul_inv _
      inv_val := inv_mul _ }
  map_one' := by
    apply Units.ext
    simp
  map_mul' := by
    intro x y
    apply Units.ext
    simp

@[simp] theorem denominatorUnitsHom_val
    (f : α →* G)
    (s : S) :
    ((denominatorUnitsHom f s : Gˣ) : G) =
      f (s : α) :=
  rfl

/-- Canonical universal realization of the left Ore localization in any group
target. -/
def canonicalLeftUniversalHom
    (f : α →* G) :
    CanonicalLeftLocalization
        (α := α) (S := S) →* G :=
  OreLocalization.universalMulHom
    f (denominatorUnitsHom f)
    (by intro s; rfl)

@[simp] theorem canonicalLeftUniversalHom_source
    (f : α →* G)
    (a : α) :
    canonicalLeftUniversalHom
        (S := S) f
        (canonicalLeftSourceHom
          (α := α) (S := S) a)
      =
    f a := by
  exact
    OreLocalization.universalMulHom_commutes
      f (denominatorUnitsHom f)
      (by intro s; rfl)

@[simp] theorem canonicalLeftUniversalHom_fraction
    (f : α →* G)
    (a : α)
    (s : S) :
    canonicalLeftUniversalHom
        (S := S) f
        (OreLocalization.oreDiv a s)
      =
    (f (s : α))⁻¹ * f a := by
  simpa [canonicalLeftUniversalHom,
    denominatorUnitsHom] using
    (OreLocalization.universalMulHom_apply
      f (denominatorUnitsHom f)
      (by intro t; rfl)
      (r := a) (s := s))

/-- Universal uniqueness: a monoid morphism out of the canonical localization
is completely determined by its restriction to the source. -/
theorem canonicalLeftUniversalHom_unique
    (f : α →* G)
    (φ :
      CanonicalLeftLocalization
        (α := α) (S := S) →* G)
    (hsource :
      ∀ a : α,
        φ (canonicalLeftSourceHom
          (α := α) (S := S) a) =
          f a) :
    φ = canonicalLeftUniversalHom
      (S := S) f := by
  exact
    OreLocalization.universalMulHom_unique
      f (denominatorUnitsHom f)
      (by intro s; rfl)
      φ hsource

end GroupTarget
end MathlibOre

end CausalLocalization
end CausalGeometry
