import CausalGeometry.Number.BilateralOreMathlib
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

section Presentation

variable [OreLocalization.OreSet S]

/-- A canonical left raw fraction really is denominator-inverse times source
numerator inside the canonical Ore localization. -/
theorem leftFraction_toCanonical_eq_inverse_mul_source
    (x : LeftFraction S) :
    x.toCanonical =
      canonicalLeftDenominatorInverse
          (α := α) (S := S) x.denominator *
        canonicalLeftSourceHom
          (α := α) (S := S) x.numerator := by
  rcases x with ⟨s, a⟩
  change
    OreLocalization.oreDiv a s =
      OreLocalization.oreDiv (1 : α) s *
        OreLocalization.oreDiv a (1 : S)
  symm
  simpa using
    (OreLocalization.oreDiv_mul_char
      (1 : α) a s (1 : S)
      (1 : α) (1 : S)
      (by simp))

end Presentation

section RightPresentation

variable [OreLocalization.OreSet S.op]

/-- A canonical right raw fraction really is source numerator times the
selected denominator inverse. -/
theorem rightFraction_toCanonical_eq_source_mul_inverse
    (x : RightFraction S) :
    x.toCanonical =
      canonicalRightSourceHom
          (α := α) (S := S) x.numerator *
        canonicalRightDenominatorInverse
          (α := α) (S := S) x.denominator := by
  rcases x with ⟨a, s⟩
  apply MulOpposite.unop_injective
  change
    OreLocalization.oreDiv
        (MulOpposite.op a)
        (opDenominator s)
      =
    OreLocalization.oreDiv
        (1 : αᵐᵒᵖ)
        (opDenominator s) *
      OreLocalization.oreDiv
        (MulOpposite.op a)
        (1 : S.op)
  exact
    leftFraction_toCanonical_eq_inverse_mul_source
      (α := αᵐᵒᵖ)
      (S := S.op)
      { denominator := opDenominator s
        numerator := MulOpposite.op a }

end RightPresentation

section BilateralNormalForms

variable [OreLocalization.OreSet S]
variable [OreLocalization.OreSet S.op]

/-- Convert one left presentation s⁻¹ a into a certified right presentation
b u⁻¹ using the canonical right Ore square a u = s b. -/
def LeftFraction.toRightNormal
    (x : LeftFraction S) :
    RightFraction S :=
  let w :=
    mathlibRightOreSquare
      (S := S)
      x.numerator x.denominator
  { numerator := w.numerator
    denominator := w.denominator }

/-- Convert one right presentation a s⁻¹ into a certified left presentation
u⁻¹ b using the canonical left Ore square u a = b s. -/
def RightFraction.toLeftNormal
    (x : RightFraction S) :
    LeftFraction S :=
  let w :=
    mathlibLeftOreSquare
      (S := S)
      x.numerator x.denominator
  { denominator := w.denominator
    numerator := w.numerator }

/-- The canonical bilateral equivalence sends every raw left fraction to the
right normal form supplied by its right Ore square. -/
theorem bilateral_left_to_right_normal
    (x : LeftFraction S) :
    canonicalBilateralOreEquiv
        (α := α) (S := S)
        x.toCanonical
      =
    x.toRightNormal.toCanonical := by
  rcases x with ⟨s, a⟩
  let w :=
    mathlibRightOreSquare
      (S := S) a s
  have hw :
      a * (w.denominator : α) =
        (s : α) * w.numerator :=
    w.cross
  rw [
    leftFraction_toCanonical_eq_inverse_mul_source,
    map_mul,
    canonicalBilateralOreEquiv_denominatorInverse,
    canonicalBilateralOreEquiv_source
  ]
  change
    canonicalRightDenominatorInverse
          (α := α) (S := S) s *
        canonicalRightSourceHom
          (α := α) (S := S) a
      =
    (LeftFraction.toRightNormal
      (S := S) { denominator := s, numerator := a }).toCanonical
  rw [
    rightFraction_toCanonical_eq_source_mul_inverse
  ]
  change
    canonicalRightDenominatorInverse
          (α := α) (S := S) s *
        canonicalRightSourceHom
          (α := α) (S := S) a
      =
    canonicalRightSourceHom
          (α := α) (S := S) w.numerator *
        canonicalRightDenominatorInverse
          (α := α) (S := S) w.denominator
  calc
    canonicalRightDenominatorInverse
          (α := α) (S := S) s *
        canonicalRightSourceHom
          (α := α) (S := S) a
        =
      (canonicalRightDenominatorInverse
            (α := α) (S := S) s *
          canonicalRightSourceHom
            (α := α) (S := S) a) *
        (canonicalRightSourceHom
              (α := α) (S := S)
              (w.denominator : α) *
          canonicalRightDenominatorInverse
            (α := α) (S := S) w.denominator) := by
              rw [
                canonicalRight_source_mul_denominatorInverse
              ]
              simp
    _ =
      canonicalRightDenominatorInverse
            (α := α) (S := S) s *
        canonicalRightSourceHom
          (α := α) (S := S)
          (a * (w.denominator : α)) *
        canonicalRightDenominatorInverse
          (α := α) (S := S) w.denominator := by
            simp only [map_mul]
            simp [mul_assoc]
    _ =
      canonicalRightDenominatorInverse
            (α := α) (S := S) s *
        canonicalRightSourceHom
          (α := α) (S := S)
          ((s : α) * w.numerator) *
        canonicalRightDenominatorInverse
          (α := α) (S := S) w.denominator := by
            rw [hw]
    _ =
      canonicalRightDenominatorInverse
            (α := α) (S := S) s *
        (canonicalRightSourceHom
              (α := α) (S := S) (s : α) *
          canonicalRightSourceHom
            (α := α) (S := S) w.numerator) *
        canonicalRightDenominatorInverse
          (α := α) (S := S) w.denominator := by
            rw [map_mul]
    _ =
      canonicalRightSourceHom
            (α := α) (S := S) w.numerator *
        canonicalRightDenominatorInverse
          (α := α) (S := S) w.denominator := by
            rw [
              ← mul_assoc,
              canonicalRight_denominatorInverse_mul_source
            ]
            simp

/-- Conversely the inverse bilateral map sends every raw right fraction to the
left normal form supplied by its left Ore square. -/
theorem bilateral_right_to_left_normal
    (x : RightFraction S) :
    (canonicalBilateralOreEquiv
        (α := α) (S := S)).symm
        x.toCanonical
      =
    x.toLeftNormal.toCanonical := by
  rcases x with ⟨a, s⟩
  let w :=
    mathlibLeftOreSquare
      (S := S) a s
  have hw :
      (w.denominator : α) * a =
        w.numerator * (s : α) :=
    w.cross

  change
    canonicalRightToLeft
        (α := α) (S := S)
        ({ numerator := a
           denominator := s } :
          RightFraction S).toCanonical
      =
    (RightFraction.toLeftNormal
      (S := S) { numerator := a, denominator := s }).toCanonical

  rw [
    rightFraction_toCanonical_eq_source_mul_inverse,
    map_mul,
    canonicalRightToLeft_source,
    canonicalRightToLeft_denominatorInverse,
    leftFraction_toCanonical_eq_inverse_mul_source
  ]

  change
    canonicalLeftSourceHom
          (α := α) (S := S) a *
        canonicalLeftDenominatorInverse
          (α := α) (S := S) s
      =
    canonicalLeftDenominatorInverse
          (α := α) (S := S) w.denominator *
        canonicalLeftSourceHom
          (α := α) (S := S) w.numerator

  calc
    canonicalLeftSourceHom
          (α := α) (S := S) a *
        canonicalLeftDenominatorInverse
          (α := α) (S := S) s
        =
      (canonicalLeftDenominatorInverse
            (α := α) (S := S) w.denominator *
          canonicalLeftSourceHom
            (α := α) (S := S)
            (w.denominator : α)) *
        (canonicalLeftSourceHom
            (α := α) (S := S) a *
          canonicalLeftDenominatorInverse
            (α := α) (S := S) s) := by
              rw [
                canonical_denominatorInverse_mul_source
              ]
              simp
    _ =
      canonicalLeftDenominatorInverse
            (α := α) (S := S) w.denominator *
        canonicalLeftSourceHom
          (α := α) (S := S)
          ((w.denominator : α) * a) *
        canonicalLeftDenominatorInverse
          (α := α) (S := S) s := by
            simp only [map_mul]
            simp [mul_assoc]
    _ =
      canonicalLeftDenominatorInverse
            (α := α) (S := S) w.denominator *
        canonicalLeftSourceHom
          (α := α) (S := S)
          (w.numerator * (s : α)) *
        canonicalLeftDenominatorInverse
          (α := α) (S := S) s := by
            rw [hw]
    _ =
      canonicalLeftDenominatorInverse
            (α := α) (S := S) w.denominator *
        (canonicalLeftSourceHom
              (α := α) (S := S) w.numerator *
          canonicalLeftSourceHom
            (α := α) (S := S) (s : α)) *
        canonicalLeftDenominatorInverse
          (α := α) (S := S) s := by
            rw [map_mul]
    _ =
      canonicalLeftDenominatorInverse
            (α := α) (S := S) w.denominator *
        canonicalLeftSourceHom
          (α := α) (S := S) w.numerator := by
            simp only [mul_assoc]
            rw [
              canonical_source_mul_denominatorInverse
            ]
            simp

end BilateralNormalForms
end CausalLocalization
end CausalGeometry
