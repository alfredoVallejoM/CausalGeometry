import CausalGeometry.Number.LocalizedValuation
import CausalGeometry.Number.MathlibRightOreBridge
import Mathlib.Algebra.Group.TypeTags.Basic

namespace CausalGeometry

universe u

namespace CausalLocalization

namespace MultiplicativeZValuation

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}
variable (v : MultiplicativeZValuation α)

/-- Regard an additive integer valuation as a multiplicative group-valued
monoid morphism.

Multiplication in Multiplicative ℤ is addition in ℤ. -/
def toMultiplicativeHom :
    α →* Multiplicative ℤ where
  toFun := fun x =>
    Multiplicative.ofAdd (v.value x)
  map_one' := by
    apply Multiplicative.toAdd_injective
    simpa using v.one_eq_zero
  map_mul' := by
    intro x y
    apply Multiplicative.toAdd_injective
    simpa using v.mul_eq_add x y

section Left

variable [OreLocalization.OreSet S]

/-- Integer valuation on the canonical left Ore localization, obtained only
from the universal property. -/
def leftOreValue
    (x :
      CanonicalLeftLocalization
        (α := α) (S := S)) :
    ℤ :=
  Multiplicative.toAdd
    (canonicalLeftUniversalHom
      (S := S)
      v.toMultiplicativeHom x)

@[simp] theorem leftOreValue_source
    (a : α) :
    v.leftOreValue
        (canonicalLeftSourceHom
          (α := α) (S := S) a)
      =
    v.value a := by
  unfold leftOreValue
  rw [canonicalLeftUniversalHom_source]
  rfl

@[simp] theorem leftOreValue_fraction
    (a : α)
    (s : S) :
    v.leftOreValue
        (OreLocalization.oreDiv a s)
      =
    v.value a -
      v.value (s : α) := by
  unfold leftOreValue
  rw [canonicalLeftUniversalHom_fraction]
  rfl

@[simp] theorem leftOreValue_denominatorInverse
    (s : S) :
    v.leftOreValue
        (canonicalLeftDenominatorInverse
          (α := α) (S := S) s)
      =
    - v.value (s : α) := by
  change
    v.leftOreValue
        (OreLocalization.oreDiv (1 : α) s)
      =
    _
  rw [leftOreValue_fraction]
  rw [v.one_eq_zero]
  omega

/-- Additivity survives on the full left Ore quotient because the extension is
a monoid homomorphism into Multiplicative ℤ. -/
theorem leftOreValue_mul
    (x y :
      CanonicalLeftLocalization
        (α := α) (S := S)) :
    v.leftOreValue (x * y) =
      v.leftOreValue x +
        v.leftOreValue y := by
  unfold leftOreValue
  rw [map_mul]
  rfl

end Left

section Right

variable [OreLocalization.OreSet S.op]

/-- Integer valuation on the canonical right Ore localization. -/
def rightOreValue
    (x :
      CanonicalRightLocalization
        (α := α) (S := S)) :
    ℤ :=
  Multiplicative.toAdd
    (canonicalRightUniversalHom
      (S := S)
      v.toMultiplicativeHom x)

@[simp] theorem rightOreValue_source
    (a : α) :
    v.rightOreValue
        (canonicalRightSourceHom
          (α := α) (S := S) a)
      =
    v.value a := by
  unfold rightOreValue
  rw [canonicalRightUniversalHom_source]
  rfl

@[simp] theorem rightOreValue_fraction
    (a : α)
    (s : S) :
    v.rightOreValue
        (MulOpposite.op
          (OreLocalization.oreDiv
            (MulOpposite.op a)
            (opDenominator s)))
      =
    v.value a -
      v.value (s : α) := by
  unfold rightOreValue
  rw [canonicalRightUniversalHom_fraction]
  rfl

@[simp] theorem rightOreValue_denominatorInverse
    (s : S) :
    v.rightOreValue
        (canonicalRightDenominatorInverse
          (α := α) (S := S) s)
      =
    - v.value (s : α) := by
  change
    v.rightOreValue
      (MulOpposite.op
        (OreLocalization.oreDiv
          (1 : αᵐᵒᵖ)
          (opDenominator s)))
      =
    _
  simpa using
    v.rightOreValue_fraction
      (S := S) (1 : α) s

theorem rightOreValue_mul
    (x y :
      CanonicalRightLocalization
        (α := α) (S := S)) :
    v.rightOreValue (x * y) =
      v.rightOreValue x +
        v.rightOreValue y := by
  unfold rightOreValue
  rw [map_mul]
  rfl

end Right

section Bilateral

variable [OreLocalization.OreSet S]
variable [OreLocalization.OreSet S.op]

/-- Left and right canonical localizations carry exactly the same extended
valuation under the canonical bilateral equivalence. -/
theorem bilateralOreValue_compatible
    (x :
      CanonicalLeftLocalization
        (α := α) (S := S)) :
    v.rightOreValue
        (canonicalBilateralOreEquiv
          (α := α) (S := S) x)
      =
    v.leftOreValue x := by
  -- Both sides are monoid morphisms to the same group and agree on the source.
  let fL :
      CanonicalLeftLocalization
          (α := α) (S := S) →*
        Multiplicative ℤ :=
    canonicalLeftUniversalHom
      (S := S) v.toMultiplicativeHom

  let fR :
      CanonicalLeftLocalization
          (α := α) (S := S) →*
        Multiplicative ℤ :=
    (canonicalRightUniversalHom
      (S := S) v.toMultiplicativeHom).comp
        (canonicalBilateralOreEquiv
          (α := α) (S := S)).toMonoidHom

  have h :
      fL = fR := by
    apply
      canonicalLeftUniversalHom_unique
        (S := S)
        v.toMultiplicativeHom
        fR
    intro a
    simp [fR, fL]

  have hx :=
    DFunLike.congr_fun h x
  exact
    congrArg Multiplicative.toAdd hx.symm

end Bilateral
end MultiplicativeZValuation
end CausalLocalization
end CausalGeometry
