import CausalGeometry.Number.MathlibRightOreBridge
import Mathlib.Algebra.Group.Units.Hom

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

section Bilateral

variable [OreLocalization.OreSet S]
variable [OreLocalization.OreSet S.op]

abbrev CanonicalLeftLoc :=
  CanonicalLeftLocalization (α := α) (S := S)

abbrev CanonicalRightLoc :=
  CanonicalRightLocalization (α := α) (S := S)

/-- Explicit denominator unit in the canonical left localization. -/
def canonicalLeftDenominatorUnit
    (s : S) :
    CanonicalLeftLoc (α := α) (S := S)ˣ where
  val :=
    canonicalLeftSourceHom
      (α := α) (S := S) (s : α)
  inv :=
    canonicalLeftDenominatorInverse
      (α := α) (S := S) s
  val_inv := by
    exact
      canonical_source_mul_denominatorInverse
        (α := α) (S := S) s
  inv_val := by
    exact
      canonical_denominatorInverse_mul_source
        (α := α) (S := S) s

/-- Denominator units bundle multiplicatively. -/
def canonicalLeftDenominatorUnitsHom :
    S →*
      CanonicalLeftLoc (α := α) (S := S)ˣ where
  toFun := canonicalLeftDenominatorUnit
  map_one' := by
    apply Units.ext
    simp [canonicalLeftDenominatorUnit,
      canonicalLeftSourceHom]
  map_mul' := by
    intro s t
    apply Units.ext
    simp [canonicalLeftDenominatorUnit,
      canonicalLeftSourceHom]

@[simp] theorem canonicalLeftDenominatorUnitsHom_val
    (s : S) :
    ((canonicalLeftDenominatorUnitsHom
        (α := α) (S := S) s :
      CanonicalLeftLoc (α := α) (S := S)ˣ) :
        CanonicalLeftLoc (α := α) (S := S))
      =
    canonicalLeftSourceHom
      (α := α) (S := S) (s : α) :=
  rfl

/-- Explicit denominator unit in the canonical right localization. -/
def canonicalRightDenominatorUnit
    (s : S) :
    CanonicalRightLoc (α := α) (S := S)ˣ where
  val :=
    canonicalRightSourceHom
      (α := α) (S := S) (s : α)
  inv :=
    canonicalRightDenominatorInverse
      (α := α) (S := S) s
  val_inv := by
    exact
      canonicalRight_source_mul_denominatorInverse
        (α := α) (S := S) s
  inv_val := by
    exact
      canonicalRight_denominatorInverse_mul_source
        (α := α) (S := S) s

def canonicalRightDenominatorUnitsHom :
    S →*
      CanonicalRightLoc (α := α) (S := S)ˣ where
  toFun := canonicalRightDenominatorUnit
  map_one' := by
    apply Units.ext
    simp [canonicalRightDenominatorUnit,
      canonicalRightSourceHom]
  map_mul' := by
    intro s t
    apply Units.ext
    simp [canonicalRightDenominatorUnit,
      canonicalRightSourceHom]

@[simp] theorem canonicalRightDenominatorUnitsHom_val
    (s : S) :
    ((canonicalRightDenominatorUnitsHom
        (α := α) (S := S) s :
      CanonicalRightLoc (α := α) (S := S)ˣ) :
        CanonicalRightLoc (α := α) (S := S))
      =
    canonicalRightSourceHom
      (α := α) (S := S) (s : α) :=
  rfl

/-- Universal map from the canonical left localization to the canonical right
localization. -/
def canonicalLeftToRight :
    CanonicalLeftLoc (α := α) (S := S) →*
      CanonicalRightLoc (α := α) (S := S) :=
  OreLocalization.universalMulHom
    (canonicalRightSourceHom
      (α := α) (S := S))
    (canonicalRightDenominatorUnitsHom
      (α := α) (S := S))
    (by intro s; rfl)

@[simp] theorem canonicalLeftToRight_source
    (a : α) :
    canonicalLeftToRight
        (α := α) (S := S)
        (canonicalLeftSourceHom
          (α := α) (S := S) a)
      =
    canonicalRightSourceHom
      (α := α) (S := S) a := by
  exact
    OreLocalization.universalMulHom_commutes
      (canonicalRightSourceHom
        (α := α) (S := S))
      (canonicalRightDenominatorUnitsHom
        (α := α) (S := S))
      (by intro s; rfl)

/-- Opposite of the canonical left source map, used to consume the opposite
Ore localization underlying the canonical right localization. -/
def canonicalLeftOppSourceHom :
    αᵐᵒᵖ →*
      (CanonicalLeftLoc
        (α := α) (S := S))ᵐᵒᵖ where
  toFun := fun a =>
    MulOpposite.op
      (canonicalLeftSourceHom
        (α := α) (S := S)
        (MulOpposite.unop a))
  map_one' := by simp
  map_mul' := by
    intro a b
    simp

/-- Opposite-unit conversion. -/
def opUnit
    {M : Type*} [Monoid M]
    (u : Mˣ) :
    (Mᵐᵒᵖ)ˣ where
  val := MulOpposite.op (u : M)
  inv := MulOpposite.op ((↑u⁻¹ : M))
  val_inv := by
    change
      MulOpposite.op
          ((↑u⁻¹ : M) * (u : M))
        =
      1
    rw [Units.inv_mul]
    rfl
  inv_val := by
    change
      MulOpposite.op
          ((u : M) * (↑u⁻¹ : M))
        =
      1
    rw [Units.mul_inv]
    rfl

/-- Denominator-unit homomorphism for the opposite target. -/
def canonicalLeftOppDenominatorUnitsHom :
    S.op →*
      ((CanonicalLeftLoc
        (α := α) (S := S))ᵐᵒᵖ)ˣ where
  toFun := fun s =>
    opUnit
      (canonicalLeftDenominatorUnit
        (α := α) (S := S)
        (unopDenominator s))
  map_one' := by
    apply Units.ext
    simp [opUnit, canonicalLeftDenominatorUnit,
      unopDenominator, canonicalLeftSourceHom]
  map_mul' := by
    intro s t
    apply Units.ext
    simp [opUnit, canonicalLeftDenominatorUnit,
      unopDenominator, canonicalLeftSourceHom]

@[simp] theorem canonicalLeftOppDenominatorUnitsHom_val
    (s : S.op) :
    ((canonicalLeftOppDenominatorUnitsHom
        (α := α) (S := S) s :
      ((CanonicalLeftLoc
        (α := α) (S := S))ᵐᵒᵖ)ˣ) :
      (CanonicalLeftLoc
        (α := α) (S := S))ᵐᵒᵖ)
      =
    canonicalLeftOppSourceHom
      (α := α) (S := S) (s : αᵐᵒᵖ) := by
  apply congrArg MulOpposite.op
  simp [canonicalLeftOppDenominatorUnitsHom,
    opUnit, canonicalLeftOppSourceHom,
    canonicalLeftDenominatorUnit,
    unopDenominator]

/-- Universal lift on the non-opposite carrier underlying the right
localization. -/
def canonicalRightUnderlyingToLeftOpp :
    OreLocalization S.op αᵐᵒᵖ →*
      (CanonicalLeftLoc
        (α := α) (S := S))ᵐᵒᵖ :=
  OreLocalization.universalMulHom
    (canonicalLeftOppSourceHom
      (α := α) (S := S))
    (canonicalLeftOppDenominatorUnitsHom
      (α := α) (S := S))
    (by
      intro s
      exact
        (canonicalLeftOppDenominatorUnitsHom_val
          (α := α) (S := S) s).symm)

/-- Universal map from the canonical right localization back to the left one. -/
def canonicalRightToLeft :
    CanonicalRightLoc (α := α) (S := S) →*
      CanonicalLeftLoc (α := α) (S := S) where
  toFun := fun q =>
    MulOpposite.unop
      (canonicalRightUnderlyingToLeftOpp
        (α := α) (S := S)
        (MulOpposite.unop q))
  map_one' := by
    simp [canonicalRightUnderlyingToLeftOpp]
  map_mul' := by
    intro x y
    simp [canonicalRightUnderlyingToLeftOpp]

@[simp] theorem canonicalRightToLeft_source
    (a : α) :
    canonicalRightToLeft
        (α := α) (S := S)
        (canonicalRightSourceHom
          (α := α) (S := S) a)
      =
    canonicalLeftSourceHom
      (α := α) (S := S) a := by
  change
    MulOpposite.unop
      (canonicalRightUnderlyingToLeftOpp
        (α := α) (S := S)
        (OreLocalization.numeratorHom
          (MulOpposite.op a)))
      =
    _
  rw [OreLocalization.universalMulHom_commutes]
  rfl

@[simp] theorem canonicalLeftToRight_denominatorInverse
    (s : S) :
    canonicalLeftToRight
        (α := α) (S := S)
        (canonicalLeftDenominatorInverse
          (α := α) (S := S) s)
      =
    canonicalRightDenominatorInverse
      (α := α) (S := S) s := by
  change
    OreLocalization.universalMulHom
        (canonicalRightSourceHom
          (α := α) (S := S))
        (canonicalRightDenominatorUnitsHom
          (α := α) (S := S))
        (by intro t; rfl)
        (OreLocalization.oreDiv (1 : α) s)
      =
    _
  rw [OreLocalization.universalMulHom_apply]
  simp [canonicalRightDenominatorUnitsHom,
    canonicalRightDenominatorUnit]

@[simp] theorem canonicalRightToLeft_denominatorInverse
    (s : S) :
    canonicalRightToLeft
        (α := α) (S := S)
        (canonicalRightDenominatorInverse
          (α := α) (S := S) s)
      =
    canonicalLeftDenominatorInverse
      (α := α) (S := S) s := by
  change
    MulOpposite.unop
      (canonicalRightUnderlyingToLeftOpp
        (α := α) (S := S)
        (OreLocalization.oreDiv
          (1 : αᵐᵒᵖ)
          (opDenominator s)))
      =
    _
  rw [OreLocalization.universalMulHom_apply]
  simp [canonicalLeftOppDenominatorUnitsHom,
    canonicalLeftDenominatorUnit,
    opUnit,
    canonicalLeftDenominatorInverse,
    unopDenominator]

/-- Both composites out of the left localization are the identity by universal
uniqueness. -/
theorem canonicalRightToLeft_comp_leftToRight :
    (canonicalRightToLeft
        (α := α) (S := S)).comp
      (canonicalLeftToRight
        (α := α) (S := S))
      =
    MonoidHom.id
      (CanonicalLeftLoc
        (α := α) (S := S)) := by
  let f :=
    canonicalLeftSourceHom
      (α := α) (S := S)
  let u :=
    canonicalLeftDenominatorUnitsHom
      (α := α) (S := S)

  have hcomp :
      (canonicalRightToLeft
          (α := α) (S := S)).comp
        (canonicalLeftToRight
          (α := α) (S := S))
        =
      OreLocalization.universalMulHom
        f u (by intro s; rfl) := by
    apply
      OreLocalization.universalMulHom_unique
        f u (by intro s; rfl)
    intro a
    simp [f]

  have hid :
      MonoidHom.id
          (CanonicalLeftLoc
            (α := α) (S := S))
        =
      OreLocalization.universalMulHom
        f u (by intro s; rfl) := by
    apply
      OreLocalization.universalMulHom_unique
        f u (by intro s; rfl)
    intro a
    rfl

  exact hcomp.trans hid.symm

/-- Turn a right-localization endomorphism into an endomorphism of the
underlying opposite-side Ore localization. -/
def rightEndUnderlying
    (φ :
      CanonicalRightLoc
        (α := α) (S := S) →*
      CanonicalRightLoc
        (α := α) (S := S)) :
    OreLocalization S.op αᵐᵒᵖ →*
      OreLocalization S.op αᵐᵒᵖ where
  toFun := fun q =>
    MulOpposite.unop
      (φ (MulOpposite.op q))
  map_one' := by simp
  map_mul' := by
    intro x y
    simp

/-- A right-localization endomorphism is determined by its values on the
original source.

The proof does not assume cancellation in the localization.  It transports
both endomorphisms to the underlying left Ore localization of the opposite
monoid and applies the universal property there. -/
theorem canonicalRight_end_ext_source
    (φ ψ :
      CanonicalRightLoc
        (α := α) (S := S) →*
      CanonicalRightLoc
        (α := α) (S := S))
    (hsource :
      ∀ a : α,
        φ (canonicalRightSourceHom
          (α := α) (S := S) a)
          =
        ψ (canonicalRightSourceHom
          (α := α) (S := S) a)) :
    φ = ψ := by

  let O :=
    OreLocalization S.op αᵐᵒᵖ

  let φu :
      O →* O :=
    rightEndUnderlying
      (α := α) (S := S) φ

  let ψu :
      O →* O :=
    rightEndUnderlying
      (α := α) (S := S) ψ

  let f :
      αᵐᵒᵖ →* O :=
    φu.comp OreLocalization.numeratorHom

  let baseUnits :
      S.op →* Oˣ :=
    canonicalLeftDenominatorUnitsHom
      (α := αᵐᵒᵖ) (S := S.op)

  let mappedUnits :
      S.op →* Oˣ :=
    (Units.map φu).comp baseUnits

  have hf :
      ∀ s : S.op,
        f (s : αᵐᵒᵖ) =
          (mappedUnits s : O) := by
    intro s
    rfl

  have hφ :
      φu =
        OreLocalization.universalMulHom
          f mappedUnits hf := by
    apply
      OreLocalization.universalMulHom_unique
        f mappedUnits hf
    intro a
    rfl

  have hψsource :
      ∀ a : αᵐᵒᵖ,
        ψu (OreLocalization.numeratorHom a) =
          f a := by
    intro a
    change
      MulOpposite.unop
        (ψ
          (canonicalRightSourceHom
            (α := α) (S := S)
            (MulOpposite.unop a)))
        =
      MulOpposite.unop
        (φ
          (canonicalRightSourceHom
            (α := α) (S := S)
            (MulOpposite.unop a)))
    exact
      congrArg MulOpposite.unop
        (hsource (MulOpposite.unop a)).symm

  have hψ :
      ψu =
        OreLocalization.universalMulHom
          f mappedUnits hf := by
    apply
      OreLocalization.universalMulHom_unique
        f mappedUnits hf
    exact hψsource

  apply MonoidHom.ext
  intro q
  have h :=
    DFunLike.congr_fun
      (hφ.trans hψ.symm)
      (MulOpposite.unop q)
  have hop := congrArg MulOpposite.op h
  simpa [φu, ψu, rightEndUnderlying] using hop

theorem canonicalLeftToRight_comp_rightToLeft :
    (canonicalLeftToRight
        (α := α) (S := S)).comp
      (canonicalRightToLeft
        (α := α) (S := S))
      =
    MonoidHom.id
      (CanonicalRightLoc
        (α := α) (S := S)) := by
  apply
    canonicalRight_end_ext_source
      (α := α) (S := S)
  intro a
  simp

/-- Canonical equivalence of the left and right Ore presentations whenever the
two OreSet hypotheses are simultaneously available. -/
def canonicalBilateralOreEquiv :
    CanonicalLeftLoc (α := α) (S := S) ≃*
      CanonicalRightLoc (α := α) (S := S) where
  toFun :=
    canonicalLeftToRight
      (α := α) (S := S)
  invFun :=
    canonicalRightToLeft
      (α := α) (S := S)
  left_inv := by
    intro x
    have h :=
      DFunLike.congr_fun
        (canonicalRightToLeft_comp_leftToRight
          (α := α) (S := S))
        x
    exact h
  right_inv := by
    intro x
    have h :=
      DFunLike.congr_fun
        (canonicalLeftToRight_comp_rightToLeft
          (α := α) (S := S))
        x
    exact h
  map_mul' := by
    intro x y
    exact map_mul _ x y

@[simp] theorem canonicalBilateralOreEquiv_source
    (a : α) :
    canonicalBilateralOreEquiv
        (α := α) (S := S)
        (canonicalLeftSourceHom
          (α := α) (S := S) a)
      =
    canonicalRightSourceHom
      (α := α) (S := S) a :=
  canonicalLeftToRight_source
    (α := α) (S := S) a

@[simp] theorem canonicalBilateralOreEquiv_denominatorInverse
    (s : S) :
    canonicalBilateralOreEquiv
        (α := α) (S := S)
        (canonicalLeftDenominatorInverse
          (α := α) (S := S) s)
      =
    canonicalRightDenominatorInverse
      (α := α) (S := S) s :=
  canonicalLeftToRight_denominatorInverse
    (α := α) (S := S) s

end Bilateral
end CausalLocalization
end CausalGeometry
