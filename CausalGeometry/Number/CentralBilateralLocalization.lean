import CausalGeometry.Number.BilateralLocalization
import CausalGeometry.Number.CentralFractionCalculus

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [CancelMonoid α]
variable {S : Submonoid α}
variable (hS : CentralDenominators S)

abbrev CentralRightCalculus :=
  centralRightFractionCalculus hS

abbrev CentralLeftCalculus :=
  centralLeftFractionCalculus hS

/-- Raw right/left presentations are the same numerator-denominator data with
opposite field order. -/
def centralPresentationEquiv :
    RightFraction S ≃ LeftFraction S where
  toFun := fun x =>
    ⟨x.denominator, x.numerator⟩
  invFun := fun x =>
    ⟨x.numerator, x.denominator⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

@[simp] theorem centralPresentationEquiv_denominator
    (x : RightFraction S) :
    (centralPresentationEquiv
      (S := S) x).denominator =
      x.denominator := rfl

@[simp] theorem centralPresentationEquiv_numerator
    (x : RightFraction S) :
    (centralPresentationEquiv
      (S := S) x).numerator =
      x.numerator := rfl

/-- The cross relation is literally preserved by the presentation swap. -/
theorem centralPresentationEquiv_rel
    {x y : RightFraction S} :
    centralLeftRel
        (centralPresentationEquiv
          (S := S) x)
        (centralPresentationEquiv
          (S := S) y) ↔
      centralRightRel x y :=
  Iff.rfl

namespace CentralBilateral

abbrev R :=
  CentralRightCalculus hS

abbrev L :=
  CentralLeftCalculus hS

/-- Quotient map from right to left presentations. -/
def toLeft :
    R.QuotientType →
      L.QuotientType :=
  Quotient.map
    (centralPresentationEquiv
      (S := S))
    (by
      intro x y h
      exact h)

/-- Quotient map from left back to right. -/
def toRight :
    L.QuotientType →
      R.QuotientType :=
  Quotient.map
    (centralPresentationEquiv
      (S := S)).symm
    (by
      intro x y h
      exact h)

@[simp] theorem toLeft_mk
    (x : RightFraction S) :
    toLeft hS (R.mk x) =
      L.mk
        (centralPresentationEquiv
          (S := S) x) := rfl

@[simp] theorem toRight_mk
    (x : LeftFraction S) :
    toRight hS (L.mk x) =
      R.mk
        ((centralPresentationEquiv
          (S := S)).symm x) := rfl

theorem toLeft_toRight
    (x : L.QuotientType) :
    toLeft hS (toRight hS x) = x := by
  refine Quotient.inductionOn x ?_
  intro x
  rfl

theorem toRight_toLeft
    (x : R.QuotientType) :
    toRight hS (toLeft hS x) = x := by
  refine Quotient.inductionOn x ?_
  intro x
  rfl

/-- Presentation swap commutes exactly with the chosen representative
multiplication. -/
theorem presentation_mul
    (x y : RightFraction S) :
    centralPresentationEquiv
        (S := S)
        (centralRightMulRep x y) =
      centralLeftMulRep
        (centralPresentationEquiv
          (S := S) x)
        (centralPresentationEquiv
          (S := S) y) := by
  rfl

/-- Multiplication is preserved on quotient classes. -/
theorem toLeft_mul
    (x y : R.QuotientType) :
    toLeft hS (x * y) =
      toLeft hS x * toLeft hS y := by
  refine Quotient.inductionOn x ?_
  intro x
  refine Quotient.inductionOn y ?_
  intro y
  rfl

@[simp] theorem toLeft_one :
    toLeft hS (1 : R.QuotientType) =
      (1 : L.QuotientType) := by
  rfl

/-- Canonical multiplicative equivalence between right and left central
localizations. -/
def mulEquiv :
    R.QuotientType ≃*
      L.QuotientType where
  toFun := toLeft hS
  invFun := toRight hS
  left_inv := toRight_toLeft hS
  right_inv := toLeft_toRight hS
  map_mul' := toLeft_mul hS

@[simp] theorem mulEquiv_source
    (a : α) :
    mulEquiv hS (R.sourceHom a) =
      L.sourceHom a := by
  rfl

@[simp] theorem mulEquiv_denominatorInverse
    (s : S) :
    mulEquiv hS
        (R.denominatorInverse s) =
      L.denominatorInverse s := by
  rfl

end CentralBilateral

/-- Full bilateral localization comparison for a central denominator system in
a cancelative noncommutative monoid. -/
def centralBilateralComparison :
    BilateralFractionComparison
      (CentralRightCalculus hS)
      (CentralLeftCalculus hS) where
  equivalence :=
    CentralBilateral.mulEquiv hS
  source_compat :=
    CentralBilateral.mulEquiv_source hS
  denominator_compat :=
    CentralBilateral.mulEquiv_denominatorInverse hS

end CausalLocalization
end CausalGeometry
