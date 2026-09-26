import CausalGeometry.Number.CommutativeLocalizationUniversal
import CausalGeometry.Number.CentralOreMathlib
import CausalGeometry.Number.BilateralOreMathlib
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [CancelCommMonoid α]
variable {S : Submonoid α}

/-- Every denominator system is central in a commutative monoid. -/
def commutativeCentralDenominators :
    CentralDenominators S := by
  intro s a
  exact mul_comm (s : α) a

/-- Canonical OreSet selected for the commutative comparison file. -/
noncomputable def commutativeLeftOreSet :
    OreLocalization.OreSet S :=
  (commutativeCentralDenominators
    (α := α) (S := S)).toMathlibOreSet

/-- Canonical opposite OreSet used by the right-handed comparison. -/
noncomputable def commutativeRightOreSet :
    OreLocalization.OreSet S.op :=
  (commutativeCentralDenominators
    (α := α) (S := S)).toOppositeMathlibOreSet

local instance commutativeLeftOreSetInst :
    OreLocalization.OreSet S :=
  commutativeLeftOreSet (α := α) (S := S)

local instance commutativeRightOreSetInst :
    OreLocalization.OreSet S.op :=
  commutativeRightOreSet (α := α) (S := S)

/-- The cross-multiplication quotient maps canonically into the left Ore
localization. -/
def commFractionToCanonicalLeft :
    CommFraction S →
      CanonicalLeftLocalization
        (α := α) (S := S) :=
  Quotient.lift
    (fun x =>
      OreLocalization.oreDiv
        x.numerator x.denominator)
    (by
      intro x y hxy
      rw [OreLocalization.oreDiv_eq_iff]
      refine
        ⟨x.denominator,
          (y.denominator : α),
          ?_, ?_⟩
      · change
          (x.denominator : α) * y.numerator =
            (y.denominator : α) * x.numerator
        calc
          (x.denominator : α) * y.numerator
              =
            y.numerator * (x.denominator : α) :=
              mul_comm _ _
          _ =
            x.numerator * (y.denominator : α) :=
              hxy.symm
          _ =
            (y.denominator : α) * x.numerator :=
              mul_comm _ _
      · exact mul_comm _ _)

/-- The previous map is multiplicative. -/
def commFractionToCanonicalLeftHom :
    CommFraction S →*
      CanonicalLeftLocalization
        (α := α) (S := S) where
  toFun :=
    commFractionToCanonicalLeft
      (α := α) (S := S)
  map_one' := by
    change
      OreLocalization.oreDiv
          (1 : α) (1 : S) =
        1
    rfl
  map_mul' := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro x
    rcases x with ⟨a, s⟩
    refine Quotient.inductionOn y ?_
    intro y
    rcases y with ⟨b, t⟩
    change
      OreLocalization.oreDiv
          (a * b) (s * t)
        =
      OreLocalization.oreDiv a s *
        OreLocalization.oreDiv b t
    rw [
      OreLocalization.oreDiv_mul_char
        a b s t a t
        (by simp [mul_comm])
    ]
    congr 1
    exact mul_comm t s

/-- Selected denominator as a unit in the commutative fraction quotient. -/
def commFractionDenominatorUnit
    (s : S) :
    (CommFraction S)ˣ where
  val :=
    CommFraction.ofElement (s : α)
  inv :=
    CommFraction.denominatorInverse s
  val_inv := by
    exact CommFraction.denominator_mul_inverse s
  inv_val := by
    exact CommFraction.inverse_mul_denominator s

def commFractionDenominatorUnitsHom :
    S →* (CommFraction S)ˣ where
  toFun :=
    commFractionDenominatorUnit
      (α := α) (S := S)
  map_one' := by
    apply Units.ext
    rfl
  map_mul' := by
    intro s t
    apply Units.ext
    rfl

@[simp] theorem commFractionDenominatorUnitsHom_val
    (s : S) :
    ((commFractionDenominatorUnitsHom
        (α := α) (S := S) s :
      (CommFraction S)ˣ) :
      CommFraction S)
      =
    CommFraction.ofElement (s : α) :=
  rfl

/-- Universal map in the reverse direction, from the canonical Ore quotient
to the pre-existing commutative fraction quotient. -/
def canonicalLeftToCommFraction :
    CanonicalLeftLocalization
        (α := α) (S := S) →*
      CommFraction S :=
  OreLocalization.universalMulHom
    (CommFraction.ofElementHom
      (α := α) (S := S))
    (commFractionDenominatorUnitsHom
      (α := α) (S := S))
    (by intro s; rfl)

@[simp] theorem canonicalLeftToCommFraction_source
    (a : α) :
    canonicalLeftToCommFraction
        (α := α) (S := S)
        (canonicalLeftSourceHom
          (α := α) (S := S) a)
      =
    CommFraction.ofElement a := by
  exact
    OreLocalization.universalMulHom_commutes
      (CommFraction.ofElementHom
        (α := α) (S := S))
      (commFractionDenominatorUnitsHom
        (α := α) (S := S))
      (by intro s; rfl)

/-- The composite on CommFraction is identity, checked on raw fraction
presentations. -/
theorem canonicalLeftToCommFraction_comp_commFractionToCanonicalLeft :
    (canonicalLeftToCommFraction
        (α := α) (S := S)).comp
      (commFractionToCanonicalLeftHom
        (α := α) (S := S))
      =
    MonoidHom.id (CommFraction S) := by
  apply MonoidHom.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro q
  rcases q with ⟨a, s⟩
  change
    canonicalLeftToCommFraction
        (α := α) (S := S)
        (OreLocalization.oreDiv a s)
      =
    CommFraction.mk a s
  rw [OreLocalization.universalMulHom_apply]
  change
    (commFractionDenominatorUnit
          (α := α) (S := S) s)⁻¹ *
        CommFraction.ofElement a
      =
    CommFraction.mk a s
  change
    CommFraction.denominatorInverse s *
        CommFraction.ofElement a
      =
    CommFraction.mk a s
  rw [mul_comm]
  exact
    (CommFraction.mk_eq_ofElement_mul_denominatorInverse
      a s).symm

/-- The composite on the canonical Ore localization is identity by its
universal uniqueness theorem. -/
theorem commFractionToCanonicalLeft_comp_canonicalLeftToCommFraction :
    (commFractionToCanonicalLeftHom
        (α := α) (S := S)).comp
      (canonicalLeftToCommFraction
        (α := α) (S := S))
      =
    MonoidHom.id
      (CanonicalLeftLocalization
        (α := α) (S := S)) := by

  let f :=
    canonicalLeftSourceHom
      (α := α) (S := S)

  let u :=
    canonicalLeftDenominatorUnitsHom
      (α := α) (S := S)

  have hcomp :
      (commFractionToCanonicalLeftHom
          (α := α) (S := S)).comp
        (canonicalLeftToCommFraction
          (α := α) (S := S))
        =
      OreLocalization.universalMulHom
        f u (by intro s; rfl) := by
    apply
      OreLocalization.universalMulHom_unique
        f u (by intro s; rfl)
    intro a
    rfl

  have hid :
      MonoidHom.id
          (CanonicalLeftLocalization
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

/-- Canonical equivalence between the original cancellative commutative
fraction quotient and the new canonical left Ore localization. -/
noncomputable def commFractionEquivCanonicalLeft :
    CommFraction S ≃*
      CanonicalLeftLocalization
        (α := α) (S := S) where
  toFun :=
    commFractionToCanonicalLeftHom
      (α := α) (S := S)
  invFun :=
    canonicalLeftToCommFraction
      (α := α) (S := S)
  left_inv := by
    intro x
    exact
      DFunLike.congr_fun
        (canonicalLeftToCommFraction_comp_commFractionToCanonicalLeft
          (α := α) (S := S))
        x
  right_inv := by
    intro x
    exact
      DFunLike.congr_fun
        (commFractionToCanonicalLeft_comp_canonicalLeftToCommFraction
          (α := α) (S := S))
        x
  map_mul' := by
    intro x y
    exact map_mul _ x y

/-- The right canonical Ore localization is therefore equivalent to the same
classical CommFraction quotient. -/
noncomputable def commFractionEquivCanonicalRight :
    CommFraction S ≃*
      CanonicalRightLocalization
        (α := α) (S := S) :=
  (commFractionEquivCanonicalLeft
      (α := α) (S := S)).trans
    (canonicalBilateralOreEquiv
      (α := α) (S := S))

@[simp] theorem commFractionEquivCanonicalLeft_mk
    (a : α) (s : S) :
    commFractionEquivCanonicalLeft
        (α := α) (S := S)
        (CommFraction.mk a s)
      =
    OreLocalization.oreDiv a s :=
  rfl

@[simp] theorem commFractionEquivCanonicalRight_ofElement
    (a : α) :
    commFractionEquivCanonicalRight
        (α := α) (S := S)
        (CommFraction.ofElement a)
      =
    canonicalRightSourceHom
      (α := α) (S := S) a := by
  simp [commFractionEquivCanonicalRight,
    CommFraction.ofElement,
    commFractionEquivCanonicalLeft]

end CausalLocalization
end CausalGeometry
