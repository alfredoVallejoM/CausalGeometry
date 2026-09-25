import CausalGeometry.Models.OreBilateralGroup
import CausalGeometry.Number.ResidualLocalizationRealization
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
import Mathlib.Tactic

namespace CausalGeometry.Models

open CausalGeometry.CausalLocalization
open CausalDivisibility

abbrev OrderedIntGroup :=
  Multiplicative ℤ

/-- Ordered group residual: multiplication is integer addition and residual is
integer subtraction. -/
def orderedIntResidual :
    ResiduatedMultiplication OrderedIntGroup where
  leftResidual := fun x z =>
    Multiplicative.ofAdd
      (z.toAdd - x.toAdd)
  rightResidual := fun z x =>
    Multiplicative.ofAdd
      (z.toAdd - x.toAdd)
  leftAdjunction := by
    intro x y z
    change
      x.toAdd + y.toAdd ≤ z.toAdd ↔
        y.toAdd ≤ z.toAdd - x.toAdd
    omega
  rightAdjunction := by
    intro x y z
    change
      y.toAdd + x.toAdd ≤ z.toAdd ↔
        y.toAdd ≤ z.toAdd - x.toAdd
    omega

@[simp] theorem orderedInt_leftResidual_toAdd
    (x z : OrderedIntGroup) :
    (orderedIntResidual.leftResidual x z).toAdd =
      z.toAdd - x.toAdd :=
  rfl

@[simp] theorem orderedInt_rightResidual_toAdd
    (z x : OrderedIntGroup) :
    (orderedIntResidual.rightResidual z x).toAdd =
      z.toAdd - x.toAdd :=
  rfl

/-- Every target is left divisible by every denominator in a group. -/
theorem orderedInt_leftDivides_all
    (s z : OrderedIntGroup) :
    LeftDivides s z := by
  refine ⟨s⁻¹ * z, ?_⟩
  simp [mul_assoc]

/-- And symmetrically on the right. -/
theorem orderedInt_rightDivides_all
    (s z : OrderedIntGroup) :
    RightDivides s z := by
  refine ⟨z * s⁻¹, ?_⟩
  simp [mul_assoc]

abbrev OrderedIntRightCalculus :=
  rightGroupCalculus
    (G := OrderedIntGroup)

/-- Source inclusion into the certified group localization is faithful. -/
theorem orderedInt_sourceFaithful :
    OrderedIntRightCalculus.SourceFaithful := by
  intro a b h
  have h' :=
    congrArg
      (RightGroupCalculus.quotientEquivGroup
        (G := OrderedIntGroup))
      h
  simpa using h'

/-- In a group every target belongs to the left-divisible admissible locus, so
the partial residual/localization comparison promotes to global compatibility. -/
def orderedInt_leftResidualGlobal
    (s : (⊤ : Submonoid OrderedIntGroup)) :
    PairedRealizationCompatibility
      OrderedIntRightCalculus.sourceRealization
      OrderedIntRightCalculus.sourceRealization
      (orderedIntResidual.leftPairedTransform
        (s : OrderedIntGroup))
      (OrderedIntRightCalculus.leftDenominatorPair s) :=
  (OrderedIntRightCalculus.leftResidualRealization
      orderedIntResidual s).toGlobal
    (fun z =>
      orderedInt_leftDivides_all
        (s : OrderedIntGroup) z)

/-- Same global promotion for the right residual. -/
def orderedInt_rightResidualGlobal
    (s : (⊤ : Submonoid OrderedIntGroup)) :
    PairedRealizationCompatibility
      OrderedIntRightCalculus.sourceRealization
      OrderedIntRightCalculus.sourceRealization
      (orderedIntResidual.rightPairedTransform
        (s : OrderedIntGroup))
      (OrderedIntRightCalculus.rightDenominatorPair s) :=
  (OrderedIntRightCalculus.rightResidualRealization
      orderedIntResidual s).toGlobal
    (fun z =>
      orderedInt_rightDivides_all
        (s : OrderedIntGroup) z)

/-- Concrete arithmetic regression: 3\8 = 5 in the multiplicative-tagged
integer group. -/
theorem orderedInt_residual_example :
    (orderedIntResidual.leftResidual
      (Multiplicative.ofAdd (3 : ℤ))
      (Multiplicative.ofAdd (8 : ℤ))).toAdd =
      5 := by
  norm_num

/-- The same example is represented exactly by inverse-denominator
multiplication in the fraction quotient. -/
theorem orderedInt_localization_example :
    let s :
        (⊤ : Submonoid OrderedIntGroup) :=
      ⟨Multiplicative.ofAdd (3 : ℤ), by simp⟩
    OrderedIntRightCalculus.denominatorInverse s *
        OrderedIntRightCalculus.sourceHom
          (Multiplicative.ofAdd (8 : ℤ)) =
      OrderedIntRightCalculus.sourceHom
        (Multiplicative.ofAdd (5 : ℤ)) := by
  intro s
  have hdiv :
      LeftDivides
        (s : OrderedIntGroup)
        (Multiplicative.ofAdd (8 : ℤ)) :=
    orderedInt_leftDivides_all
      (s : OrderedIntGroup)
      (Multiplicative.ofAdd (8 : ℤ))
  have h :=
    OrderedIntRightCalculus.leftDivides_localizes
      orderedIntResidual s
      (Multiplicative.ofAdd (8 : ℤ))
      hdiv
  simpa using h

/-- Faithfulness detects exact divisibility through backward-square
commutation; in this group control the condition is always true. -/
theorem orderedInt_backward_square_global
    (s : (⊤ : Submonoid OrderedIntGroup))
    (z : OrderedIntGroup) :
    OrderedIntRightCalculus.sourceHom
        (orderedIntResidual.leftResidual
          (s : OrderedIntGroup) z) =
      OrderedIntRightCalculus.denominatorInverse s *
        OrderedIntRightCalculus.sourceHom z := by
  exact
    (OrderedIntRightCalculus.leftBackward_compat_of_divides
      orderedIntResidual s z
      (orderedInt_leftDivides_all
        (s : OrderedIntGroup) z))

end CausalGeometry.Models
