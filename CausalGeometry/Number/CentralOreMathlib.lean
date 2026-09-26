import CausalGeometry.Number.CentralOre
import CausalGeometry.Number.MathlibRightOreBridge

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

/-- Central selected denominators satisfy the full mathlib left OreSet
hypothesis in an arbitrary monoid.

Centrality supplies both ingredients:
* the Ore square;
* reversibility, because from a*s=b*s one gets s*a=s*b by commuting the
  selected denominator across both source elements.

No cancellation assumption on the ambient monoid is needed. -/
def CentralDenominators.toMathlibOreSet
    (hS : CentralDenominators S) :
    OreLocalization.OreSet S where

  ore_right_cancel := by
    intro r₁ r₂ s h
    refine ⟨s, ?_⟩
    calc
      (s : α) * r₁ = r₁ * (s : α) :=
        (hS s r₁).eq
      _ = r₂ * (s : α) := h
      _ = (s : α) * r₂ :=
        (hS s r₂).eq.symm

  oreNum := fun r _ => r

  oreDenom := fun _ s => s

  ore_eq := by
    intro r s
    exact (hS s r).eq

/-- Centrality transports to the opposite denominator system. -/
def CentralDenominators.op
    (hS : CentralDenominators S) :
    CentralDenominators S.op := by
  intro s a
  have h :=
    hS (unopDenominator s)
      (MulOpposite.unop a)
  change
    (s : αᵐᵒᵖ) * a =
      a * (s : αᵐᵒᵖ)
  have hop := congrArg MulOpposite.op h.eq
  simpa [unopDenominator] using hop

/-- Hence the same central sector also satisfies the opposite OreSet needed
by the canonical right localization. -/
def CentralDenominators.toOppositeMathlibOreSet
    (hS : CentralDenominators S) :
    OreLocalization.OreSet S.op :=
  hS.op.toMathlibOreSet

/-- With the promoted OreSet, the generic mathlib left square reduces to the
expected central square at the equation level. -/
theorem central_mathlib_left_cross
    (hS : CentralDenominators S)
    (a : α) (s : S) :
    letI : OreLocalization.OreSet S :=
      hS.toMathlibOreSet
    (mathlibLeftOreSquare
      (S := S) a s).cross =
      (hS.leftSquare a s).cross := by
  rfl

/-- The promoted left localization uses the expected unchanged numerator and
denominator choices in the central sector. -/
theorem central_mathlib_left_numerator
    (hS : CentralDenominators S)
    (a : α) (s : S) :
    letI : OreLocalization.OreSet S :=
      hS.toMathlibOreSet
    (mathlibLeftOreSquare
      (S := S) a s).numerator = a := by
  rfl

theorem central_mathlib_left_denominator
    (hS : CentralDenominators S)
    (a : α) (s : S) :
    letI : OreLocalization.OreSet S :=
      hS.toMathlibOreSet
    (mathlibLeftOreSquare
      (S := S) a s).denominator = s := by
  rfl

/-- The same statement for the right square after passage through the
opposite monoid. -/
theorem central_mathlib_right_numerator
    (hS : CentralDenominators S)
    (a : α) (s : S) :
    letI : OreLocalization.OreSet S.op :=
      hS.toOppositeMathlibOreSet
    (mathlibRightOreSquare
      (S := S) a s).numerator = a := by
  rfl

theorem central_mathlib_right_denominator
    (hS : CentralDenominators S)
    (a : α) (s : S) :
    letI : OreLocalization.OreSet S.op :=
      hS.toOppositeMathlibOreSet
    (mathlibRightOreSquare
      (S := S) a s).denominator = s := by
  apply Subtype.ext
  rfl

end CausalLocalization
end CausalGeometry
