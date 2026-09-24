import CausalGeometry.Calculus.Difference
import CausalGeometry.History.Trace
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Inclusion-exclusion variation around a flat concurrency diamond. It measures
the interaction between two causal directions without identifying it with an
error term. -/
def causalSquareVariation {A : Type w} [AddCommGroup A]
    (F : Configuration S → A)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : A :=
  F d.afterEF - F d.afterE - F d.afterF + F C

@[simp] theorem causalSquareVariation_const {A : Type w} [AddCommGroup A]
    (a : A) {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    causalSquareVariation (fun _ => a) d = 0 := by
  simp [causalSquareVariation]


/-- Swapping the two concurrent directions leaves the square variation
unchanged. The statement uses endpoint flatness plus commutativity in the
observable group; it does not identify the two execution words. -/
theorem causalSquareVariation_symm {A : Type w} [AddCommGroup A]
    (F : Configuration S → A)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    causalSquareVariation F d.symm =
      causalSquareVariation F d := by
  unfold causalSquareVariation
  change
    F d.afterFE - F d.afterF - F d.afterE + F C =
      F d.afterEF - F d.afterE - F d.afterF + F C
  rw [ConcurrencyDiamond.endpoint_eq d]
  abel

/-- Antisymmetrized second causal difference. On a flat concurrency square this
is the discrete exterior d_C^2 term. -/
def causalExteriorSecondDifference {A : Type w} [AddCommGroup A]
    (F : Configuration S → A)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : A :=
  causalSquareVariation F d -
    causalSquareVariation F d.symm

@[simp] theorem causalExteriorSecondDifference_eq_zero
    {A : Type w} [AddCommGroup A]
    (F : Configuration S → A)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    causalExteriorSecondDifference F d = 0 := by
  rw [causalExteriorSecondDifference,
    causalSquareVariation_symm F d]
  exact sub_self _

/-- Order curvature compares the two sequential endpoints. It is meaningful
before quotienting histories by concurrency exchange. -/
def causalOrderCurvature {A : Type w} [AddGroup A]
    (F : Configuration S → A)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : A :=
  F d.afterEF - F d.afterFE

/-- A genuine concurrency diamond is flat for endpoint observables: the two
orders reach the same configuration, so order curvature vanishes. -/
@[simp] theorem causalOrderCurvature_flat {A : Type w} [AddGroup A]
    (F : Configuration S → A)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    causalOrderCurvature F d = 0 := by
  unfold causalOrderCurvature
  rw [ConcurrencyDiamond.endpoint_eq d]
  exact sub_self _

end CausalGeometry
