import CausalGeometry.Calculus.Difference
import CausalGeometry.History.Trace

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
