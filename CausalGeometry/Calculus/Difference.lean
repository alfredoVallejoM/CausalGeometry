import CausalGeometry.Foundation.EventSystem

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Finite causal variation of an additive observable along an enabled event. -/
def causalDifference {A : Type w} [AddGroup A]
    (F : Configuration S → A) (C : Configuration S)
    (e : Event) (h : S.Enabled C e) : A :=
  F (S.extend C e h) - F C

@[simp] theorem causalDifference_const {A : Type w} [AddGroup A]
    (a : A) (C : Configuration S) (e : Event) (h : S.Enabled C e) :
    causalDifference (fun _ => a) C e h = 0 := by
  simp [causalDifference]

end CausalGeometry
