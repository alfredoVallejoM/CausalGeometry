import CausalGeometry.Calculus.Connection
import CausalGeometry.Calculus.Difference

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Covariant finite difference along one enabled causal event.

The observable at the old configuration is first transported by the chosen
connection before comparison with the observable at the extended
configuration. -/
def covariantDifference {V : Type w} [AddGroup V]
    (∇ : CausalConnection S V)
    (F : Configuration S → V)
    (C : Configuration S)
    (e : Event) (h : S.Enabled C e) : V :=
  F (S.extend C e h) - ∇.transport C e h (F C)

@[simp] theorem covariantDifference_const_trivial
    {V : Type w} [AddGroup V]
    (a : V) (C : Configuration S)
    (e : Event) (h : S.Enabled C e) :
    covariantDifference (CausalConnection.trivial S V)
      (fun _ => a) C e h = 0 := by
  simp [covariantDifference, CausalConnection.trivial]

theorem covariantDifference_trivial_eq_causalDifference
    {V : Type w} [AddGroup V]
    (F : Configuration S → V)
    (C : Configuration S)
    (e : Event) (h : S.Enabled C e) :
    covariantDifference (CausalConnection.trivial S V) F C e h =
      causalDifference F C e h := by
  rfl

end CausalGeometry
