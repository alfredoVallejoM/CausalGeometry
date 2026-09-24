import CausalGeometry.Calculus.Difference

namespace CausalGeometry

universe u v
open EventSystem

variable {Event : Type u} {Label : Type v}

/-- One primitive-event direction available at a derived configuration. -/
structure EventDirection
    (S : EventSystem Event Label)
    (C : Configuration S) where
  event : Event
  enabled : S.Enabled C event

namespace EventDirection

variable {S : EventSystem Event Label} {C : Configuration S}

def endpoint (d : EventDirection S C) : Configuration S :=
  S.extend C d.event d.enabled

def difference {V : Type*} [AddGroup V]
    (F : Configuration S → V)
    (d : EventDirection S C) : V :=
  causalDifference F C d.event d.enabled

@[simp] theorem difference_const {V : Type*} [AddGroup V]
    (a : V) (d : EventDirection S C) :
    d.difference (fun _ => a) = 0 := by
  simp [difference]

end EventDirection
end CausalGeometry
