import CausalGeometry.Foundation.EventSystem

namespace CausalGeometry

universe u v
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- One enabled causal step. -/
structure Step (C D : Configuration S) where
  event : Event
  enabled : S.Enabled C event
  target_eq : D.carrier = insert event C.carrier

/-- A concurrency diamond records the two admissible orders without declaring
the paths definitionally equal. -/
structure ConcurrencyDiamond (C : Configuration S) (e f : Event) where
  concurrent : S.ConcurrentAt C e f
  afterE : Configuration S := S.extend C e concurrent.1
  afterF : Configuration S := S.extend C f concurrent.2.1

/-- Extensional endpoint reached by adding two concurrent events. -/
def concurrentEndpoint (C : Configuration S) (e f : Event) : Set Event :=
  insert f (insert e C.carrier)

theorem concurrentEndpoint_comm (C : Configuration S) (e f : Event) :
    concurrentEndpoint C e f = concurrentEndpoint C f e := by
  simp [concurrentEndpoint, Set.insert_comm]

/-- Finite execution as a list of events plus a semantic validity predicate.
The later campaign replaces this thin carrier by a compositional history
category. -/
structure Execution (S : EventSystem Event Label) where
  start : Configuration S
  events : List Event
  valid : Prop

end CausalGeometry
