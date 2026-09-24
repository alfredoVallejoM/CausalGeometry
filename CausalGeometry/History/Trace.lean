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

/-- A concurrency diamond records a genuinely concurrent pair. The intermediate
and terminal configurations are derived canonically from the concurrency proof
rather than stored as freely overridable fields. -/
structure ConcurrencyDiamond (C : Configuration S) (e f : Event) where
  concurrent : S.ConcurrentAt C e f

namespace ConcurrencyDiamond

def afterE {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Configuration S :=
  S.extend C e d.concurrent.1

def afterF {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Configuration S :=
  S.extend C f d.concurrent.2.1

def afterEF {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Configuration S :=
  S.extend d.afterE f (S.concurrent_enabled_after_left d.concurrent)

def afterFE {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Configuration S :=
  S.extend d.afterF e (S.concurrent_enabled_after_right d.concurrent)

/-- Flat concurrent executions reach the same causal configuration. -/
theorem endpoint_eq {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    d.afterEF = d.afterFE := by
  apply S.configuration_eq_of_carrier_eq
  simp [afterEF, afterFE, afterE, afterF, Set.insert_comm]

/-- Reversing the two concurrent directions gives the same diamond with swapped
orientation. -/
def symm {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    ConcurrencyDiamond C f e :=
  ⟨S.concurrentAt_symm d.concurrent⟩

end ConcurrencyDiamond

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
