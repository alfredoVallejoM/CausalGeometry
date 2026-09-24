import CausalGeometry.History.Path
import CausalGeometry.History.Trace

namespace CausalGeometry

universe u v x
open EventSystem

variable {Event : Type u} {Label : Type v}

/-- A causal connection with a configuration-dependent fiber.

Primitive events remain the base directions. Transport is allowed to change
the fiber because its codomain is indexed by the extended configuration. -/
structure DependentCausalConnection
    (S : EventSystem Event Label)
    (Fiber : Configuration S → Type x) where
  transport :
    ∀ (C : Configuration S) (e : Event)
      (h : S.Enabled C e),
      Fiber C → Fiber (S.extend C e h)

namespace DependentCausalConnection

variable {S : EventSystem Event Label}
variable {Fiber : Configuration S → Type x}

def transportEF
    (∇ : DependentCausalConnection S Fiber)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    Fiber C → Fiber d.afterEF :=
  fun x =>
    ∇.transport d.afterE f
      (S.concurrent_enabled_after_left d.concurrent)
      (∇.transport C e d.concurrent.1 x)

def transportFE
    (∇ : DependentCausalConnection S Fiber)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    Fiber C → Fiber d.afterFE :=
  fun x =>
    ∇.transport d.afterF e
      (S.concurrent_enabled_after_right d.concurrent)
      (∇.transport C f d.concurrent.2.1 x)

/-- Flatness for dependent fibers compares the two ordered transports only
after transporting the codomain type along equality of the square endpoints. -/
def FlatOn
    (∇ : DependentCausalConnection S Fiber)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Prop :=
  ∀ x,
    cast (congrArg Fiber (ConcurrencyDiamond.endpoint_eq d))
        (∇.transportEF d x) =
      ∇.transportFE d x

/-- Parallel transport through a derived causal path with genuinely varying
fibers. -/
def pathTransport
    (∇ : DependentCausalConnection S Fiber)
    {C D : Configuration S} :
    CausalPath S C D → Fiber C → Fiber D
  | .nil _ => id
  | .step e h tail =>
      fun x => ∇.pathTransport tail (∇.transport C e h x)

@[simp] theorem pathTransport_nil
    (∇ : DependentCausalConnection S Fiber)
    (C : Configuration S) (x : Fiber C) :
    ∇.pathTransport (.nil C) x = x := rfl

@[simp] theorem pathTransport_step
    (∇ : DependentCausalConnection S Fiber)
    {C D : Configuration S}
    (e : Event) (h : S.Enabled C e)
    (tail : CausalPath S (S.extend C e h) D)
    (x : Fiber C) :
    ∇.pathTransport (.step e h tail) x =
      ∇.pathTransport tail (∇.transport C e h x) := rfl

/-- Every ordinary constant-fiber causal connection is a special case. -/
def ofConstant {V : Type x}
    (∇ : CausalConnection S V) :
    DependentCausalConnection S (fun _ => V) where
  transport := fun C e h => ∇.transport C e h

end DependentCausalConnection
end CausalGeometry
