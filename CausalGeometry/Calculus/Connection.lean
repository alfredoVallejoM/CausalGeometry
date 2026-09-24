import CausalGeometry.History.Trace

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}

/-- A constant-fiber causal connection. It assigns a transport operation to
every enabled causal step. More general dependent fibers can be added later
without changing the flat-diamond contract below. -/
structure CausalConnection
    (S : EventSystem Event Label) (V : Type w) where
  transport :
    ∀ (C : Configuration S) (e : Event),
      S.Enabled C e → V → V

namespace CausalConnection

variable {S : EventSystem Event Label} {V : Type w}

def transportEF (∇ : CausalConnection S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : V → V :=
  fun x =>
    ∇.transport d.afterE f
      (S.concurrent_enabled_after_left d.concurrent)
      (∇.transport C e d.concurrent.1 x)

def transportFE (∇ : CausalConnection S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : V → V :=
  fun x =>
    ∇.transport d.afterF e
      (S.concurrent_enabled_after_right d.concurrent)
      (∇.transport C f d.concurrent.2.1 x)

/-- Flatness on one concurrency diamond means transport is independent of the
order chosen around that diamond. -/
def FlatOn (∇ : CausalConnection S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Prop :=
  ∀ x, ∇.transportEF d x = ∇.transportFE d x

/-- Curvature of a constant-fiber connection on one concurrency diamond. -/
def curvature [AddGroup V] (∇ : CausalConnection S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) (x : V) : V :=
  ∇.transportEF d x - ∇.transportFE d x

theorem curvature_eq_zero_of_flat [AddGroup V]
    (∇ : CausalConnection S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f)
    (h : ∇.FlatOn d) (x : V) :
    ∇.curvature d x = 0 := by
  simp [curvature, h x]

theorem flatOn_iff_curvature_eq_zero [AddGroup V]
    (∇ : CausalConnection S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    ∇.FlatOn d ↔ ∀ x, ∇.curvature d x = 0 := by
  constructor
  · intro h x
    exact ∇.curvature_eq_zero_of_flat d h x
  · intro h x
    have hx := h x
    unfold curvature at hx
    exact sub_eq_zero.mp hx

/-- The connection that transports every value identically. -/
def trivial (S : EventSystem Event Label) (V : Type w) :
    CausalConnection S V where
  transport := fun _ _ _ x => x

@[simp] theorem trivial_flat
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (trivial S V).FlatOn d := by
  intro x
  rfl

end CausalConnection
end CausalGeometry
