import CausalGeometry.Calculus.DependentConnection
import Mathlib.LinearAlgebra.Dual.Defs

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Linear causal transport with a configuration-dependent fiber.

Unlike LinearCausalConnection, source and target fibers may differ at every
event. -/
structure DependentLinearCausalConnection
    (K : Type w)
    (S : EventSystem Event Label)
    (Fiber : Configuration S → Type x)
    [Semiring K]
    [∀ C, AddCommMonoid (Fiber C)]
    [∀ C, Module K (Fiber C)] where
  transport :
    ∀ (C : Configuration S) (e : Event)
      (h : S.Enabled C e),
      Fiber C →ₗ[K] Fiber (S.extend C e h)

namespace DependentLinearCausalConnection

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommSemiring K]
variable [∀ C, AddCommMonoid (Fiber C)]
variable [∀ C, Module K (Fiber C)]

def toDependentConnection
    (∇ : DependentLinearCausalConnection K S Fiber) :
    DependentCausalConnection S Fiber where
  transport := fun C e h => ∇.transport C e h

def transportEF
    (∇ : DependentLinearCausalConnection K S Fiber)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    Fiber C →ₗ[K] Fiber d.afterEF :=
  (∇.transport d.afterE f
      (S.concurrent_enabled_after_left d.concurrent)).comp
    (∇.transport C e d.concurrent.1)

def transportFE
    (∇ : DependentLinearCausalConnection K S Fiber)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    Fiber C →ₗ[K] Fiber d.afterFE :=
  (∇.transport d.afterF e
      (S.concurrent_enabled_after_right d.concurrent)).comp
    (∇.transport C f d.concurrent.2.1)

/-- Flatness for a dependent linear connection compares transported vectors
after casting along the canonical equality of square endpoints. -/
def FlatOn
    (∇ : DependentLinearCausalConnection K S Fiber)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Prop :=
  ∀ x,
    cast
        (congrArg Fiber
          (ConcurrencyDiamond.endpoint_eq d))
        (∇.transportEF d x) =
      ∇.transportFE d x

/-- Parallel linear transport along a finite derived causal path. -/
def pathTransport
    (∇ : DependentLinearCausalConnection K S Fiber)
    {C D : Configuration S} :
    CausalPath S C D →
      Fiber C →ₗ[K] Fiber D
  | .nil _ => LinearMap.id
  | .step e h tail =>
      (∇.pathTransport tail).comp
        (∇.transport C e h)

@[simp] theorem pathTransport_nil
    (∇ : DependentLinearCausalConnection K S Fiber)
    (C : Configuration S) :
    ∇.pathTransport (.nil C) =
      LinearMap.id := rfl

@[simp] theorem pathTransport_step
    (∇ : DependentLinearCausalConnection K S Fiber)
    {C D : Configuration S}
    (e : Event) (h : S.Enabled C e)
    (tail :
      CausalPath S
        (S.extend C e h) D) :
    ∇.pathTransport (.step e h tail) =
      (∇.pathTransport tail).comp
        (∇.transport C e h) := rfl

/-- Covector pullback is available for every linear transport, even when the
transport is not invertible. -/
def covectorPullback
    (∇ : DependentLinearCausalConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Module.Dual K (Fiber (S.extend C e h)) →ₗ[K]
      Module.Dual K (Fiber C) where
  toFun := fun ω =>
    ω.comp (∇.transport C e h)
  map_add' := by
    intro ω η
    ext x
    simp
  map_smul' := by
    intro a ω
    ext x
    simp

@[simp] theorem covectorPullback_apply
    (∇ : DependentLinearCausalConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (ω :
      Module.Dual K
        (Fiber (S.extend C e h)))
    (x : Fiber C) :
    ∇.covectorPullback C e h ω x =
      ω (∇.transport C e h x) :=
  rfl

/-- The canonical vector-covector pairing is exactly natural under vector
pushforward and covector pullback. -/
theorem pairing_natural
    (∇ : DependentLinearCausalConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (ω :
      Module.Dual K
        (Fiber (S.extend C e h)))
    (x : Fiber C) :
    (∇.covectorPullback C e h ω) x =
      ω (∇.transport C e h x) :=
  rfl

end DependentLinearCausalConnection

/-- Stronger dependent connection in which every primitive event transport is
a linear equivalence.  This is the minimum extra structure needed for
covariant forward transport of covectors. -/
structure DependentLinearEquivConnection
    (K : Type w)
    (S : EventSystem Event Label)
    (Fiber : Configuration S → Type x)
    [Semiring K]
    [∀ C, AddCommMonoid (Fiber C)]
    [∀ C, Module K (Fiber C)] where
  transport :
    ∀ (C : Configuration S) (e : Event)
      (h : S.Enabled C e),
      Fiber C ≃ₗ[K] Fiber (S.extend C e h)

namespace DependentLinearEquivConnection

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommSemiring K]
variable [∀ C, AddCommMonoid (Fiber C)]
variable [∀ C, Module K (Fiber C)]

def toLinearConnection
    (∇ : DependentLinearEquivConnection K S Fiber) :
    DependentLinearCausalConnection K S Fiber where
  transport :=
    fun C e h =>
      (∇.transport C e h).toLinearMap

/-- Forward covector transport uses the inverse vector transport. -/
def covectorPushforward
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Module.Dual K (Fiber C) →ₗ[K]
      Module.Dual K (Fiber (S.extend C e h)) where
  toFun := fun ω =>
    ω.comp
      (∇.transport C e h).symm.toLinearMap
  map_add' := by
    intro ω η
    ext x
    simp
  map_smul' := by
    intro a ω
    ext x
    simp

@[simp] theorem covectorPushforward_apply
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (ω : Module.Dual K (Fiber C))
    (y : Fiber (S.extend C e h)) :
    ∇.covectorPushforward C e h ω y =
      ω ((∇.transport C e h).symm y) :=
  rfl

/-- Pairing is preserved by simultaneous forward transport of vectors and
covectors when the transport is invertible. -/
@[simp] theorem pairing_preserved
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (ω : Module.Dual K (Fiber C))
    (x : Fiber C) :
    (∇.covectorPushforward C e h ω)
        (∇.transport C e h x) =
      ω x := by
  simp [covectorPushforward]

/-- Pulling back a forward-transported covector recovers the original
covector. -/
theorem pullback_pushforward_covector
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (ω : Module.Dual K (Fiber C)) :
    (∇.toLinearConnection.covectorPullback
      C e h)
      (∇.covectorPushforward C e h ω) =
        ω := by
  ext x
  simp [DependentLinearCausalConnection.covectorPullback,
    covectorPushforward]

end DependentLinearEquivConnection
end CausalGeometry
