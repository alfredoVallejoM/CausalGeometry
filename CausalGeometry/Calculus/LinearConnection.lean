import CausalGeometry.Calculus.Connection
import Mathlib.LinearAlgebra.Basic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Linear transport along primitive causal events. The event/configuration
geometry remains unchanged; only the transported fiber carries module
structure. -/
structure LinearCausalConnection
    (K : Type w) (S : EventSystem Event Label) (V : Type x)
    [Semiring K] [AddCommMonoid V] [Module K V] where
  transport :
    ∀ (C : Configuration S) (e : Event),
      S.Enabled C e → V →ₗ[K] V

namespace LinearCausalConnection

variable {K : Type w} {V : Type x}
variable [Semiring K] [AddCommMonoid V] [Module K V]

def toCausalConnection
    (∇ : LinearCausalConnection K S V) :
    CausalConnection S V where
  transport := fun C e h => ∇.transport C e h

def transportEF
    (∇ : LinearCausalConnection K S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    V →ₗ[K] V :=
  (∇.transport d.afterE f
      (S.concurrent_enabled_after_left d.concurrent)).comp
    (∇.transport C e d.concurrent.1)

def transportFE
    (∇ : LinearCausalConnection K S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    V →ₗ[K] V :=
  (∇.transport d.afterF e
      (S.concurrent_enabled_after_right d.concurrent)).comp
    (∇.transport C f d.concurrent.2.1)

def FlatOn
    (∇ : LinearCausalConnection K S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : Prop :=
  ∇.transportEF d = ∇.transportFE d

variable [AddCommGroup V]

/-- Linear curvature is the difference between the two ordered transports. -/
def curvature
    (∇ : LinearCausalConnection K S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    V →ₗ[K] V :=
  ∇.transportEF d - ∇.transportFE d

theorem flatOn_iff_curvature_eq_zero
    (∇ : LinearCausalConnection K S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    ∇.FlatOn d ↔ ∇.curvature d = 0 := by
  unfold FlatOn curvature
  exact sub_eq_zero

@[simp] theorem curvature_apply
    (∇ : LinearCausalConnection K S V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) (x : V) :
    ∇.curvature d x =
      ∇.transportEF d x - ∇.transportFE d x := by
  rfl

/-- A gauge is a configuration-indexed family of fiber automorphisms. -/
structure Gauge where
  at : (C : Configuration S) → V ≃ₗ[K] V

/-- Gauge-conjugated connection. No claim of gauge invariance is made merely by
this definition; covariance of curvature is a separate theorem obligation. -/
def gaugeTransform
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V)) :
    LinearCausalConnection K S V where
  transport := fun C e h =>
    (G.at (S.extend C e h)).toLinearMap.comp
      ((∇.transport C e h).comp (G.at C).symm.toLinearMap)

@[simp] theorem gaugeTransform_apply
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    (C : Configuration S) (e : Event)
    (h : S.Enabled C e) (x : V) :
    (∇.gaugeTransform G).transport C e h x =
      G.at (S.extend C e h)
        (∇.transport C e h ((G.at C).symm x)) := by
  rfl

end LinearCausalConnection
end CausalGeometry
