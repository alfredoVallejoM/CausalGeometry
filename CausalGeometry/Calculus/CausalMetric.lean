import CausalGeometry.Calculus.LinearConnection
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

/-- A nondegenerate symmetric causal bilinear metric on one linear fiber.

No signature or positivity is imposed.  This permits Euclidean, pseudo-Riemannian
and purely algebraic realizations to share the same source interface. -/
structure CausalMetric
    (K : Type u)
    (V : Type v)
    [Field K]
    [AddCommGroup V]
    [Module K V] where

  form : V →ₗ[K] V →ₗ[K] K

  symmetric :
    ∀ x y,
      form x y = form y x

  nondegenerate :
    ∀ x,
      (∀ y, form x y = 0) →
        x = 0

namespace CausalMetric

variable
    {K : Type u}
    {V : Type v}
    [Field K]
    [AddCommGroup V]
    [Module K V]
    (g : CausalMetric K V)

def pair (x y : V) : K :=
  g.form x y

@[simp] theorem pair_zero_left (y : V) :
    g.pair 0 y = 0 := by
  simp [pair]

@[simp] theorem pair_zero_right (x : V) :
    g.pair x 0 = 0 := by
  simp [pair]

theorem pair_symm (x y : V) :
    g.pair x y = g.pair y x :=
  g.symmetric x y

theorem eq_zero_of_pair_all_zero
    {x : V}
    (h : ∀ y, g.pair x y = 0) :
    x = 0 :=
  g.nondegenerate x h

end CausalMetric

namespace LinearCausalConnection

variable
    {Event : Type w}
    {Label : Type x}
    {S : EventSystem Event Label}
    {K : Type u}
    {V : Type v}
    [Field K]
    [AddCommGroup V]
    [Module K V]

/-- Metric compatibility of finite causal transport.

This is an exact finite isometry law for every primitive enabled event.  It is
not definitionally imposed on a connection. -/
def MetricCompatible
    (∇ : LinearCausalConnection K S V)
    (g : CausalMetric K V) : Prop :=
  ∀ (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (x y : V),
      g.pair
          (∇.transport C e h x)
          (∇.transport C e h y)
        =
      g.pair x y

/-- Exact metric-compatible primitive transport is automatically injective.
Surjectivity is intentionally not inferred: causal evolution may be
information-preserving in the metric sense on its image without being
reversible. -/
theorem transport_injective_of_metricCompatible
    (∇ : LinearCausalConnection K S V)
    (g : CausalMetric K V)
    (hmetric : ∇.MetricCompatible g)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Function.Injective (∇.transport C e h) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply g.eq_zero_of_pair_all_zero
  intro z
  calc
    g.pair (x - y) z =
        g.pair
          (∇.transport C e h (x - y))
          (∇.transport C e h z) := by
            symm
            exact hmetric C e h (x - y) z
    _ =
        g.pair 0
          (∇.transport C e h z) := by
            rw [map_sub, hxy, sub_self]
    _ = 0 := by simp

end LinearCausalConnection
end CausalGeometry
