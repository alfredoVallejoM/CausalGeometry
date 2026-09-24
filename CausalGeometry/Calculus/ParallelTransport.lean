import CausalGeometry.Calculus.LinearConnection
import CausalGeometry.History.Path

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Semiring K] [AddCommMonoid V] [Module K V]

namespace LinearCausalConnection

/-- Parallel transport along one finite causal path. Chronological event order
is retained as composition order of linear transports. -/
def pathTransport
    (∇ : LinearCausalConnection K S V)
    {C D : Configuration S} :
    CausalPath S C D → V →ₗ[K] V
  | .nil _ => LinearMap.id
  | .step e h tail =>
      (∇.pathTransport tail).comp (∇.transport C e h)

@[simp] theorem pathTransport_nil
    (∇ : LinearCausalConnection K S V)
    (C : Configuration S) :
    ∇.pathTransport (.nil C) = LinearMap.id := rfl

@[simp] theorem pathTransport_step
    (∇ : LinearCausalConnection K S V)
    {C D : Configuration S}
    (e : Event) (h : S.Enabled C e)
    (tail : CausalPath S (S.extend C e h) D) :
    ∇.pathTransport (.step e h tail) =
      (∇.pathTransport tail).comp (∇.transport C e h) := rfl

/-- Holonomy is transport along a closed causal history. It is an endomorphism;
invertibility is not silently assumed. -/
def holonomy
    (∇ : LinearCausalConnection K S V)
    {C : Configuration S}
    (p : CausalPath S C C) :
    V →ₗ[K] V :=
  ∇.pathTransport p

@[simp] theorem holonomy_nil
    (∇ : LinearCausalConnection K S V)
    (C : Configuration S) :
    ∇.holonomy (.nil C) = LinearMap.id := rfl

end LinearCausalConnection
end CausalGeometry
