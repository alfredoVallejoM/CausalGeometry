import CausalGeometry.Calculus.EventDirection
import Mathlib.LinearAlgebra.Basic

namespace CausalGeometry

universe u v w x y
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- A linear model of first causal differences at one derived configuration.

Event directions remain discrete/primitive. The realization chooses vectors in
an auxiliary tangent module and a linear Jacobian whose values agree with the
actual finite causal differences on those generators. -/
structure CausalLinearization
    (K : Type w)
    {V : Type x}
    (F : Configuration S → V)
    (C : Configuration S)
    (T : Type y)
    [Semiring K]
    [AddCommMonoid T] [Module K T]
    [AddCommGroup V] [Module K V] where
  eventVector : EventDirection S C → T
  jacobian : T →ₗ[K] V
  agrees :
    ∀ d, jacobian (eventVector d) = d.difference F

namespace CausalLinearization

variable {K : Type w} {V : Type x} {T : Type y}
variable [Semiring K]
variable [AddCommMonoid T] [Module K T]
variable [AddCommGroup V] [Module K V]
variable {F : Configuration S → V} {C : Configuration S}

/-- Jacobian-vector product. -/
def jvp (J : CausalLinearization K F C T) (t : T) : V :=
  J.jacobian t

@[simp] theorem jvp_event
    (J : CausalLinearization K F C T)
    (d : EventDirection S C) :
    J.jvp (J.eventVector d) = d.difference F :=
  J.agrees d

/-- Algebraic reverse action on a covector: J^vee(lambda)=lambda o J.
This is a linear-dual/restriction bridge, not the foundational Psi. -/
def vjp
    (J : CausalLinearization K F C T)
    (λ : V →ₗ[K] K) :
    T →ₗ[K] K :=
  λ.comp J.jacobian

@[simp] theorem vjp_apply
    (J : CausalLinearization K F C T)
    (λ : V →ₗ[K] K) (t : T) :
    J.vjp λ t = λ (J.jacobian t) :=
  rfl

@[simp] theorem vjp_event
    (J : CausalLinearization K F C T)
    (λ : V →ₗ[K] K)
    (d : EventDirection S C) :
    J.vjp λ (J.eventVector d) = λ (d.difference F) := by
  rw [vjp_apply, J.agrees d]

end CausalLinearization
end CausalGeometry
