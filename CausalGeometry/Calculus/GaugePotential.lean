import CausalGeometry.Calculus.CubeFrame
import CausalGeometry.Calculus.EventDirection
import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Semiring K] [AddCommGroup V] [Module K V]

/-- Commutator of two linear causal operators. -/
def linearCommutator
    (A B : V →ₗ[K] V) : V →ₗ[K] V :=
  A.comp B - B.comp A

@[simp] theorem linearCommutator_apply
    (A B : V →ₗ[K] V) (x : V) :
    linearCommutator A B x =
      A (B x) - B (A x) := rfl

@[simp] theorem linearCommutator_self
    (A : V →ₗ[K] V) :
    linearCommutator A A = 0 := by
  ext x
  simp [linearCommutator]

theorem linearCommutator_skew
    (A B : V →ₗ[K] V) :
    linearCommutator A B =
      - linearCommutator B A := by
  ext x
  simp [linearCommutator]
  abel

/-- Jacobi identity for endomorphism commutators. This is the algebraic source
of the local Bianchi identity below. -/
theorem linearCommutator_jacobi
    (A B C : V →ₗ[K] V) :
    linearCommutator A (linearCommutator B C)
      + linearCommutator B (linearCommutator C A)
      + linearCommutator C (linearCommutator A B) = 0 := by
  ext x
  simp [linearCommutator]
  abel

/-- Local linearized gauge potential at one derived causal configuration.
It assigns an endomorphism to every enabled primitive-event direction. -/
structure CausalGaugePotential
    (K : Type w)
    (S : EventSystem Event Label)
    (V : Type x)
    (C : Configuration S)
    [Semiring K] [AddCommGroup V] [Module K V] where
  operator : EventDirection S C → V →ₗ[K] V

namespace CausalGaugePotential

variable {C : Configuration S}

/-- Infinitesimal/local curvature as commutator of causal directional
operators. This is deliberately distinct from finite square transport
curvature until a comparison theorem is supplied. -/
def curvature
    (A : CausalGaugePotential K S V C)
    (d e : EventDirection S C) :
    V →ₗ[K] V :=
  linearCommutator (A.operator d) (A.operator e)

/-- Covariant action on an endomorphism in the local linearized model. -/
def covariantEndDerivative
    (A : CausalGaugePotential K S V C)
    (d : EventDirection S C)
    (T : V →ₗ[K] V) :
    V →ₗ[K] V :=
  linearCommutator (A.operator d) T

@[simp] theorem curvature_self
    (A : CausalGaugePotential K S V C)
    (d : EventDirection S C) :
    A.curvature d d = 0 :=
  linearCommutator_self _

theorem curvature_skew
    (A : CausalGaugePotential K S V C)
    (d e : EventDirection S C) :
    A.curvature d e = - A.curvature e d :=
  linearCommutator_skew _ _

/-- Local causal Bianchi identity. It is Jacobi for the three directional
operators and requires no claim about finite-transport curvature. -/
theorem bianchi
    (A : CausalGaugePotential K S V C)
    (d e f : EventDirection S C) :
    A.covariantEndDerivative d (A.curvature e f)
      + A.covariantEndDerivative e (A.curvature f d)
      + A.covariantEndDerivative f (A.curvature d e) = 0 := by
  exact linearCommutator_jacobi
    (A.operator d) (A.operator e) (A.operator f)

/-- A cube frame canonically supplies local event directions to the gauge
potential. -/
def cubeDirection
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i : ι) :
    EventDirection S C where
  event := Q.event i
  enabled := Q.enabled i

theorem bianchi_on_cube
    {ι : Type*}
    (A : CausalGaugePotential K S V C)
    (Q : CausalCubeFrame S C ι)
    (i j k : ι) :
    A.covariantEndDerivative (cubeDirection Q i)
        (A.curvature (cubeDirection Q j) (cubeDirection Q k))
      + A.covariantEndDerivative (cubeDirection Q j)
        (A.curvature (cubeDirection Q k) (cubeDirection Q i))
      + A.covariantEndDerivative (cubeDirection Q k)
        (A.curvature (cubeDirection Q i) (cubeDirection Q j)) = 0 :=
  A.bianchi _ _ _

end CausalGaugePotential
end CausalGeometry
