import CausalGeometry.Calculus.CausalLeviCivita
import CausalGeometry.Calculus.CoordinateCurvature
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x y
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A finite causal linear frame at one configuration.

Each coordinate vector of the basis is realized by an actual enabled causal
direction through the supplied solder form. -/
structure CausalLinearFrame
    (theta : CausalSolderForm K S V C)
    (ι : Type y)
    [Fintype ι] where

  basis : Basis ι K V

  direction :
    ι → EventDirection S C

  realizes :
    ∀ i,
      theta.value (direction i) =
        basis i

namespace CausalLinearFrame

variable {C : Configuration S}
variable {ι : Type y} [Fintype ι]
variable {theta : CausalSolderForm K S V C}
variable (F : CausalLinearFrame theta ι)

/-- A causal linear frame automatically proves that the solder form spans the
whole fiber. -/
theorem solder_spans :
    theta.Spans := by
  unfold CausalSolderForm.Spans
  apply le_antisymm le_top
  rw [← F.basis.span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  refine ⟨F.direction i, ?_⟩
  exact F.realizes i

/-- Coordinate coefficient of a local vector in the causal frame. -/
def coord
    (i : ι) :
    V →ₗ[K] K :=
  F.basis.coord i

@[simp] theorem coord_basis
    (i j : ι) :
    F.coord i (F.basis j) =
      if j = i then 1 else 0 := by
  classical
  simp [coord]

/-- Christoffel coefficient in the causal frame. -/
def christoffel
    (A : CausalGaugePotential K S V C)
    (i j k : ι) : K :=
  F.basis.coord k
    (A.operator (F.direction i)
      (F.basis j))

/-- Curvature components R^a_{bcd} of one local causal gauge potential. -/
def curvatureComponents
    (A : CausalGaugePotential K S V C) :
    CoordinateTensor.Curvature
      (K := K) (ι := ι) :=
  fun I J =>
    F.basis.coord (I (0 : Fin 1))
      ((A.curvature
        (F.direction (J (1 : Fin 3)))
        (F.direction (J (2 : Fin 3))))
        (F.basis (J (0 : Fin 3))))

@[simp] theorem curvatureComponents_apply
    (A : CausalGaugePotential K S V C)
    (I : Fin 1 → ι)
    (J : Fin 3 → ι) :
    F.curvatureComponents A I J =
      F.basis.coord (I 0)
        ((A.curvature
          (F.direction (J 1))
          (F.direction (J 2)))
          (F.basis (J 0))) :=
  rfl

/-- Ricci components obtained from the actual causal curvature components. -/
def ricciComponents
    (A : CausalGaugePotential K S V C) :
    CoordinateTensor K ι 0 2 :=
  CoordinateTensor.ricci
    (F.curvatureComponents A)

/-- Scalar curvature of the local causal connection in the selected frame and
for a supplied inverse metric tensor. -/
def scalarCurvature
    (gInv : CoordinateTensor K ι 2 0)
    (A : CausalGaugePotential K S V C) : K :=
  CoordinateTensor.scalarCurvature
    gInv (F.curvatureComponents A)

/-- Frame-supported Levi-Civita uniqueness.

The explicit frame discharges the abstract spanning hypothesis automatically. -/
theorem leviCivita_unique
    [CharZero K]
    (A A' : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (B : CausalDirectionBracket S V C)
    (hmetric : A.MetricCompatibleLocal g)
    (hmetric' : A'.MetricCompatibleLocal g)
    (hT : A.TorsionFree theta B)
    (hT' : A'.TorsionFree theta B) :
    A = A' :=
  CausalGaugePotential.leviCivita_unique
    A A' g theta B
    F.solder_spans
    hmetric hmetric'
    hT hT'

end CausalLinearFrame
end CausalGeometry
