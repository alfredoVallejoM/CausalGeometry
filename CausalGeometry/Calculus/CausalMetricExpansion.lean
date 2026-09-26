import CausalGeometry.Calculus.CausalLeviCivita
import CausalGeometry.Calculus.LinearConnection
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Field K] [AddCommGroup V] [Module K V]

namespace CausalMetricComparison

variable {C : Configuration S}

/-- Linearized metric defect of one local directional operator. -/
def localMetricDefect
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (d : EventDirection S C)
    (x y : V) : K :=
  g.pair (A.operator d x) y +
    g.pair x (A.operator d y)

/-- Exact quadratic correction appearing when a finite transport is written
as I+A. -/
def quadraticMetricCorrection
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (d : EventDirection S C)
    (x y : V) : K :=
  g.pair
    (A.operator d x)
    (A.operator d y)

/-- Exact finite/local metric identity.

If T=I+A and T is an exact isometry, then the linearized skew-adjoint defect
is the negative quadratic correction. -/
theorem finite_isometry_expansion
    (nabla : LinearCausalConnection K S V)
    (A : (C : Configuration S) →
      CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (htransport :
      ∀ (C : Configuration S)
        (e : Event)
        (h : S.Enabled C e),
        nabla.transport C e h =
          LinearMap.id +
            (A C).operator ⟨e, h⟩)
    (hmetric : nabla.MetricCompatible g)
    (C : Configuration S)
    (d : EventDirection S C)
    (x y : V) :
    localMetricDefect (A C) g d x y +
        quadraticMetricCorrection (A C) g d x y
      =
    0 := by

  have h :=
    hmetric C d.event d.enabled x y

  rw [htransport C d.event d.enabled] at h

  unfold localMetricDefect
    quadraticMetricCorrection
    CausalMetric.pair at *

  simp only [
    LinearMap.add_apply,
    LinearMap.id_apply,
    map_add
  ] at h

  linear_combination h

/-- Equivalent form: the local metric defect is exactly minus the finite
quadratic correction. -/
theorem localMetricDefect_eq_neg_quadratic
    (nabla : LinearCausalConnection K S V)
    (A : (C : Configuration S) →
      CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (htransport :
      ∀ (C : Configuration S)
        (e : Event)
        (h : S.Enabled C e),
        nabla.transport C e h =
          LinearMap.id +
            (A C).operator ⟨e, h⟩)
    (hmetric : nabla.MetricCompatible g)
    (C : Configuration S)
    (d : EventDirection S C)
    (x y : V) :
    localMetricDefect (A C) g d x y
      =
    - quadraticMetricCorrection (A C) g d x y := by
  exact
    eq_neg_of_add_eq_zero_left
      (finite_isometry_expansion
        nabla A g htransport hmetric
        C d x y)

/-- Exact finite metric compatibility implies infinitesimal/local metric
compatibility whenever the quadratic correction vanishes on the named local
sector. -/
theorem local_metricCompatible_of_quadratic_zero
    (nabla : LinearCausalConnection K S V)
    (A : (C : Configuration S) →
      CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (htransport :
      ∀ (C : Configuration S)
        (e : Event)
        (h : S.Enabled C e),
        nabla.transport C e h =
          LinearMap.id +
            (A C).operator ⟨e, h⟩)
    (hmetric : nabla.MetricCompatible g)
    (C : Configuration S)
    (hquad :
      ∀ d x y,
        quadraticMetricCorrection
          (A C) g d x y = 0) :
    (A C).MetricCompatibleLocal g := by

  intro d x y

  have h :=
    finite_isometry_expansion
      nabla A g htransport hmetric
      C d x y

  rw [hquad d x y] at h
  simpa [localMetricDefect] using h

/-- Conversely, an I+A finite transport is exactly metric-compatible whenever
the full finite metric identity (linear defect plus quadratic correction)
vanishes. -/
theorem finite_metricCompatible_of_expansion
    (nabla : LinearCausalConnection K S V)
    (A : (C : Configuration S) →
      CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (htransport :
      ∀ (C : Configuration S)
        (e : Event)
        (h : S.Enabled C e),
        nabla.transport C e h =
          LinearMap.id +
            (A C).operator ⟨e, h⟩)
    (hexp :
      ∀ (C : Configuration S)
        (d : EventDirection S C)
        (x y : V),
        localMetricDefect (A C) g d x y +
            quadraticMetricCorrection (A C) g d x y
          =
        0) :
    nabla.MetricCompatible g := by

  intro C e h x y

  let d : EventDirection S C :=
    ⟨e, h⟩

  have hz := hexp C d x y

  rw [htransport C e h]

  unfold localMetricDefect
    quadraticMetricCorrection
    CausalMetric.pair at hz ⊢

  simp only [
    LinearMap.add_apply,
    LinearMap.id_apply,
    map_add
  ]

  linear_combination hz

/-- If the local operator is infinitesimally metric-compatible, exact finite
isometry of I+A is equivalent to vanishing of the quadratic correction. -/
theorem finite_metricCompatible_iff_quadratic_zero_of_local
    (nabla : LinearCausalConnection K S V)
    (A : (C : Configuration S) →
      CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (htransport :
      ∀ (C : Configuration S)
        (e : Event)
        (h : S.Enabled C e),
        nabla.transport C e h =
          LinearMap.id +
            (A C).operator ⟨e, h⟩)
    (hlocal :
      ∀ C,
        (A C).MetricCompatibleLocal g) :
    nabla.MetricCompatible g ↔
      ∀ (C : Configuration S)
        (d : EventDirection S C)
        (x y : V),
        quadraticMetricCorrection
          (A C) g d x y = 0 := by

  constructor

  · intro hmetric C d x y

    have h :=
      finite_isometry_expansion
        nabla A g htransport hmetric
        C d x y

    have hl := hlocal C d x y

    unfold localMetricDefect at h
    rw [hl] at h
    simpa using h

  · intro hquad

    apply finite_metricCompatible_of_expansion
      nabla A g htransport

    intro C d x y

    have hl := hlocal C d x y

    unfold localMetricDefect
      quadraticMetricCorrection at *

    rw [hl, hquad C d x y]
    simp

end CausalMetricComparison
end CausalGeometry
