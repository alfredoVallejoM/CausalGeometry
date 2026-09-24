import CausalGeometry.Calculus.GaugeCovariance
import CausalGeometry.Calculus.ParallelTransport

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Semiring K] [AddCommGroup V] [Module K V]

namespace LinearCausalConnection

/-- Parallel transport along a path transforms by endpoint conjugation. -/
theorem gaugeTransform_pathTransport
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    {C D : Configuration S}
    (p : CausalPath S C D) :
    (∇.gaugeTransform G).pathTransport p =
      (G.at D).toLinearMap.comp
        ((∇.pathTransport p).comp (G.at C).symm.toLinearMap) := by
  induction p with
  | nil C =>
      ext x
      simp [pathTransport]
  | step e h tail ih =>
      simp only [pathTransport_step]
      rw [ih]
      ext x
      simp [gaugeTransform_apply]

/-- Holonomy of a closed causal path is conjugated by the gauge at the base
configuration. Thus its conjugacy class is the gauge-stable datum. -/
theorem gaugeTransform_holonomy
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    {C : Configuration S}
    (p : CausalPath S C C) :
    (∇.gaugeTransform G).holonomy p =
      (G.at C).toLinearMap.comp
        ((∇.holonomy p).comp (G.at C).symm.toLinearMap) := by
  exact ∇.gaugeTransform_pathTransport G p

end LinearCausalConnection
end CausalGeometry
