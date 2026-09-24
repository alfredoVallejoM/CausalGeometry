import CausalGeometry.Calculus.LinearConnection

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Semiring K] [AddCommGroup V] [Module K V]

namespace LinearCausalConnection

@[simp] theorem gaugeTransform_transportEF_apply
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) (x : V) :
    (∇.gaugeTransform G).transportEF d x =
      G.at d.afterEF
        (∇.transportEF d ((G.at C).symm x)) := by
  simp [transportEF, gaugeTransform_apply]

@[simp] theorem gaugeTransform_transportFE_apply
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) (x : V) :
    (∇.gaugeTransform G).transportFE d x =
      G.at d.afterFE
        (∇.transportFE d ((G.at C).symm x)) := by
  simp [transportFE, gaugeTransform_apply]

/-- Curvature transforms by endpoint conjugation. This is covariance, not an
assumption that curvature itself is gauge invariant. -/
theorem gaugeTransform_curvature_apply
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) (x : V) :
    (∇.gaugeTransform G).curvature d x =
      G.at d.afterEF
        (∇.curvature d ((G.at C).symm x)) := by
  simp only [curvature_apply, gaugeTransform_transportEF_apply,
    gaugeTransform_transportFE_apply]
  rw [← ConcurrencyDiamond.endpoint_eq d]
  exact (map_sub (G.at d.afterEF)
    (∇.transportEF d ((G.at C).symm x))
    (∇.transportFE d ((G.at C).symm x))).symm

theorem gaugeTransform_curvature
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (∇.gaugeTransform G).curvature d =
      (G.at d.afterEF).toLinearMap.comp
        ((∇.curvature d).comp (G.at C).symm.toLinearMap) := by
  ext x
  exact ∇.gaugeTransform_curvature_apply G d x

/-- Flatness of a causal square is gauge stable. -/
theorem gaugeTransform_flatOn
    (∇ : LinearCausalConnection K S V)
    (G : Gauge (K := K) (S := S) (V := V))
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f)
    (h : ∇.FlatOn d) :
    (∇.gaugeTransform G).FlatOn d := by
  have h0 : ∇.curvature d = 0 :=
    (∇.flatOn_iff_curvature_eq_zero d).mp h
  apply ((∇.gaugeTransform G).flatOn_iff_curvature_eq_zero d).mpr
  ext x
  rw [gaugeTransform_curvature_apply, h0]
  simp

end LinearCausalConnection
end CausalGeometry
