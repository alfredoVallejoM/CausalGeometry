import CausalGeometry.Foundation.EventSystemEquiv
import CausalGeometry.Calculus.IteratedDifference

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ w

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace EventSystemEquiv

variable (E : EventSystemEquiv S₁ S₂)

/-- Pull an observable on target configurations back to source
configurations. -/
def pullObservable
    {K : Type w}
    (F : Configuration S₂ → K) :
    Configuration S₁ → K :=
  fun C => F (E.mapConfiguration C)

/-- The first causal difference is representation invariant. -/
theorem causalDifference_natural
    {K : Type w} [AddGroup K]
    (F : Configuration S₂ → K)
    (C : Configuration S₁)
    (e : Event₁)
    (h : S₁.Enabled C e) :
    causalDifference F
        (E.mapConfiguration C)
        (E.eventEquiv e)
        ((E.enabled_iff C e).2 h)
      =
    causalDifference
        (E.pullObservable F)
        C e h := by
  unfold causalDifference pullObservable
  rw [← E.map_extend C e h]

/-- Target configuration after the first leg of a mapped concurrency diamond
is exactly the image of the source intermediate configuration. -/
theorem map_afterE
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    E.mapConfiguration d.afterE =
      (E.mapDiamond d).afterE := by
  unfold ConcurrencyDiamond.afterE
  exact E.map_extend C e d.concurrent.1

theorem map_afterF
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    E.mapConfiguration d.afterF =
      (E.mapDiamond d).afterF := by
  unfold ConcurrencyDiamond.afterF
  exact E.map_extend C f d.concurrent.2.1

/-- Two-step e-then-f endpoint is preserved. -/
theorem map_afterEF
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    E.mapConfiguration d.afterEF =
      (E.mapDiamond d).afterEF := by
  apply S₂.configuration_eq_of_carrier_eq
  ext x
  simp [
    EventSystemEquiv.mapConfiguration,
    ConcurrencyDiamond.afterEF,
    ConcurrencyDiamond.afterE,
    EventSystem.extend
  ]

/-- Two-step f-then-e endpoint is preserved. -/
theorem map_afterFE
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    E.mapConfiguration d.afterFE =
      (E.mapDiamond d).afterFE := by
  apply S₂.configuration_eq_of_carrier_eq
  ext x
  simp [
    EventSystemEquiv.mapConfiguration,
    ConcurrencyDiamond.afterFE,
    ConcurrencyDiamond.afterF,
    EventSystem.extend
  ]

/-- Square variation of scalar observables is representation invariant. -/
theorem causalSquareVariation_natural
    {K : Type w} [AddCommGroup K]
    (F : Configuration S₂ → K)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    causalSquareVariation F
        (E.mapDiamond d)
      =
    causalSquareVariation
        (E.pullObservable F) d := by
  unfold causalSquareVariation pullObservable
  rw [
    ← E.map_afterEF d,
    ← E.map_afterE d,
    ← E.map_afterF d
  ]

/-- Order curvature of a scalar observable is also invariant. -/
theorem causalOrderCurvature_natural
    {K : Type w} [AddGroup K]
    (F : Configuration S₂ → K)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    causalOrderCurvature F
        (E.mapDiamond d)
      =
    causalOrderCurvature
        (E.pullObservable F) d := by
  unfold causalOrderCurvature pullObservable
  rw [
    ← E.map_afterEF d,
    ← E.map_afterFE d
  ]

/-- Flat endpoint equality is preserved by representation change. -/
theorem mapped_endpoint_eq
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    E.mapConfiguration d.afterEF =
      E.mapConfiguration d.afterFE := by
  rw [
    E.map_afterEF d,
    E.map_afterFE d
  ]
  exact
    ConcurrencyDiamond.endpoint_eq
      (E.mapDiamond d)

end EventSystemEquiv
end CausalGeometry
