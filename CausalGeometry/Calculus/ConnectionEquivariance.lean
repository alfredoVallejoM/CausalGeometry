import CausalGeometry.Calculus.EventSystemEquiv
import CausalGeometry.Calculus.LinearConnection
import CausalGeometry.Calculus.DependentLinearConnection

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ w x

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace EventSystemEquiv

variable (E : EventSystemEquiv S₁ S₂)

/-- Pull back a constant-fiber linear causal connection. -/
def pullLinearConnection
    {K : Type w} {V : Type x}
    [Semiring K] [AddCommMonoid V] [Module K V]
    (∇ : LinearCausalConnection K S₂ V) :
    LinearCausalConnection K S₁ V where
  transport := fun C e h =>
    ∇.transport
      (E.mapConfiguration C)
      (E.eventEquiv e)
      ((E.enabled_iff C e).2 h)

@[simp] theorem pullLinearConnection_transport
    {K : Type w} {V : Type x}
    [Semiring K] [AddCommMonoid V] [Module K V]
    (∇ : LinearCausalConnection K S₂ V)
    (C : Configuration S₁)
    (e : Event₁)
    (h : S₁.Enabled C e) :
    (E.pullLinearConnection ∇).transport C e h =
      ∇.transport
        (E.mapConfiguration C)
        (E.eventEquiv e)
        ((E.enabled_iff C e).2 h) :=
  rfl

/-- Two-step e-then-f transport is invariant. -/
theorem pullLinearConnection_transportEF
    {K : Type w} {V : Type x}
    [Semiring K] [AddCommMonoid V] [Module K V]
    (∇ : LinearCausalConnection K S₂ V)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    (E.pullLinearConnection ∇).transportEF d =
      ∇.transportEF (E.mapDiamond d) := by
  ext x
  unfold
    LinearCausalConnection.transportEF
    pullLinearConnection
  have hcfg := E.map_afterE d
  cases hcfg
  rfl

/-- f-then-e transport is invariant. -/
theorem pullLinearConnection_transportFE
    {K : Type w} {V : Type x}
    [Semiring K] [AddCommMonoid V] [Module K V]
    (∇ : LinearCausalConnection K S₂ V)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    (E.pullLinearConnection ∇).transportFE d =
      ∇.transportFE (E.mapDiamond d) := by
  ext x
  unfold
    LinearCausalConnection.transportFE
    pullLinearConnection
  have hcfg := E.map_afterF d
  cases hcfg
  rfl

/-- Finite curvature is representation invariant. -/
theorem pullLinearConnection_curvature
    {K : Type w} {V : Type x}
    [Semiring K] [AddCommGroup V] [Module K V]
    (∇ : LinearCausalConnection K S₂ V)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    (E.pullLinearConnection ∇).curvature d =
      ∇.curvature (E.mapDiamond d) := by
  unfold LinearCausalConnection.curvature
  rw [
    E.pullLinearConnection_transportEF ∇ d,
    E.pullLinearConnection_transportFE ∇ d
  ]

/-- Flatness of one diamond is preserved and reflected. -/
theorem pullLinearConnection_flatOn_iff
    {K : Type w} {V : Type x}
    [Semiring K] [AddCommGroup V] [Module K V]
    (∇ : LinearCausalConnection K S₂ V)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    (E.pullLinearConnection ∇).FlatOn d ↔
      ∇.FlatOn (E.mapDiamond d) := by
  rw [
    LinearCausalConnection.flatOn_iff_curvature_eq_zero,
    LinearCausalConnection.flatOn_iff_curvature_eq_zero,
    E.pullLinearConnection_curvature
  ]

/-- Pull a dependent linear connection.  The codomain type is transported
across the proved equality between mapping-after-extension and
extension-after-mapping. -/
def pullDependentLinearConnection
    {K : Type w}
    {Fiber : Configuration S₂ → Type x}
    [CommSemiring K]
    [∀ C, AddCommMonoid (Fiber C)]
    [∀ C, Module K (Fiber C)]
    (∇ : DependentLinearCausalConnection K S₂ Fiber) :
    DependentLinearCausalConnection
      K S₁ (E.pullFiber Fiber) where
  transport := by
    intro C e h
    have hcfg :=
      E.map_extend C e h
    cases hcfg
    exact
      ∇.transport
        (E.mapConfiguration C)
        (E.eventEquiv e)
        ((E.enabled_iff C e).2 h)

/-- Pull an invertible dependent linear connection. -/
def pullDependentLinearEquivConnection
    {K : Type w}
    {Fiber : Configuration S₂ → Type x}
    [CommSemiring K]
    [∀ C, AddCommMonoid (Fiber C)]
    [∀ C, Module K (Fiber C)]
    (∇ : DependentLinearEquivConnection K S₂ Fiber) :
    DependentLinearEquivConnection
      K S₁ (E.pullFiber Fiber) where
  transport := by
    intro C e h
    have hcfg :=
      E.map_extend C e h
    cases hcfg
    exact
      ∇.transport
        (E.mapConfiguration C)
        (E.eventEquiv e)
        ((E.enabled_iff C e).2 h)

/-- Forgetting invertibility commutes with pullback. -/
theorem pullEquiv_toLinearConnection
    {K : Type w}
    {Fiber : Configuration S₂ → Type x}
    [CommSemiring K]
    [∀ C, AddCommMonoid (Fiber C)]
    [∀ C, Module K (Fiber C)]
    (∇ : DependentLinearEquivConnection K S₂ Fiber) :
    (E.pullDependentLinearEquivConnection ∇).toLinearConnection =
      E.pullDependentLinearConnection
        ∇.toLinearConnection := by
  cases E
  rfl

end EventSystemEquiv
end CausalGeometry
