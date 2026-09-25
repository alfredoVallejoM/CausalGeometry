import CausalGeometry.Calculus.EventSystemEquiv
import CausalGeometry.Calculus.CohomologyH2

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
variable {K : Type w} [AddCommGroup K]

/-- Contravariant pullback of causal one-forms. -/
def pullOneForm
    (ω : CausalOneForm S₂ K) :
    CausalOneForm S₁ K where
  value := fun C d =>
    ω.value
      (E.mapConfiguration C)
      (E.directionEquiv C d)

/-- Pullback is additive. -/
def pullOneFormHom :
    CausalOneForm S₂ K →+
      CausalOneForm S₁ K where
  toFun := E.pullOneForm
  map_zero' := by
    apply CausalOneForm.ext
    intro C d
    rfl
  map_add' := by
    intro ω η
    apply CausalOneForm.ext
    intro C d
    rfl

@[simp] theorem pullOneForm_value
    (ω : CausalOneForm S₂ K)
    (C : Configuration S₁)
    (d : EventDirection S₁ C) :
    (E.pullOneForm ω).value C d =
      ω.value
        (E.mapConfiguration C)
        (E.directionEquiv C d) :=
  rfl

theorem directionEquiv_baseE
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    E.directionEquiv C
        (CausalOneForm.baseE d)
      =
    CausalOneForm.baseE
      (E.mapDiamond d) := by
  apply EventDirection.ext
  rfl

theorem directionEquiv_baseF
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    E.directionEquiv C
        (CausalOneForm.baseF d)
      =
    CausalOneForm.baseF
      (E.mapDiamond d) := by
  apply EventDirection.ext
  rfl

/-- First component variation of a one-form commutes with pullback. -/
theorem variationEF_natural
    (ω : CausalOneForm S₂ K)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    CausalOneForm.variationEF
        (E.pullOneForm ω) d
      =
    CausalOneForm.variationEF
        ω (E.mapDiamond d) := by
  unfold CausalOneForm.variationEF
    pullOneForm
  have hcfg := E.map_afterE d
  cases hcfg
  have hafter :
      E.directionEquiv d.afterE
          (CausalOneForm.afterE_F d)
        =
      CausalOneForm.afterE_F
        (E.mapDiamond d) := by
    apply EventDirection.ext
    rfl
  have hbase :=
    E.directionEquiv_baseF d
  rw [hafter, hbase]

/-- Opposite component variation commutes with pullback. -/
theorem variationFE_natural
    (ω : CausalOneForm S₂ K)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    CausalOneForm.variationFE
        (E.pullOneForm ω) d
      =
    CausalOneForm.variationFE
        ω (E.mapDiamond d) := by
  unfold CausalOneForm.variationFE
    pullOneForm
  have hcfg := E.map_afterF d
  cases hcfg
  have hafter :
      E.directionEquiv d.afterF
          (CausalOneForm.afterF_E d)
        =
      CausalOneForm.afterF_E
        (E.mapDiamond d) := by
    apply EventDirection.ext
    rfl
  have hbase :=
    E.directionEquiv_baseE d
  rw [hafter, hbase]

/-- Exterior derivative of one-forms is natural under causal-system
isomorphism. -/
theorem exteriorDerivative_one_natural
    (ω : CausalOneForm S₂ K)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    CausalOneForm.exteriorDerivative
        (E.pullOneForm ω) d
      =
    CausalOneForm.exteriorDerivative
        ω (E.mapDiamond d) := by
  unfold CausalOneForm.exteriorDerivative
  rw [
    E.variationEF_natural ω d,
    E.variationFE_natural ω d
  ]

/-- Closedness of one-forms is representation invariant in the pullback
direction. -/
theorem pullOneForm_closed
    {ω : CausalOneForm S₂ K}
    (hω : ω.Closed) :
    (E.pullOneForm ω).Closed := by
  intro C e f d
  rw [E.exteriorDerivative_one_natural ω d]
  exact hω (E.mapDiamond d)

/-- Pullback of an exact one-form is the exact one-form of the pulled scalar
potential. -/
theorem pullOneForm_exact
    (F : Configuration S₂ → K) :
    E.pullOneForm
        (CausalOneForm.exact F)
      =
    CausalOneForm.exact
      (E.pullObservable F) := by
  apply CausalOneForm.ext
  intro C d
  exact
    E.causalDifference_natural
      F C d.event d.enabled

/-- Contravariant pullback of causal two-forms. -/
def pullTwoForm
    (ω : CausalTwoForm S₂ K) :
    CausalTwoForm S₁ K where
  value := fun d =>
    ω.value (E.mapDiamond d)
  skew := by
    intro C e f d
    rw [E.mapDiamond_symm d]
    exact ω.skew (E.mapDiamond d)

/-- Pullback of two-forms is additive. -/
def pullTwoFormHom :
    CausalTwoForm S₂ K →+
      CausalTwoForm S₁ K where
  toFun := E.pullTwoForm
  map_zero' := by
    apply CausalTwoForm.ext
    intro C e f d
    rfl
  map_add' := by
    intro ω η
    apply CausalTwoForm.ext
    intro C e f d
    rfl

@[simp] theorem pullTwoForm_value
    (ω : CausalTwoForm S₂ K)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    (E.pullTwoForm ω).value d =
      ω.value (E.mapDiamond d) :=
  rfl

/-- Packing exterior derivative as a two-form commutes with pullback. -/
theorem pullTwoForm_exteriorDerivative
    (ω : CausalOneForm S₂ K) :
    E.pullTwoForm
        (CausalTwoForm.ofExteriorDerivative ω)
      =
    CausalTwoForm.ofExteriorDerivative
      (E.pullOneForm ω) := by
  apply CausalTwoForm.ext
  intro C e f d
  exact
    (E.exteriorDerivative_one_natural
      ω d).symm

/-- Pullback and inverse pullback cancel on one-forms. -/
@[simp] theorem symm_pullOneForm_pullOneForm
    (ω : CausalOneForm S₂ K) :
    E.symm.pullOneForm
        (E.pullOneForm ω)
      =
    ω := by
  apply CausalOneForm.ext
  intro C d
  unfold pullOneForm
  have hcfg :=
    E.mapConfiguration_symm_mapConfiguration C
  cases hcfg
  congr 1
  apply EventDirection.ext
  simp [directionEquiv]

/-- The other one-form round trip also cancels. -/
@[simp] theorem pullOneForm_symm_pullOneForm
    (ω : CausalOneForm S₁ K) :
    E.pullOneForm
        (E.symm.pullOneForm ω)
      =
    ω := by
  apply CausalOneForm.ext
  intro C d
  unfold pullOneForm
  have hcfg :=
    E.symm_mapConfiguration_mapConfiguration C
  cases hcfg
  congr 1
  apply EventDirection.ext
  simp [directionEquiv]

/-- One-form spaces are additively equivalent under causal-system
isomorphism. -/
def oneFormAddEquiv :
    CausalOneForm S₁ K ≃+
      CausalOneForm S₂ K where
  toFun := E.symm.pullOneForm
  invFun := E.pullOneForm
  left_inv :=
    E.pullOneForm_symm_pullOneForm
  right_inv :=
    E.symm_pullOneForm_pullOneForm
  map_add' := by
    intro ω η
    rfl

/-- Pullback and inverse pullback cancel on two-forms. -/
@[simp] theorem symm_pullTwoForm_pullTwoForm
    (ω : CausalTwoForm S₂ K) :
    E.symm.pullTwoForm
        (E.pullTwoForm ω)
      =
    ω := by
  apply CausalTwoForm.ext
  intro C e f d
  unfold pullTwoForm
  have hcfg :=
    E.mapConfiguration_symm_mapConfiguration C
  cases hcfg
  congr 1

@[simp] theorem pullTwoForm_symm_pullTwoForm
    (ω : CausalTwoForm S₁ K) :
    E.pullTwoForm
        (E.symm.pullTwoForm ω)
      =
    ω := by
  apply CausalTwoForm.ext
  intro C e f d
  unfold pullTwoForm
  have hcfg :=
    E.symm_mapConfiguration_mapConfiguration C
  cases hcfg
  congr 1

/-- Two-form spaces are additively equivalent. -/
def twoFormAddEquiv :
    CausalTwoForm S₁ K ≃+
      CausalTwoForm S₂ K where
  toFun := E.symm.pullTwoForm
  invFun := E.pullTwoForm
  left_inv :=
    E.pullTwoForm_symm_pullTwoForm
  right_inv :=
    E.symm_pullTwoForm_pullTwoForm
  map_add' := by
    intro ω η
    rfl

end EventSystemEquiv
end CausalGeometry
