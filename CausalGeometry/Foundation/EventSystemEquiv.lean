import CausalGeometry.Calculus.EventDirection
import CausalGeometry.History.Trace

namespace CausalGeometry

universe u₁ v₁ u₂ v₂

/-- Isomorphism of primitive causal event systems.

This is stronger than a mere event renaming:
- primitive event carriers are equivalent;
- label carriers are equivalent;
- precedence is preserved and reflected;
- conflict is preserved and reflected;
- labels commute with the event equivalence.

All derived configuration/history/calculus invariance is built from this
primitive equivalence rather than assumed independently. -/
structure EventSystemEquiv
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    (S₁ : EventSystem Event₁ Label₁)
    (S₂ : EventSystem Event₂ Label₂) where
  eventEquiv : Event₁ ≃ Event₂
  labelEquiv : Label₁ ≃ Label₂

  precedes_iff :
    ∀ e f,
      S₂.precedes
          (eventEquiv e)
          (eventEquiv f) ↔
        S₁.precedes e f

  conflict_iff :
    ∀ e f,
      S₂.conflict
          (eventEquiv e)
          (eventEquiv f) ↔
        S₁.conflict e f

  label_compat :
    ∀ e,
      labelEquiv (S₁.label e) =
        S₂.label (eventEquiv e)

namespace EventSystemEquiv

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

/-- Reverse a primitive causal-system equivalence. -/
def symm
    (E : EventSystemEquiv S₁ S₂) :
    EventSystemEquiv S₂ S₁ where
  eventEquiv := E.eventEquiv.symm
  labelEquiv := E.labelEquiv.symm

  precedes_iff := by
    intro e f
    have h :=
      (E.precedes_iff
        (E.eventEquiv.symm e)
        (E.eventEquiv.symm f)).symm
    simpa using h

  conflict_iff := by
    intro e f
    have h :=
      (E.conflict_iff
        (E.eventEquiv.symm e)
        (E.eventEquiv.symm f)).symm
    simpa using h

  label_compat := by
    intro e
    apply E.labelEquiv.injective
    simp [E.label_compat]

/-- Identity causal-system equivalence. -/
def refl
    (S : EventSystem Event₁ Label₁) :
    EventSystemEquiv S S where
  eventEquiv := Equiv.refl _
  labelEquiv := Equiv.refl _
  precedes_iff := by
    intro e f
    rfl
  conflict_iff := by
    intro e f
    rfl
  label_compat := by
    intro e
    rfl

/-- Composition of causal-system equivalences. -/
def trans
    {Event₃ : Type*} {Label₃ : Type*}
    {S₃ : EventSystem Event₃ Label₃}
    (E₁₂ : EventSystemEquiv S₁ S₂)
    (E₂₃ : EventSystemEquiv S₂ S₃) :
    EventSystemEquiv S₁ S₃ where
  eventEquiv :=
    E₁₂.eventEquiv.trans E₂₃.eventEquiv
  labelEquiv :=
    E₁₂.labelEquiv.trans E₂₃.labelEquiv

  precedes_iff := by
    intro e f
    rw [
      E₂₃.precedes_iff,
      E₁₂.precedes_iff
    ]

  conflict_iff := by
    intro e f
    rw [
      E₂₃.conflict_iff,
      E₁₂.conflict_iff
    ]

  label_compat := by
    intro e
    simp only [Equiv.trans_apply]
    rw [E₁₂.label_compat,
      E₂₃.label_compat]

/-- Push a derived configuration through a primitive causal-system
equivalence.  The target carrier is the inverse-image description under the
event equivalence; this makes membership proofs canonical. -/
def mapConfiguration
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁) :
    Configuration S₂ where
  carrier :=
    {e₂ |
      E.eventEquiv.symm e₂ ∈ C}

  downClosed := by
    intro e₂ f₂ he hp
    have hp₁ :
        S₁.precedes
          (E.eventEquiv.symm f₂)
          (E.eventEquiv.symm e₂) := by
      apply
        (E.precedes_iff
          (E.eventEquiv.symm f₂)
          (E.eventEquiv.symm e₂)).mp
      simpa using hp
    exact C.downClosed he hp₁

  conflictFree := by
    intro e₂ f₂ he hf hc
    have hc₁ :
        S₁.conflict
          (E.eventEquiv.symm e₂)
          (E.eventEquiv.symm f₂) := by
      apply
        (E.conflict_iff
          (E.eventEquiv.symm e₂)
          (E.eventEquiv.symm f₂)).mp
      simpa using hc
    exact C.conflictFree he hf hc₁

@[simp] theorem mem_mapConfiguration
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁)
    (e : Event₁) :
    E.eventEquiv e ∈ E.mapConfiguration C ↔
      e ∈ C := by
  rfl

@[simp] theorem mem_mapConfiguration_symm
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁)
    (e : Event₂) :
    e ∈ E.mapConfiguration C ↔
      E.eventEquiv.symm e ∈ C :=
  Iff.rfl

/-- Mapping configurations forward and then backward is identity. -/
@[simp] theorem symm_mapConfiguration_mapConfiguration
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁) :
    E.symm.mapConfiguration
        (E.mapConfiguration C) =
      C := by
  apply S₁.configuration_eq_of_carrier_eq
  ext e
  simp [mapConfiguration]

/-- And conversely. -/
@[simp] theorem mapConfiguration_symm_mapConfiguration
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₂) :
    E.mapConfiguration
        (E.symm.mapConfiguration C) =
      C := by
  apply S₂.configuration_eq_of_carrier_eq
  ext e
  simp [mapConfiguration]

/-- Derived configuration spaces are equivalent. -/
def configurationEquiv
    (E : EventSystemEquiv S₁ S₂) :
    Configuration S₁ ≃ Configuration S₂ where
  toFun := E.mapConfiguration
  invFun := E.symm.mapConfiguration
  left_inv :=
    E.symm_mapConfiguration_mapConfiguration
  right_inv :=
    E.mapConfiguration_symm_mapConfiguration

/-- Enabledness is preserved and reflected by causal-system equivalence. -/
theorem enabled_iff
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁)
    (e : Event₁) :
    S₂.Enabled
        (E.mapConfiguration C)
        (E.eventEquiv e) ↔
      S₁.Enabled C e := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro he
      exact h.1
        ((E.mem_mapConfiguration C e).2 he)
    · intro f hp
      have hp₂ :
          S₂.precedes
            (E.eventEquiv f)
            (E.eventEquiv e) :=
        (E.precedes_iff f e).2 hp
      have hm :=
        h.2.1 (E.eventEquiv f) hp₂
      exact
        (E.mem_mapConfiguration C f).1 hm
    · intro f hf hc
      have hf₂ :
          E.eventEquiv f ∈
            E.mapConfiguration C :=
        (E.mem_mapConfiguration C f).2 hf
      have hc₂ :
          S₂.conflict
            (E.eventEquiv e)
            (E.eventEquiv f) :=
        (E.conflict_iff e f).2 hc
      exact h.2.2
        (E.eventEquiv f) hf₂ hc₂

  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro he
      exact h.1
        ((E.mem_mapConfiguration C e).1 he)
    · intro f₂ hp₂
      let f :=
        E.eventEquiv.symm f₂
      have hp₁ :
          S₁.precedes f e := by
        apply
          (E.precedes_iff f e).mp
        simpa [f] using hp₂
      have hf₁ :=
        h.2.1 f hp₁
      exact hf₁
    · intro f₂ hf₂ hc₂
      let f :=
        E.eventEquiv.symm f₂
      have hf₁ : f ∈ C := by
        exact hf₂
      have hc₁ :
          S₁.conflict e f := by
        apply
          (E.conflict_iff e f).mp
        simpa [f] using hc₂
      exact h.2.2 f hf₁ hc₁

/-- Enabled event directions are equivalent at corresponding
configurations. -/
def directionEquiv
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁) :
    EventDirection S₁ C ≃
      EventDirection S₂
        (E.mapConfiguration C) where
  toFun := fun d =>
    ⟨E.eventEquiv d.event,
      (E.enabled_iff C d.event).2
        d.enabled⟩

  invFun := fun d => by
    let e :=
      E.eventEquiv.symm d.event
    refine ⟨e, ?_⟩
    apply
      (E.enabled_iff C e).1
    simpa [e] using d.enabled

  left_inv := by
    intro d
    apply EventDirection.ext
    simp

  right_inv := by
    intro d
    apply EventDirection.ext
    simp

/-- Concurrency is preserved and reflected. -/
theorem concurrentAt_iff
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁)
    (e f : Event₁) :
    S₂.ConcurrentAt
        (E.mapConfiguration C)
        (E.eventEquiv e)
        (E.eventEquiv f) ↔
      S₁.ConcurrentAt C e f := by
  constructor
  · intro h
    rcases h with
      ⟨he, hf, hef, hfe, hc, hne⟩
    refine ⟨
      (E.enabled_iff C e).1 he,
      (E.enabled_iff C f).1 hf,
      ?_, ?_, ?_, ?_⟩
    · intro hp
      exact hef
        ((E.precedes_iff e f).2 hp)
    · intro hp
      exact hfe
        ((E.precedes_iff f e).2 hp)
    · intro hcf
      exact hc
        ((E.conflict_iff e f).2 hcf)
    · intro heq
      exact hne
        (congrArg E.eventEquiv heq)
  · intro h
    rcases h with
      ⟨he, hf, hef, hfe, hc, hne⟩
    refine ⟨
      (E.enabled_iff C e).2 he,
      (E.enabled_iff C f).2 hf,
      ?_, ?_, ?_, ?_⟩
    · intro hp
      exact hef
        ((E.precedes_iff e f).1 hp)
    · intro hp
      exact hfe
        ((E.precedes_iff f e).1 hp)
    · intro hcf
      exact hc
        ((E.conflict_iff e f).1 hcf)
    · exact fun heq =>
        hne (E.eventEquiv.injective heq)

/-- Map a genuine concurrency diamond. -/
def mapDiamond
    (E : EventSystemEquiv S₁ S₂)
    {C : Configuration S₁}
    {e f : Event₁}
    (d : ConcurrencyDiamond C e f) :
    ConcurrencyDiamond
      (E.mapConfiguration C)
      (E.eventEquiv e)
      (E.eventEquiv f) where
  concurrent :=
    (E.concurrentAt_iff C e f).2
      d.concurrent

/-- Mapping an enabled extension is the same derived configuration as extending
the mapped configuration by the mapped event. -/
theorem map_extend
    (E : EventSystemEquiv S₁ S₂)
    (C : Configuration S₁)
    (e : Event₁)
    (h : S₁.Enabled C e) :
    E.mapConfiguration
        (S₁.extend C e h)
      =
    S₂.extend
      (E.mapConfiguration C)
      (E.eventEquiv e)
      ((E.enabled_iff C e).2 h) := by
  apply S₂.configuration_eq_of_carrier_eq
  ext x
  simp [
    mapConfiguration,
    EventSystem.extend
  ]

end EventSystemEquiv
end CausalGeometry
