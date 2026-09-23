import CausalGeometry.Foundation.ExtensionRestriction
import Mathlib.Data.Set.Basic

namespace CausalGeometry

universe u v

namespace CorrelativeRestriction

variable {α : Type u} {β : Type v}

/-- Existential forward image of a possibility set along a causal relation. -/
def relExtend (r : α → β → Prop) (P : Set α) : Set β :=
  {b | ∃ a, a ∈ P ∧ r a b}

/-- Universal precondition: all causal outputs must satisfy the target condition. -/
def relRestrict (r : α → β → Prop) (Q : Set β) : Set α :=
  {a | ∀ b, r a b → b ∈ Q}

theorem relAdjunction (r : α → β → Prop) (P : Set α) (Q : Set β) :
    relExtend r P ⊆ Q ↔ P ⊆ relRestrict r Q := by
  constructor
  · intro h a ha b hab
    exact h ⟨a, ha, hab⟩
  · intro h b hb
    rcases hb with ⟨a, ha, hab⟩
    exact h ha b hab

/-- Every causal relation canonically induces extension and correlative restriction. -/
def ofRelation (r : α → β → Prop) :
    ExtensionRestriction (Set α) (Set β) where
  extend := relExtend r
  restrict := relRestrict r
  adjunction := relAdjunction r

/-- A deterministic causal map is the special case given by its graph relation. -/
def graphRelation (f : α → β) : α → β → Prop :=
  fun a b => f a = b

@[simp] theorem graph_extend (f : α → β) (P : Set α) :
    relExtend (graphRelation f) P = f '' P := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

@[simp] theorem graph_restrict (f : α → β) (Q : Set β) :
    relRestrict (graphRelation f) Q = f ⁻¹' Q := by
  ext a
  constructor
  · intro h
    exact h (f a) rfl
  · intro h b hab
    subst b
    exact h

/-- Correlation of source and target conditions through a relation. -/
def Correlated (r : α → β → Prop) (P : Set α) (Q : Set β) : Prop :=
  relExtend r P ⊆ Q

theorem correlated_iff (r : α → β → Prop) (P : Set α) (Q : Set β) :
    Correlated r P Q ↔ P ⊆ relRestrict r Q :=
  relAdjunction r P Q

/-- Relational composition, matching sequential causal composition. -/
def comp {γ : Type*} (r : α → β → Prop) (s : β → γ → Prop) :
    α → γ → Prop :=
  fun a c => ∃ b, r a b ∧ s b c

theorem relExtend_comp {γ : Type*}
    (r : α → β → Prop) (s : β → γ → Prop) (P : Set α) :
    relExtend (comp r s) P = relExtend s (relExtend r P) := by
  ext c
  constructor
  · rintro ⟨a, ha, b, hab, hbc⟩
    exact ⟨b, ⟨a, ha, hab⟩, hbc⟩
  · rintro ⟨b, ⟨a, ha, hab⟩, hbc⟩
    exact ⟨a, ha, b, hab, hbc⟩

theorem relRestrict_comp {γ : Type*}
    (r : α → β → Prop) (s : β → γ → Prop) (Q : Set γ) :
    relRestrict (comp r s) Q =
      relRestrict r (relRestrict s Q) := by
  ext a
  constructor
  · intro h b hab c hbc
    exact h c ⟨b, hab, hbc⟩
  · intro h c hc
    rcases hc with ⟨b, hab, hbc⟩
    exact h b hab c hbc

end CorrelativeRestriction
end CausalGeometry
