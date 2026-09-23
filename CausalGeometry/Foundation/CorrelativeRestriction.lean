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
    simpa [graphRelation] using h.trans_eq hab

/-- Correlation of source and target conditions through a relation. -/
def Correlated (r : α → β → Prop) (P : Set α) (Q : Set β) : Prop :=
  relExtend r P ⊆ Q

theorem correlated_iff (r : α → β → Prop) (P : Set α) (Q : Set β) :
    Correlated r P Q ↔ P ⊆ relRestrict r Q :=
  relAdjunction r P Q

end CorrelativeRestriction
end CausalGeometry
