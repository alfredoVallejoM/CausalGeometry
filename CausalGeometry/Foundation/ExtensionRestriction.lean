import Mathlib.Order.Basic

namespace CausalGeometry

universe u v w

/-- Ordered causal extension together with its correlative restriction.
The adjunction law is the primitive semantic contract. -/
structure ExtensionRestriction
    (α : Type u) (β : Type v)
    [Preorder α] [Preorder β] where
  extend : α → β
  restrict : β → α
  adjunction : ∀ a b, extend a ≤ b ↔ a ≤ restrict b

namespace ExtensionRestriction

variable {α : Type u} {β : Type v}
variable [Preorder α] [Preorder β]
variable (E : ExtensionRestriction α β)

theorem unit (a : α) : a ≤ E.restrict (E.extend a) :=
  (E.adjunction a (E.extend a)).mp le_rfl

theorem counit (b : β) : E.extend (E.restrict b) ≤ b :=
  (E.adjunction (E.restrict b) b).mpr le_rfl

theorem monotone_extend : Monotone E.extend := by
  intro a a' haa
  apply (E.adjunction a (E.extend a')).mpr
  exact haa.trans (E.unit a')

theorem monotone_restrict : Monotone E.restrict := by
  intro b b' hbb
  apply (E.adjunction (E.restrict b) b').mp
  exact (E.counit b).trans hbb

/-- Correlative closure on source conditions. -/
def closure (a : α) : α :=
  E.restrict (E.extend a)

/-- Realizable interior on target conditions. -/
def interior (b : β) : β :=
  E.extend (E.restrict b)

theorem closure_extensive (a : α) : a ≤ E.closure a :=
  E.unit a

theorem interior_reductive (b : β) : E.interior b ≤ b :=
  E.counit b

theorem monotone_closure : Monotone E.closure := by
  intro a a' haa
  exact E.monotone_restrict (E.monotone_extend haa)

theorem monotone_interior : Monotone E.interior := by
  intro b b' hbb
  exact E.monotone_extend (E.monotone_restrict hbb)

theorem closure_idempotent [PartialOrder α] (a : α) :
    E.closure (E.closure a) = E.closure a := by
  apply le_antisymm
  · exact E.monotone_restrict (E.counit (E.extend a))
  · exact E.unit (E.closure a)

theorem interior_idempotent [PartialOrder β] (b : β) :
    E.interior (E.interior b) = E.interior b := by
  apply le_antisymm
  · exact E.counit (E.interior b)
  · exact E.monotone_extend (E.unit (E.restrict b))

def identity (α : Type u) [Preorder α] : ExtensionRestriction α α where
  extend := id
  restrict := id
  adjunction := by
    intro a b
    rfl

def comp {γ : Type w} [Preorder γ]
    (F : ExtensionRestriction β γ) :
    ExtensionRestriction α γ where
  extend := fun a => F.extend (E.extend a)
  restrict := fun c => E.restrict (F.restrict c)
  adjunction := by
    intro a c
    constructor
    · intro h
      have h₁ : E.extend a ≤ F.restrict c :=
        (F.adjunction (E.extend a) c).mp h
      exact (E.adjunction a (F.restrict c)).mp h₁
    · intro h
      have h₁ : E.extend a ≤ F.restrict c :=
        (E.adjunction a (F.restrict c)).mpr h
      exact (F.adjunction (E.extend a) c).mpr h₁

end ExtensionRestriction
end CausalGeometry
