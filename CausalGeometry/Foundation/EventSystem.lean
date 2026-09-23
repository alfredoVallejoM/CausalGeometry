import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.RelClasses

namespace CausalGeometry

universe u v

/-- Primitive causal event system. Arithmetic structure is deliberately absent. -/
structure EventSystem (Event : Type u) (Label : Type v) where
  precedes : Event → Event → Prop
  conflict : Event → Event → Prop
  label : Event → Label
  precedes_irrefl : Irreflexive precedes
  precedes_trans : Transitive precedes
  conflict_symm : Symmetric conflict
  conflict_irrefl : Irreflexive conflict
  conflict_future :
    ∀ {e f g : Event}, conflict e f → precedes f g → conflict e g

namespace EventSystem

variable {Event : Type u} {Label : Type v} (S : EventSystem Event Label)

/-- A finite or infinite partial history: downward closed and conflict free. -/
structure Configuration where
  carrier : Set Event
  downClosed :
    ∀ {e f : Event}, carrier e → S.precedes f e → carrier f
  conflictFree :
    ∀ {e f : Event}, carrier e → carrier f → ¬ S.conflict e f

instance : Membership Event (Configuration S) :=
  ⟨fun e C => C.carrier e⟩

@[simp] theorem mem_carrier (C : Configuration S) (e : Event) :
    e ∈ C ↔ C.carrier e := Iff.rfl

/-- The empty history is always causally valid. -/
def empty : Configuration S where
  carrier := ∅
  downClosed := by simp
  conflictFree := by simp

/-- An event is enabled when all causes are present and it conflicts with none
of the current history. -/
def Enabled (C : Configuration S) (e : Event) : Prop :=
  e ∉ C ∧
  (∀ f, S.precedes f e → f ∈ C) ∧
  (∀ f, f ∈ C → ¬ S.conflict e f)

/-- Two enabled events are concurrent when they are causally independent and
compatible. -/
def ConcurrentAt (C : Configuration S) (e f : Event) : Prop :=
  S.Enabled C e ∧
  S.Enabled C f ∧
  ¬ S.precedes e f ∧
  ¬ S.precedes f e ∧
  ¬ S.conflict e f

theorem concurrentAt_symm {C : Configuration S} {e f : Event}
    (h : S.ConcurrentAt C e f) :
    S.ConcurrentAt C f e := by
  rcases h with ⟨he, hf, hef, hfe, hc⟩
  exact ⟨hf, he, hfe, hef, fun hcf => hc (S.conflict_symm hcf)⟩

/-- Extending a configuration by an enabled event. -/
def extend (C : Configuration S) (e : Event) (h : S.Enabled C e) :
    Configuration S where
  carrier := insert e C.carrier
  downClosed := by
    intro x y hx hy
    rcases hx with rfl | hx
    · exact Set.mem_insert_of_mem _ (h.2.1 y hy)
    · exact Set.mem_insert_of_mem _ (C.downClosed hx hy)
  conflictFree := by
    intro x y hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact S.conflict_irrefl e
      · exact h.2.2 y hy
    · rcases hy with rfl | hy
      · intro hxe
        exact h.2.2 x hx (S.conflict_symm hxe)
      · exact C.conflictFree hx hy

end EventSystem
end CausalGeometry
