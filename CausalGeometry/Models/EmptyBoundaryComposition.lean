import CausalGeometry.Process.EndComposition
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace EmptyBoundaryComposition

/-
A deliberately coarse negative control for realization-loss tests.

The boundary is empty, so serial gluing needs no cross-interface event.  The
composite event system is the disjoint union of the two event systems.
The selected equivalence is intentionally indiscrete; this makes the model a
mutation control, not a proposed semantic equivalence for production use.
-/

universe u

/-- Disjoint-union causal precedence. Cross-component precedence is absent. -/
def sumPrecedes
    {E₁ E₂ : Type u}
    {L₁ L₂ : Type u}
    (S₁ : EventSystem E₁ L₁)
    (S₂ : EventSystem E₂ L₂) :
    (E₁ ⊕ E₂) → (E₁ ⊕ E₂) → Prop
  | Sum.inl a, Sum.inl b => S₁.precedes a b
  | Sum.inr a, Sum.inr b => S₂.precedes a b
  | _, _ => False

/-- Disjoint-union conflict. Cross-component conflicts are absent. -/
def sumConflict
    {E₁ E₂ : Type u}
    {L₁ L₂ : Type u}
    (S₁ : EventSystem E₁ L₁)
    (S₂ : EventSystem E₂ L₂) :
    (E₁ ⊕ E₂) → (E₁ ⊕ E₂) → Prop
  | Sum.inl a, Sum.inl b => S₁.conflict a b
  | Sum.inr a, Sum.inr b => S₂.conflict a b
  | _, _ => False

def sumLabel
    {E₁ E₂ : Type u}
    {L₁ L₂ : Type u}
    (S₁ : EventSystem E₁ L₁)
    (S₂ : EventSystem E₂ L₂) :
    (E₁ ⊕ E₂) → (L₁ ⊕ L₂)
  | Sum.inl a => Sum.inl (S₁.label a)
  | Sum.inr b => Sum.inr (S₂.label b)

/-- The disjoint union of two event systems. -/
def sumEventSystem
    {E₁ E₂ : Type u}
    {L₁ L₂ : Type u}
    (S₁ : EventSystem E₁ L₁)
    (S₂ : EventSystem E₂ L₂) :
    EventSystem (E₁ ⊕ E₂) (L₁ ⊕ L₂) where

  precedes := sumPrecedes S₁ S₂
  conflict := sumConflict S₁ S₂
  label := sumLabel S₁ S₂

  precedes_irrefl := by
    intro e
    cases e with
    | inl a =>
        exact S₁.precedes_irrefl a
    | inr b =>
        exact S₂.precedes_irrefl b

  precedes_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;>
      simp [sumPrecedes] at hab hbc ⊢
    · exact S₁.precedes_trans hab hbc
    · exact S₂.precedes_trans hab hbc

  conflict_symm := by
    intro a b hab
    cases a <;> cases b <;>
      simp [sumConflict] at hab ⊢
    · exact S₁.conflict_symm hab
    · exact S₂.conflict_symm hab

  conflict_irrefl := by
    intro e
    cases e with
    | inl a =>
        exact S₁.conflict_irrefl a
    | inr b =>
        exact S₂.conflict_irrefl b

  conflict_future := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;>
      simp [sumConflict, sumPrecedes] at hab hbc ⊢
    · exact S₁.conflict_future hab hbc
    · exact S₂.conflict_future hab hbc

/-- Empty-boundary disjoint-union composite. -/
def composeDiary
    (X Y : EndDiary.{0, u} Empty) :
    EndDiary.{0, u} Empty where
  Event := X.Event ⊕ Y.Event
  Label := X.Label ⊕ Y.Label
  system := sumEventSystem X.system Y.system
  inputSupport := fun a => Empty.elim a
  outputSupport := fun a => Empty.elim a

/-- Witness that the disjoint-union diary is a valid composition when the
boundary has no interface points. -/
def composeData
    (X Y : EndDiary.{0, u} Empty) :
    DiaryCompositionData X Y where
  composite := composeDiary X Y
  leftEvent := Sum.inl
  rightEvent := Sum.inr
  leftLabel := Sum.inl
  rightLabel := Sum.inr
  left_injective := Sum.inl_injective
  right_injective := Sum.inr_injective
  left_right_disjoint := by
    intro x y h
    cases h
  left_label := by
    intro x
    rfl
  right_label := by
    intro y
    rfl
  left_precedes := by
    intro x y h
    exact h
  right_precedes := by
    intro x y h
    exact h
  left_conflict := by
    intro x y h
    exact h
  right_conflict := by
    intro x y h
    exact h
  input_support := by
    intro a
    exact Empty.elim a
  output_support := by
    intro a
    exact Empty.elim a
  interface_precedes := by
    intro a
    exact Empty.elim a

/-- Empty event system used by the weak unit. -/
def emptyEventSystem :
    EventSystem Empty Empty where
  precedes := fun a => Empty.elim a
  conflict := fun a => Empty.elim a
  label := fun a => Empty.elim a
  precedes_irrefl := by
    intro a
    exact Empty.elim a
  precedes_trans := by
    intro a
    exact Empty.elim a
  conflict_symm := by
    intro a
    exact Empty.elim a
  conflict_irrefl := by
    intro a
    exact Empty.elim a
  conflict_future := by
    intro a
    exact Empty.elim a

/-- Empty-event diary. -/
def emptyDiary :
    EndDiary Empty where
  Event := Empty
  Label := Empty
  system := emptyEventSystem
  inputSupport := fun a => Empty.elim a
  outputSupport := fun a => Empty.elim a

/-- One-event diary with no causal order or conflict. -/
def singletonDiary :
    EndDiary Empty where
  Event := PUnit
  Label := PUnit
  system :=
    { precedes := fun _ _ => False
      conflict := fun _ _ => False
      label := id
      precedes_irrefl := by simp
      precedes_trans := by simp
      conflict_symm := by simp
      conflict_irrefl := by simp
      conflict_future := by simp }
  inputSupport := fun a => Empty.elim a
  outputSupport := fun a => Empty.elim a

/-- The two control diaries are genuinely different before any realization. -/
theorem emptyDiary_ne_singletonDiary :
    emptyDiary ≠ singletonDiary := by
  intro h
  have hEvent :
      Empty = PUnit :=
    congrArg Diary.Event h
  have impossible : Empty :=
    hEvent.symm ▸ PUnit.unit
  exact Empty.elim impossible

/-- Deliberately coarse weak composition system.

The indiscrete equivalence is used only as an adversarial realization-loss
control.  It must never be confused with the semantic equivalences used by
the positive causal programme. -/
def coarseSystem :
    EndDiaryCompositionSystem.{0, u} Empty where
  composeData := composeData
  equivalent := fun _ _ => True
  equivalent_refl := by
    intro X
    trivial
  equivalent_symm := by
    intro X Y h
    trivial
  equivalent_trans := by
    intro X Y Z hXY hYZ
    trivial
  unit := emptyDiary
  associator := by
    intro X Y Z
    trivial
  left_unitor := by
    intro X
    trivial
  right_unitor := by
    intro X
    trivial

end EmptyBoundaryComposition
end Models
end CausalGeometry
