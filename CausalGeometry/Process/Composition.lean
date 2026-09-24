import CausalGeometry.Process.Diary

namespace CausalGeometry

universe u v w x

/-- Witnessed gluing of two typed diaries.

Composition is not manufactured from boundary types alone. A witness supplies a
composite event system, embeddings of the two event systems, preservation laws,
boundary support laws and the cross-interface causal relation that actually
glues output events to input events.

The first implementation keeps all event/label carriers in one universe. A
later universe-lift adapter can remove that convenience without changing the
mathematical contract. -/
structure DiaryCompositionData
    {A : Type u} {B : Type v} {C : Type w}
    (D : Diary.{u, v, x} A B)
    (E : Diary.{v, w, x} B C) where
  composite : Diary.{u, w, x} A C

  leftEvent : D.Event → composite.Event
  rightEvent : E.Event → composite.Event
  leftLabel : D.Label → composite.Label
  rightLabel : E.Label → composite.Label

  left_injective : Function.Injective leftEvent
  right_injective : Function.Injective rightEvent
  left_right_disjoint :
    ∀ d e, leftEvent d ≠ rightEvent e

  left_label :
    ∀ d, composite.system.label (leftEvent d) =
      leftLabel (D.system.label d)
  right_label :
    ∀ e, composite.system.label (rightEvent e) =
      rightLabel (E.system.label e)

  left_precedes :
    ∀ {d d'}, D.system.precedes d d' →
      composite.system.precedes (leftEvent d) (leftEvent d')
  right_precedes :
    ∀ {e e'}, E.system.precedes e e' →
      composite.system.precedes (rightEvent e) (rightEvent e')

  left_conflict :
    ∀ {d d'}, D.system.conflict d d' →
      composite.system.conflict (leftEvent d) (leftEvent d')
  right_conflict :
    ∀ {e e'}, E.system.conflict e e' →
      composite.system.conflict (rightEvent e) (rightEvent e')

  input_support :
    ∀ a, composite.inputSupport a = leftEvent '' D.inputSupport a
  output_support :
    ∀ c, composite.outputSupport c = rightEvent '' E.outputSupport c

  interface_precedes :
    ∀ (b : B) {d : D.Event} {e : E.Event},
      d ∈ D.outputSupport b →
      e ∈ E.inputSupport b →
      composite.system.precedes (leftEvent d) (rightEvent e)

namespace DiaryCompositionData

variable
    {A : Type u} {B : Type v} {C : Type w}
    {D : Diary.{u, v, x} A B}
    {E : Diary.{v, w, x} B C}

/-- The chosen composite diary carried by a gluing witness. -/
def result (G : DiaryCompositionData D E) : Diary.{u, w, x} A C :=
  G.composite

@[simp] theorem result_inputSupport
    (G : DiaryCompositionData D E) (a : A) :
    G.result.inputSupport a = G.leftEvent '' D.inputSupport a :=
  G.input_support a

@[simp] theorem result_outputSupport
    (G : DiaryCompositionData D E) (c : C) :
    G.result.outputSupport c = G.rightEvent '' E.outputSupport c :=
  G.output_support c

end DiaryCompositionData

/-- Existence of a witnessed composite. This is weaker and more honest than a
global primitive multiplication on all diaries. -/
def DiariesComposable
    {A : Type u} {B : Type v} {C : Type w}
    (D : Diary.{u, v, x} A B)
    (E : Diary.{v, w, x} B C) : Prop :=
  Nonempty (DiaryCompositionData D E)

end CausalGeometry
