import CausalGeometry.Process.Diary

namespace CausalGeometry

universe u v w

/-- Event-level dagger witness for one diary.

Diary.flip only swaps boundary supports. A genuine dagger additionally
reverses causal precedence on an equivalent event carrier, preserves conflict
and transports the boundary supports. It is therefore separate data. -/
structure DiaryDaggerData
    {A : Type u} {B : Type v}
    (D : Diary.{u, v, w} A B) where
  dagger : Diary.{v, u, w} B A
  eventEquiv : D.Event ≃ dagger.Event
  labelEquiv : D.Label ≃ dagger.Label

  label_preserved :
    ∀ e, dagger.system.label (eventEquiv e) =
      labelEquiv (D.system.label e)

  precedence_reversed :
    ∀ e f,
      dagger.system.precedes (eventEquiv f) (eventEquiv e) ↔
        D.system.precedes e f

  conflict_preserved :
    ∀ e f,
      dagger.system.conflict (eventEquiv e) (eventEquiv f) ↔
        D.system.conflict e f

  input_support :
    ∀ b, dagger.inputSupport b = eventEquiv '' D.outputSupport b

  output_support :
    ∀ a, dagger.outputSupport a = eventEquiv '' D.inputSupport a

namespace DiaryDaggerData

variable
    {A : Type u} {B : Type v}
    {D : Diary.{u, v, w} A B}

/-- Explicit witness that applying two chosen daggers returns to the original
event and label carriers. The second dagger need not be definitionally equal to
D, so return equivalences are part of the witness. -/
structure InvolutionWitness
    (D₁ : DiaryDaggerData D)
    (D₂ : DiaryDaggerData D₁.dagger) where
  returnEvent : D₂.dagger.Event ≃ D.Event
  returnLabel : D₂.dagger.Label ≃ D.Label
  event_roundtrip :
    ∀ e, returnEvent (D₂.eventEquiv (D₁.eventEquiv e)) = e
  label_roundtrip :
    ∀ l, returnLabel (D₂.labelEquiv (D₁.labelEquiv l)) = l

end DiaryDaggerData
end CausalGeometry
