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

/-- Event-level involutivity of two chosen dagger witnesses. No involution is
assumed merely from the existence of one dagger. -/
def EventInvolutive
    (D₁ : DiaryDaggerData D)
    (D₂ : DiaryDaggerData D₁.dagger) : Prop :=
  ∀ e, D₂.eventEquiv (D₁.eventEquiv e) = e

/-- Label-level involutivity of two chosen dagger witnesses. -/
def LabelInvolutive
    (D₁ : DiaryDaggerData D)
    (D₂ : DiaryDaggerData D₁.dagger) : Prop :=
  ∀ l, D₂.labelEquiv (D₁.labelEquiv l) = l

end DiaryDaggerData
end CausalGeometry
