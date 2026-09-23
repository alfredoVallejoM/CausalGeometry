import CausalGeometry.History.Trace

namespace CausalGeometry

universe u v w

/-- A typed causal process with explicit input and output boundaries.
The first campaign keeps only the minimum carrier needed for later gluing. -/
structure Diary (A : Type u) (B : Type v) where
  Event : Type w
  Label : Type w
  system : EventSystem Event Label
  inputSupport : A → Set Event
  outputSupport : B → Set Event

/-- Endodiaries are the primitive carrier of causal numbers. -/
abbrev EndDiary (A : Type u) := Diary A A

/-- Boundary reversal. Event-level reversal is added only once the chosen
causal equivalence and gluing laws have been proved. -/
def Diary.flip {A : Type u} {B : Type v} (D : Diary A B) : Diary B A where
  Event := D.Event
  Label := D.Label
  system := D.system
  inputSupport := D.outputSupport
  outputSupport := D.inputSupport

@[simp] theorem Diary.flip_flip {A : Type u} {B : Type v} (D : Diary A B) :
    D.flip.flip = D := by
  cases D
  rfl

end CausalGeometry
