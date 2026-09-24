import CausalGeometry.Foundation.EventSystem

namespace CausalGeometry

universe u v
open EventSystem

variable {Event : Type u} {Label : Type v}

/-- A derived causal path. Primitive data are still events and enabling;
a path merely records a composable finite execution. -/
inductive CausalPath (S : EventSystem Event Label) :
    Configuration S → Configuration S → Type (max u v) where
  | nil (C : Configuration S) : CausalPath S C C
  | step {C D : Configuration S}
      (e : Event) (h : S.Enabled C e)
      (tail : CausalPath S (S.extend C e h) D) :
      CausalPath S C D

namespace CausalPath

variable {S : EventSystem Event Label}

def length {C D : Configuration S} :
    CausalPath S C D → Nat
  | .nil _ => 0
  | .step _ _ tail => tail.length + 1

def append {A B C : Configuration S}
    (p : CausalPath S A B)
    (q : CausalPath S B C) :
    CausalPath S A C := by
  induction p with
  | nil _ =>
      exact q
  | step e h tail ih =>
      exact CausalPath.step e h (ih q)

@[simp] theorem length_nil (C : Configuration S) :
    (CausalPath.nil C).length = 0 := rfl

@[simp] theorem length_step {C D : Configuration S}
    (e : Event) (h : S.Enabled C e)
    (tail : CausalPath S (S.extend C e h) D) :
    (CausalPath.step e h tail).length = tail.length + 1 := rfl

end CausalPath
end CausalGeometry
