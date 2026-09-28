import CausalGeometry.History.Path
import Mathlib.Tactic

/-!
# Composition of derived causal paths

The original producer and its three public lemmas have been moved verbatim
from Variational/DiscreteAction. The right unit and associativity are now
proved by induction, independently of any Lagrangian or ECIA realization.
-/
namespace CausalGeometry

universe u v
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalPath

/-- Concatenation of derived causal paths. -/
def comp :
    {C D E : Configuration S} →
      CausalPath S C D →
      CausalPath S D E →
      CausalPath S C E
  | _, _, _, .nil _, q => q
  | _, _, _, .step e h tail, q =>
      .step e h (comp tail q)

@[simp] theorem nil_comp
    {C D : Configuration S}
    (q : CausalPath S C D) :
    (CausalPath.nil C).comp q = q :=
  rfl

@[simp] theorem step_comp
    {C D E : Configuration S}
    (e : Event)
    (h : S.Enabled C e)
    (tail : CausalPath S (S.extend C e h) D)
    (q : CausalPath S D E) :
    (CausalPath.step e h tail).comp q =
      CausalPath.step e h (tail.comp q) :=
  rfl

theorem length_comp
    {C D E : Configuration S}
    (p : CausalPath S C D)
    (q : CausalPath S D E) :
    (p.comp q).length =
      p.length + q.length := by
  induction p with
  | nil =>
      simp [comp]
  | step e h tail ih =>
      simp [comp, ih, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

@[simp] theorem comp_nil
    {C D : Configuration S} (p : CausalPath S C D) :
    p.comp (.nil D) = p := by
  induction p with
  | nil => rfl
  | step e h tail ih => simp only [step_comp, ih]

theorem comp_assoc
    {A B C D : Configuration S}
    (p : CausalPath S A B) (q : CausalPath S B C)
    (r : CausalPath S C D) :
    (p.comp q).comp r = p.comp (q.comp r) := by
  induction p with
  | nil => rfl
  | step e h tail ih => simp only [step_comp, ih]

end CausalPath
end CausalGeometry
