import CausalGeometry.Number.Basic
import CausalGeometry.Realization.IndexedFamily

namespace CausalGeometry
namespace Models
namespace CommonSourceControls

/-- Empty primitive event system used as one causal-source witness. -/
def emptySystem :
    EventSystem PEmpty PUnit where
  precedes := fun _ _ => False
  conflict := fun _ _ => False
  label := fun e => nomatch e
  precedes_irrefl := by
    intro e
    exact nomatch e
  precedes_trans := by
    intro e
    exact nomatch e
  conflict_symm := by
    intro e
    exact nomatch e
  conflict_irrefl := by
    intro e
    exact nomatch e
  conflict_future := by
    intro e
    exact nomatch e

/-- A causal number with no primitive events. -/
def emptyCausalNumber :
    CausalNumber Unit where
  Event := PEmpty
  Label := PUnit
  system := emptySystem
  inputSupport := fun _ => ∅
  outputSupport := fun _ => ∅

/-- One-event primitive system with no causal or conflict edges. -/
def singletonSystem :
    EventSystem PUnit PUnit where
  precedes := fun _ _ => False
  conflict := fun _ _ => False
  label := fun _ => PUnit.unit
  precedes_irrefl := by
    intro e h
    exact h
  precedes_trans := by
    intro e f g hef
    exact False.elim hef
  conflict_symm := by
    intro e f hef
    exact False.elim hef
  conflict_irrefl := by
    intro e h
    exact h
  conflict_future := by
    intro e f g hef
    exact False.elim hef

/-- A causal number with one independent primitive event. -/
def singletonCausalNumber :
    CausalNumber Unit where
  Event := PUnit
  Label := PUnit
  system := singletonSystem
  inputSupport := fun _ => ∅
  outputSupport := fun _ => ∅

/-- The two source witnesses are genuinely distinct before any realization. -/
theorem empty_ne_singleton :
    emptyCausalNumber ≠
      singletonCausalNumber := by
  intro h
  have hnonempty :
      Nonempty emptyCausalNumber.Event := by
    rw [h]
    exact ⟨PUnit.unit⟩
  exact hnonempty.elim

/-- Named two-point source domain for downstream common-source realization
controls. -/
def TwoSourceDomain
    (X : CausalNumber Unit) : Prop :=
  X = emptyCausalNumber ∨
    X = singletonCausalNumber

theorem empty_mem_twoSourceDomain :
    TwoSourceDomain emptyCausalNumber :=
  Or.inl rfl

theorem singleton_mem_twoSourceDomain :
    TwoSourceDomain singletonCausalNumber :=
  Or.inr rfl

end CommonSourceControls
end Models
end CausalGeometry
