import CausalGeometry.History.Composition
import CausalGeometry.History.DiamondPaths

namespace CausalGeometry

universe u v
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalPath

/-- Ordered occurrences, not labels. No causal validity is discarded in the
path itself; this is an observation of that existing inductive carrier. -/
def eventList : {C D : Configuration S} → CausalPath S C D → List Event
  | _, _, .nil _ => []
  | _, _, .step e _ tail => e :: tail.eventList

@[simp] theorem eventList_nil (C : Configuration S) :
    (CausalPath.nil C).eventList = [] := rfl

@[simp] theorem eventList_step {C D : Configuration S}
    (e : Event) (h : S.Enabled C e)
    (tail : CausalPath S (S.extend C e h) D) :
    (CausalPath.step e h tail).eventList = e :: tail.eventList := rfl

@[simp] theorem eventList_comp {C D E : Configuration S}
    (p : CausalPath S C D) (q : CausalPath S D E) :
    (p.comp q).eventList = p.eventList ++ q.eventList := by
  induction p with
  | nil => rfl
  | step e h tail ih => simp only [step_comp, eventList_step, ih, List.cons_append]

@[simp] theorem eventList_castEnd {C D E : Configuration S}
    (h : D = E) (p : CausalPath S C D) :
    (p.castEnd h).eventList = p.eventList := by
  cases h
  rfl

@[simp] theorem eventList_castStart {A C D : Configuration S}
    (h : A = C) (p : CausalPath S A D) :
    (p.castStart h).eventList = p.eventList := by
  cases h
  rfl

@[simp] theorem eventList_length {C D : Configuration S}
    (p : CausalPath S C D) : p.eventList.length = p.length := by
  induction p with
  | nil => rfl
  | step e h tail ih => simp only [eventList_step, List.length_cons, length_step, ih]

/-- This observation reflects equality of actual paths with fixed endpoints.
It does NOT reflect equality of exchange routes between those paths. -/
theorem eq_of_eventList_eq {C D : Configuration S}
    (p q : CausalPath S C D) (h : p.eventList = q.eventList) : p = q := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => rfl
      | step f hf tail => simp [eventList] at h
  | step e he tail ih =>
      cases q with
      | nil => simp [eventList] at h
      | step f hf other =>
          simp only [eventList_step, List.cons.injEq] at h
          rcases h with ⟨hef, ht⟩
          subst f
          have htail := ih other ht
          cases htail
          rfl

end CausalPath

namespace CausalVariational

@[simp] theorem diamondPathEF_eventList
    {C : Configuration S} {e f : Event} (d : ConcurrencyDiamond C e f) :
    (diamondPathEF d).eventList = [e, f] := rfl

@[simp] theorem diamondPathFE_eventList
    {C : Configuration S} {e f : Event} (d : ConcurrencyDiamond C e f) :
    (diamondPathFE d).eventList = [f, e] := by
  simp only [diamondPathFE, CausalPath.eventList_castEnd,
    CausalPath.eventList_step, CausalPath.eventList_nil]

end CausalVariational
end CausalGeometry
