import CausalGeometry.Exchange.Path
import CausalGeometry.Variational.ElementaryEulerLagrange

/-!
# Existing causal action as an internal consumer of exchange routes

The full contextual action difference is the local square defect. Thus the
existing elementary Euler–Lagrange condition suffices for action preservation
along every free exchange route. This does not identify distinct routes.
-/
namespace CausalGeometry.Exchange

universe u v w
open CausalGeometry EventSystem CausalVariational

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} [AddCommGroup K]

/-- Prefix and suffix contributions cancel without any stationarity assumption. -/
theorem Step.actionDifference_eq {C D : Configuration S}
    {p q : CausalPath S C D} (s : Step p q) (L : CausalStepLagrangian S K) :
    actionDifference L p q = squareActionDefect L s.diamond := by
  rw [← s.source_eq, ← s.target_eq]
  unfold actionDifference
  simp only [pathAction_comp]
  have hd := actionDifference_diamondPaths L s.diamond
  unfold actionDifference at hd
  rw [← hd]
  abel

/-- The pre-existing intrinsic Euler–Lagrange condition has a genuine
contextual consumer, not just the bare two-event square. -/
theorem Step.preservesAction {C D : Configuration S}
    {p q : CausalPath S C D} (s : Step p q)
    (L : CausalStepLagrangian S K) (hEL : ElementaryEulerLagrange L) :
    pathAction L p = pathAction L q := by
  apply sub_eq_zero.mp
  change actionDifference L p q = 0
  rw [s.actionDifference_eq L]
  exact hEL s.diamond

/-- Invariance under any finite sequence of witnessed contextual exchanges. -/
theorem Route.preservesAction {C D : Configuration S}
    {p q : CausalPath S C D} (r : Route p q)
    (L : CausalStepLagrangian S K) (hEL : ElementaryEulerLagrange L) :
    pathAction L p = pathAction L q := by
  induction r with
  | nil => rfl
  | cons t s ih => exact ih.trans (s.preservesAction L hEL)

end CausalGeometry.Exchange
