import CausalGeometry.Variational.DiscreteAction
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalVariational

variable {K : Type w} [AddCommGroup K]

/-- Add an exact boundary term B(C')-B(C) to a local causal Lagrangian. -/
def addBoundary
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K) :
    CausalStepLagrangian S K :=
  fun C e h =>
    L C e h +
      (B (S.extend C e h) - B C)

/-- Discrete variational gauge law.

Adding an exact boundary term changes the action only by the endpoint
difference. -/
theorem pathAction_addBoundary
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K)
    {C D : Configuration S}
    (p : CausalPath S C D) :
    pathAction (addBoundary L B) p =
      pathAction L p + B D - B C := by
  induction p with
  | nil =>
      simp [pathAction, addBoundary]
  | step e h tail ih =>
      simp [pathAction, addBoundary, ih]
      abel

/-- Therefore action differences between histories with the same endpoints are
invariant under Lagrangian boundary gauge. -/
theorem actionDifference_addBoundary
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K)
    {C D : Configuration S}
    (p q : CausalPath S C D) :
    actionDifference (addBoundary L B) p q =
      actionDifference L p q := by
  unfold actionDifference
  rw [pathAction_addBoundary L B p,
    pathAction_addBoundary L B q]
  abel

/-- The local concurrency-square variational defect is gauge invariant. -/
theorem squareActionDefect_addBoundary
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    squareActionDefect (addBoundary L B) d =
      squareActionDefect L d := by
  unfold squareActionDefect addBoundary
  have hend := d.endpoint_eq
  rw [hend]
  abel

end CausalVariational
end CausalGeometry
