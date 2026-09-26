import CausalGeometry.History.Path
import CausalGeometry.Calculus.CubeShift
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
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

end CausalPath

/-- Local discrete causal Lagrangian attached to one enabled primitive event. -/
abbrev CausalStepLagrangian
    (S : EventSystem Event Label)
    (K : Type w) :=
  (C : Configuration S) →
    (e : Event) →
      S.Enabled C e → K

namespace CausalVariational

variable {K : Type w} [AddCommGroup K]

/-- Action of a finite causal path. -/
def pathAction
    (L : CausalStepLagrangian S K) :
    {C D : Configuration S} →
      CausalPath S C D → K
  | _, _, .nil _ => 0
  | C, _, .step e h tail =>
      L C e h + pathAction L tail

@[simp] theorem pathAction_nil
    (L : CausalStepLagrangian S K)
    (C : Configuration S) :
    pathAction L (CausalPath.nil C) = 0 :=
  rfl

@[simp] theorem pathAction_step
    (L : CausalStepLagrangian S K)
    {C D : Configuration S}
    (e : Event)
    (h : S.Enabled C e)
    (tail : CausalPath S (S.extend C e h) D) :
    pathAction L (CausalPath.step e h tail) =
      L C e h + pathAction L tail :=
  rfl

/-- Action is additive under path concatenation. -/
theorem pathAction_comp
    (L : CausalStepLagrangian S K)
    {C D E : Configuration S}
    (p : CausalPath S C D)
    (q : CausalPath S D E) :
    pathAction L (p.comp q) =
      pathAction L p + pathAction L q := by
  induction p with
  | nil =>
      simp [CausalPath.comp, pathAction]
  | step e h tail ih =>
      simp [CausalPath.comp, pathAction, ih, add_assoc]

/-- Variational comparison of two causal histories with the same endpoints. -/
def actionDifference
    (L : CausalStepLagrangian S K)
    {C D : Configuration S}
    (p q : CausalPath S C D) : K :=
  pathAction L p - pathAction L q

/-- Local action-order defect on a concurrency diamond.

This is the variational analogue of causal order curvature: it measures the
difference between the two two-step histories e;f and f;e. -/
def squareActionDefect
    (L : CausalStepLagrangian S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) : K :=
  (L C e d.concurrent.1 +
      L d.afterE f
        (S.concurrent_enabled_after_left d.concurrent))
    -
  (L C f d.concurrent.2.1 +
      L d.afterF e
        (S.concurrent_enabled_after_right d.concurrent))

def PathIndependentOnDiamond
    (L : CausalStepLagrangian S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) : Prop :=
  squareActionDefect L d = 0

theorem pathIndependentOnDiamond_iff
    (L : CausalStepLagrangian S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    PathIndependentOnDiamond L d ↔
      L C e d.concurrent.1 +
          L d.afterE f
            (S.concurrent_enabled_after_left d.concurrent)
        =
      L C f d.concurrent.2.1 +
          L d.afterF e
            (S.concurrent_enabled_after_right d.concurrent) := by
  unfold PathIndependentOnDiamond squareActionDefect
  exact sub_eq_zero

theorem squareActionDefect_symm
    (L : CausalStepLagrangian S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    squareActionDefect L d.symm =
      - squareActionDefect L d := by
  unfold squareActionDefect
  abel

end CausalVariational
end CausalGeometry
