import CausalGeometry.History.PathEquivariance
import CausalGeometry.Variational.DiscreteAction
import Mathlib.Tactic

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ w

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace CausalVariational

variable {K : Type w} [AddCommGroup K]

/-- Pull a target step Lagrangian back through a primitive causal-system
equivalence. -/
def pullStepLagrangian
    (E : EventSystemEquiv S₁ S₂)
    (L : CausalStepLagrangian S₂ K) :
    CausalStepLagrangian S₁ K :=
  fun C e h =>
    L (E.mapConfiguration C)
      (E.eventEquiv e)
      ((E.enabled_iff C e).2 h)

/-- Casting the declared start of a path along an equality does not change its
action. -/
theorem pathAction_castStart
    (L : CausalStepLagrangian S₁ K)
    {C C' D : Configuration S₁}
    (h : C = C')
    (p : CausalPath S₁ C D) :
    pathAction L (p.castStart h) =
      pathAction L p := by
  cases h
  rfl

/-- Casting only the declared terminal configuration does not change action. -/
theorem pathAction_castEnd
    (L : CausalStepLagrangian S₁ K)
    {C D D' : Configuration S₁}
    (h : D = D')
    (p : CausalPath S₁ C D) :
    pathAction L (p.castEnd h) =
      pathAction L p := by
  cases h
  rfl

/-- Discrete action is natural under primitive causal-system equivalence. -/
theorem pathAction_natural
    (E : EventSystemEquiv S₁ S₂)
    (L : CausalStepLagrangian S₂ K)
    {C D : Configuration S₁}
    (p : CausalPath S₁ C D) :
    pathAction L (E.mapPath p) =
      pathAction (pullStepLagrangian E L) p := by
  induction p with
  | nil =>
      rfl
  | step e h tail ih =>
      dsimp [EventSystemEquiv.mapPath,
        pathAction, pullStepLagrangian]
      rw [pathAction_castStart]
      rw [ih]

/-- A self-equivalence is a Lagrangian symmetry when pulling the local action
density back along the symmetry leaves it unchanged. -/
def LagrangianSymmetry
    {Event : Type u₁} {Label : Type v₁}
    {S : EventSystem Event Label}
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K) :
    Prop :=
  pullStepLagrangian E L = L

/-- A Lagrangian symmetry preserves the action of every causal path. -/
theorem pathAction_invariant
    {Event : Type u₁} {Label : Type v₁}
    {S : EventSystem Event Label}
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (hL : LagrangianSymmetry E L)
    {C D : Configuration S}
    (p : CausalPath S C D) :
    pathAction L (E.mapPath p) =
      pathAction L p := by
  rw [pathAction_natural]
  rw [hL]

/-- Turn the image of a path under a symmetry into a genuine same-endpoint
variation when the two endpoints are fixed by the symmetry. -/
def fixedEndpointSymmetryPath
    {Event : Type u₁} {Label : Type v₁}
    {S : EventSystem Event Label}
    (E : EventSystemEquiv S S)
    {C D : Configuration S}
    (hC : E.mapConfiguration C = C)
    (hD : E.mapConfiguration D = D)
    (p : CausalPath S C D) :
    CausalPath S C D :=
  ((E.mapPath p).castStart hC).castEnd hD

/-- First exact Noether-type consequence.

A Lagrangian symmetry that fixes the endpoints produces a same-endpoint path
whose action difference from the original path is exactly zero.

This is an action-level conservation theorem.  A momentum map/current requires
additional symplectic or tensor data and is deliberately not inferred here. -/
theorem noether_actionDifference_zero
    {Event : Type u₁} {Label : Type v₁}
    {S : EventSystem Event Label}
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (hL : LagrangianSymmetry E L)
    {C D : Configuration S}
    (hC : E.mapConfiguration C = C)
    (hD : E.mapConfiguration D = D)
    (p : CausalPath S C D) :
    actionDifference L
        (fixedEndpointSymmetryPath
          E hC hD p)
        p
      =
    0 := by
  unfold actionDifference
  unfold fixedEndpointSymmetryPath
  rw [pathAction_castEnd, pathAction_castStart]
  rw [pathAction_invariant E L hL p]
  exact sub_self _

/-- Stationarity against an explicitly supplied class of same-endpoint
competitors. -/
def StationaryAgainst
    {Event : Type u₁} {Label : Type v₁}
    {S : EventSystem Event Label}
    (L : CausalStepLagrangian S K)
    {C D : Configuration S}
    (p : CausalPath S C D)
    (Allowed : CausalPath S C D → Prop) :
    Prop :=
  ∀ q,
    Allowed q →
      actionDifference L q p = 0

/-- A fixed-endpoint Lagrangian symmetry supplies one certified zero-action
variation and hence one admissible stationarity test. -/
theorem stationary_against_single_symmetry
    {Event : Type u₁} {Label : Type v₁}
    {S : EventSystem Event Label}
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (hL : LagrangianSymmetry E L)
    {C D : Configuration S}
    (hC : E.mapConfiguration C = C)
    (hD : E.mapConfiguration D = D)
    (p : CausalPath S C D) :
    StationaryAgainst L p
      (fun q =>
        q =
          fixedEndpointSymmetryPath
            E hC hD p) := by
  intro q hq
  subst q
  exact
    noether_actionDifference_zero
      E L hL hC hD p

end CausalVariational
end CausalGeometry
