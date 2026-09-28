import CausalGeometry.History.DiamondPaths
import CausalGeometry.Variational.ActionGauge
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalVariational

variable {K : Type w} [AddCommGroup K]

/-- The local square-action defect is literally the action difference between
the two same-endpoint concurrent-swap paths. -/
theorem actionDifference_diamondPaths
    (L : CausalStepLagrangian S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    actionDifference L
        (diamondPathEF d)
        (diamondPathFE d)
      =
    squareActionDefect L d := by
  unfold diamondPathEF diamondPathFE
  unfold actionDifference
  rw [pathAction_castEnd]
  simp only [pathAction_step, pathAction_nil, add_zero, squareActionDefect]

/-- Intrinsic discrete Euler--Lagrange equation for the primitive concurrency
variations of the causal event geometry.

Every allowed local exchange e;f <-> f;e must be stationary. -/
def ElementaryEulerLagrange
    (L : CausalStepLagrangian S K) : Prop :=
  ∀ {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f),
      squareActionDefect L d = 0

/-- Equivalent path-level formulation: every elementary concurrent swap has
zero same-endpoint action variation. -/
def ElementarySwapStationary
    (L : CausalStepLagrangian S K) : Prop :=
  ∀ {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f),
      actionDifference L
        (diamondPathEF d)
        (diamondPathFE d)
      =
    0

theorem elementaryEulerLagrange_iff_swapStationary
    (L : CausalStepLagrangian S K) :
    ElementaryEulerLagrange L ↔
      ElementarySwapStationary L := by
  constructor
  · intro h C e f d
    rw [actionDifference_diamondPaths]
    exact h d
  · intro h C e f d
    rw [← actionDifference_diamondPaths L d]
    exact h d

/-- Euler--Lagrange on primitive concurrent swaps is exactly local path
independence on every concurrency diamond. -/
theorem elementaryEulerLagrange_iff_pathIndependent
    (L : CausalStepLagrangian S K) :
    ElementaryEulerLagrange L ↔
      ∀ {C : Configuration S}
        {e f : Event}
        (d : ConcurrencyDiamond C e f),
          PathIndependentOnDiamond L d := by
  rfl

/-- Boundary gauge changes do not alter the elementary Euler--Lagrange
equations. -/
theorem elementaryEulerLagrange_addBoundary_iff
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K) :
    ElementaryEulerLagrange
        (addBoundary L B)
      ↔
    ElementaryEulerLagrange L := by
  constructor
  · intro h C e f d
    have hd := h d
    rw [squareActionDefect_addBoundary] at hd
    exact hd
  · intro h C e f d
    rw [squareActionDefect_addBoundary]
    exact h d

/-- The elementary Euler--Lagrange equation is orientation independent:
reversing the ordered diamond gives the same vanishing condition. -/
theorem elementaryEulerLagrange_symm
    (L : CausalStepLagrangian S K)
    (hEL : ElementaryEulerLagrange L)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    squareActionDefect L d.symm = 0 := by
  rw [squareActionDefect_symm]
  rw [hEL d]
  simp

end CausalVariational
end CausalGeometry
